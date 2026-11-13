import Mogulskii.IntervalAction
import Mogulskii.PolygonVelocity
import Mogulskii.Statements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open Set Filter MeasureTheory Asymptotics
open scoped BigOperators ENNReal Topology Interval

namespace Mogulskii

local instance actionIdentityEuclideanMeasurableSpace {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance actionIdentityEuclideanBorelSpace {d : ℕ} :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

private theorem absolutelyContinuous_coordinate {d : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin d)}
    (hf : AbsolutelyContinuousOnInterval f 0 1) (i : Fin d) :
    AbsolutelyContinuousOnInterval (fun t => f t i) 0 1 := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf ε hε
  refine ⟨δ, hδ, fun intervals hwithin hlen => ?_⟩
  apply lt_of_le_of_lt (Finset.sum_le_sum fun j hj => ?_) (h intervals hwithin hlen)
  rw [dist_eq_norm, dist_eq_norm]
  exact PiLp.norm_apply_le (f (intervals.2 j).1 - f (intervals.2 j).2) i

private noncomputable def coordinateVelocity {d : ℕ}
    (f : ℝ → EuclideanSpace ℝ (Fin d)) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => deriv (fun s => f s i) t

private theorem integrableOn_coordinateVelocity {d : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin d)} (hf : AbsolutelyContinuousOnInterval f 0 1) :
    IntegrableOn (coordinateVelocity f) (Icc 0 1) := by
  have hcoord (i : Fin d) : IntegrableOn (deriv (fun t => f t i)) (Icc 0 1) := by
    have hi := (absolutelyContinuous_coordinate hf i).intervalIntegrable_deriv
    unfold IntegrableOn
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi
  have heq : coordinateVelocity f = fun t => ∑ i : Fin d,
      PiLp.single 2 i (deriv (fun s => f s i) t) := by
    funext t
    ext j
    change coordinateVelocity f t j = EuclideanSpace.proj (𝕜 := ℝ) j
      (∑ i : Fin d, PiLp.single 2 i (deriv (fun s => f s i) t))
    rw [map_sum]
    simp [coordinateVelocity, EuclideanSpace.coe_proj, PiLp.single_apply, Finset.sum_ite_eq']
  rw [heq]
  apply integrable_finsetSum
  intro i _
  refine ((hcoord i).smul_const
    (PiLp.single (β := fun _ : Fin d => ℝ) 2 i 1)).congr (Eventually.of_forall fun t => ?_)
  ext j
  by_cases h : j = i <;> simp [PiLp.single_apply, h]

private theorem integral_coordinateVelocity {d : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin d)} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (t : UnitTime) :
    (∫ s in (0 : ℝ)..(t : ℝ), coordinateVelocity f s) = f t - f 0 := by
  have hi : IntervalIntegrable (coordinateVelocity f) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.property.1).mpr
      ((integrableOn_coordinateVelocity hf).mono_set fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩)
  ext i
  change (EuclideanSpace.proj (𝕜 := ℝ) i)
    (∫ s in (0 : ℝ)..(t : ℝ), coordinateVelocity f s) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
  exact ((absolutelyContinuous_coordinate hf i).mono (by
    rw [uIcc_of_le t.property.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl t.property.2)).integral_deriv_eq_sub

/-- The path associated to finite disjoint-interval action is the primitive of an
integrable velocity. -/
theorem exists_integrable_velocity_of_disjointIntervalAction
    {d : ℕ} {I : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hgrow : ∀ q > (0 : ℝ), ∃ M ≥ 0, ∀ v : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (q * ‖v‖ - M) ≤ I v)
    {φ : WalkPath d} (hφ : disjointIntervalAction I φ ≠ ⊤) :
    ∃ v : ℝ → EuclideanSpace ℝ (Fin d), IntegrableOn v (Icc 0 1) ∧
      ∀ t : UnitTime, φ t = ∫ s in (0 : ℝ)..(t : ℝ), v s := by
  have hAc := absolutelyContinuous_extendPath hgrow hφ (le_refl _)
  refine ⟨coordinateVelocity (extendPath φ), integrableOn_coordinateVelocity hAc, fun t => ?_⟩
  rw [integral_coordinateVelocity hAc, extendPath_eq φ t]
  have h0 := finite_disjointIntervalAction_start hφ
  rw [show extendPath φ 0 = φ ⟨0, by norm_num⟩ from extendPath_eq φ ⟨0, by norm_num⟩]
  change φ ⟨0, by norm_num⟩ = 0 at h0
  rw [h0, sub_zero]

/-- Integrating Jensen's inequality over any finite disjoint family bounds the discrete
action by the integral action. -/
theorem disjointIntervalAction_le_pathRate {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) (φ : WalkPath d) :
    disjointIntervalAction (cramerRate μ X) φ ≤ pathRate (cramerRate μ X) φ := by
  unfold pathRate
  refine le_iInf fun v => le_iInf fun hv => le_iInf fun hφ => ?_
  have h0 : φ zeroTime = 0 := by rw [hφ]; simp [zeroTime]
  rw [disjointIntervalAction, if_pos h0]
  refine iSup_le fun n => iSup_le fun s => iSup_le fun t => iSup_le fun hst => iSup_le fun hd => ?_
  have hsub (i : ℕ) :
      Ioc (s i : ℝ) (t i : ℝ) ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨(s i).property.1.trans hx.1.le, hx.2.trans (t i).property.2⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, ∫⁻ x in Ioc (s i : ℝ) (t i : ℝ), cramerRate μ X (v x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle : (s i : ℝ) ≤ (t i : ℝ) := hst i (Finset.mem_range.mp hi)
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [heq, sub_self, ENNReal.ofReal_zero, zero_mul]
        exact zero_le
      · have hs : IntegrableOn v (Ioc (0 : ℝ) (s i : ℝ)) :=
          hv.mono_set fun x hx => ⟨hx.1.le, hx.2.trans (s i).property.2⟩
        have ht := hv.mono_set (hsub i)
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (s i).property.1).mpr hs)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr ht)
        rw [hφ, hφ, ← hadd, add_sub_cancel_left, intervalIntegral.integral_of_le hle]
        exact cramerRate_secant_le μ X hlt ht
    _ = ∫⁻ x in ⋃ i ∈ Finset.range n, Ioc (s i : ℝ) (t i : ℝ), cramerRate μ X (v x) :=
      (lintegral_biUnion_finset hd (fun _ _ => measurableSet_Ioc) _).symm
    _ ≤ _ := lintegral_mono_set (iUnion₂_subset fun i _ => hsub i)

private theorem tendsto_secant_of_hasDerivAt {F : ℝ → ℝ} {v x : ℝ}
    (hF : HasDerivAt F v x) {a b : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 x))
    (hab : ∀ᶠ n in atTop, a n ≤ x ∧ x ≤ b n ∧ a n < b n) :
    Tendsto (fun n => (b n - a n)⁻¹ * (F (b n) - F (a n))) atTop (𝓝 v) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hder := hF.isLittleO.bound (half_pos hε)
  filter_upwards [ha.eventually hder, hb.eventually hder, hab] with n han hbn hn
  have hlen : 0 < b n - a n := sub_pos.mpr hn.2.2
  have ha' : |F (a n) - F x - (a n - x) * v| ≤ (ε / 2) * (x - a n) := by
    simpa [smul_eq_mul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hn.1), neg_sub] using han
  have hb' : |F (b n) - F x - (b n - x) * v| ≤ (ε / 2) * (b n - x) := by
    simpa [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hn.2.1)] using hbn
  rw [Real.dist_eq, show (b n - a n)⁻¹ * (F (b n) - F (a n)) - v =
      ((F (b n) - F x - (b n - x) * v) - (F (a n) - F x - (a n - x) * v)) /
        (b n - a n) by field_simp [hlen.ne'] <;> ring, abs_div, abs_of_pos hlen, div_lt_iff₀ hlen]
  refine (abs_sub _ _).trans_lt ?_
  have h := add_le_add hb' ha'
  nlinarith only [h, mul_pos hε hlen]

private theorem tendsto_polygonVelocity_meshSlope_of_hasDerivAt {d : ℕ}
    (φ : WalkPath d) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (h : ∀ i : Fin d, HasDerivAt (fun s => extendPath φ s i)
      (coordinateVelocity (extendPath φ) t i) t) :
    Tendsto (fun m : ℕ => polygonVelocity (m + 1)
      (fun i => ((m + 1 : ℕ) : ℝ) •
        (φ (meshTime (m + 1) (i + 1)) - φ (meshTime (m + 1) i))) t)
      atTop (𝓝 (coordinateVelocity (extendPath φ) t)) := by
  let k (m : ℕ) := ⌈((m + 1 : ℕ) : ℝ) * t⌉₊ - 1
  have hmul (m : ℕ) : 0 < ((m + 1 : ℕ) : ℝ) * t := by positivity [ht.1]
  have hceil (m : ℕ) : 0 < ⌈((m + 1 : ℕ) : ℝ) * t⌉₊ := by
    exact_mod_cast (hmul m).trans_le (Nat.le_ceil _)
  have hk (m : ℕ) : k m < m + 1 := by
    have hle : ⌈((m + 1 : ℕ) : ℝ) * t⌉₊ ≤ m + 1 :=
      Nat.ceil_le.mpr (mul_le_of_le_one_right (by positivity) ht.2)
    dsimp [k]
    omega
  have hk₁ (m : ℕ) : (k m : ℝ) < ((m + 1 : ℕ) : ℝ) * t := by
    have h := Nat.ceil_lt_add_one (hmul m).le
    have he : k m + 1 = ⌈((m + 1 : ℕ) : ℝ) * t⌉₊ := Nat.sub_add_cancel (hceil m)
    rw [← he, Nat.cast_add, Nat.cast_one] at h
    linarith
  have hk₂ (m : ℕ) : ((m + 1 : ℕ) : ℝ) * t ≤ ((k m + 1 : ℕ) : ℝ) := by
    rw [show k m + 1 = ⌈((m + 1 : ℕ) : ℝ) * t⌉₊ from Nat.sub_add_cancel (hceil m)]
    exact Nat.le_ceil _
  let a (m : ℕ) : ℝ := meshTime (m + 1) (k m)
  let b (m : ℕ) : ℝ := meshTime (m + 1) (k m + 1)
  have ha (m) : a m = (k m : ℝ) / ((m + 1 : ℕ) : ℝ) := coe_meshTime (hk m).le
  have hb (m) : b m = ((k m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := coe_meshTime (hk m)
  have hlen (m) : b m - a m = ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [ha, hb]
    push_cast
    ring
  have hab (m) : a m < t ∧ t ≤ b m := by
    rw [ha, hb, div_lt_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    simpa [mul_comm t] using And.intro (hk₁ m) (hk₂ m)
  have hlim : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have ha_lim : Tendsto a atTop (𝓝 t) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hlim
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (hab m).1), ← hlen m]
    linarith [(hab m).2]
  have hb_lim : Tendsto b atTop (𝓝 t) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hlim
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hab m).2), ← hlen m]
    linarith [(hab m).1]
  apply (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isInducing.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  have hsec := tendsto_secant_of_hasDerivAt (h i) ha_lim hb_lim
    (Eventually.of_forall fun m => ⟨(hab m).1.le, (hab m).2, (hab m).1.trans_le (hab m).2⟩)
  refine hsec.congr fun m => ?_
  rw [hlen, inv_inv]
  have hstep := polygonVelocity_eq (Nat.succ_pos m) (hk m)
    (fun i => ((m + 1 : ℕ) : ℝ) •
      (φ (meshTime (m + 1) (i + 1)) - φ (meshTime (m + 1) i)))
    (s := t) (by
      have hh := hab m
      rw [ha, hb] at hh
      simp only [Nat.cast_succ] at hh ⊢
      exact hh)
  change _ = (polygonVelocity (m + 1) (fun j => ((m + 1 : ℕ) : ℝ) •
    (φ (meshTime (m + 1) (j + 1)) - φ (meshTime (m + 1) j))) t) i
  rw [hstep]
  simp [a, b, extendPath_eq, smul_eq_mul]

theorem meshAction_le_disjointIntervalAction {d : ℕ}
    (I : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (φ : WalkPath d) (hφ : φ ⟨0, by norm_num⟩ = 0) {m : ℕ} (hm : 0 < m) :
    (∫⁻ t in Icc (0 : ℝ) 1, I (polygonVelocity m
      (fun i => (m : ℝ) • (φ (meshTime m (i + 1)) - φ (meshTime m i))) t)) ≤
      disjointIntervalAction I φ := by
  rw [lintegral_polygonVelocity hm]
  have hm' : (0 : ℝ) < m := by positivity
  have hmono (i j : ℕ) (hi : i ≤ j) : meshTime m i ≤ meshTime m j := by
    change min (i : ℝ) (m : ℝ) / m ≤ min (j : ℝ) (m : ℝ) / m
    exact div_le_div_of_nonneg_right (min_le_min (by exact_mod_cast hi) le_rfl) hm'.le
  refine (Finset.sum_le_sum fun i hi => ?_).trans
    (secantSum_le_disjointIntervalAction hφ m
      (meshTime m) (fun i => meshTime m (i + 1)) (fun i _ => hmono i (i + 1) (Nat.le_succ _)) ?_)
  · have hi' := Finset.mem_range.mp hi
    have he : (meshTime m (i+1) : ℝ) - (meshTime m i : ℝ) = 1 / m := by
      rw [coe_meshTime hi', coe_meshTime hi'.le]
      push_cast
      ring
    rw [he, one_div, inv_inv]
  · intro i hi j hj hij
    have help (k l : ℕ) (hkl : k < l) : Disjoint
        (Ioc (meshTime m k : ℝ) (meshTime m (k + 1) : ℝ))
        (Ioc (meshTime m l : ℝ) (meshTime m (l + 1) : ℝ)) := by
      refine Set.disjoint_left.mpr fun _ h₁ h₂ => ?_
      exact (not_lt_of_ge (h₁.2.trans (hmono _ _ hkl))) h₂.1
    exact (lt_or_gt_of_ne hij).elim (help i j) (fun h => (help j i h).symm)

/-- The integral of the Cramér rate of the path velocity equals the supremum of discrete
secant costs. -/
theorem pathRate_eq_disjointIntervalAction {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (hgrow : ∀ q > (0 : ℝ), ∃ M ≥ 0, ∀ v : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (q * ‖v‖ - M) ≤ cramerRate μ X v)
    (φ : WalkPath d) :
    pathRate (cramerRate μ X) φ = disjointIntervalAction (cramerRate μ X) φ := by
  refine le_antisymm ?_ (disjointIntervalAction_le_pathRate μ X φ)
  by_cases hφ : disjointIntervalAction (cramerRate μ X) φ = ⊤
  · rw [hφ]
    exact le_top
  let v := coordinateVelocity (extendPath φ)
  have hac := absolutelyContinuous_extendPath hgrow hφ (le_refl _)
  have hv := integrableOn_coordinateVelocity hac
  have hprim (t : UnitTime) : φ t = ∫ s in (0 : ℝ)..(t : ℝ), v s := by
    rw [integral_coordinateVelocity hac, extendPath_eq φ t]
    have h0 := finite_disjointIntervalAction_start hφ
    rw [show extendPath φ 0 = φ ⟨0, by norm_num⟩ from extendPath_eq φ ⟨0, by norm_num⟩]
    change φ ⟨0, by norm_num⟩ = 0 at h0
    rw [h0, sub_zero]
  unfold pathRate
  refine (iInf_le _ v).trans ((iInf_le _ hv).trans ((iInf_le _ hprim).trans ?_))
  let w (m : ℕ) := polygonVelocity (m + 1) (fun i => ((m + 1 : ℕ) : ℝ) •
    (φ (meshTime (m + 1) (i + 1)) - φ (meshTime (m + 1) i)))
  have hw (m) : AEMeasurable (fun t => cramerRate μ X (w m t))
      (volume.restrict (Icc 0 1)) :=
    (lowerSemicontinuous_cramerRate μ X).measurable.comp_aemeasurable
      ((integrable_polygonVelocity _ _).integrableOn (s := Icc 0 1)).aemeasurable
  have hd (i : Fin d) : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc (0 : ℝ) 1 →
      DifferentiableAt ℝ (fun s => extendPath φ s i) t :=
    (absolutelyContinuous_coordinate hac i).ae_differentiableAt
  have hda : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ∀ i : Fin d,
      HasDerivAt (fun s => extendPath φ s i) (v t i) t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [ae_all_iff.mpr hd] with t ht hmem i
    exact (ht i (by simpa [uIcc_of_le zero_le_one] using hmem)).hasDerivAt
  have htmem : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), t ∈ Ioc (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioc
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, liminf (fun m => cramerRate μ X (w m t)) atTop := by
      apply lintegral_mono_ae
      filter_upwards [hda, htmem] with t hdt ht
      have hlim : Tendsto (fun m => w m t) atTop (𝓝 (v t)) :=
        tendsto_polygonVelocity_meshSlope_of_hasDerivAt φ ht hdt
      have hsemi := LowerSemicontinuous.le_liminf (lowerSemicontinuous_cramerRate μ X) (v t)
      exact hsemi.trans (hlim.liminf_le_liminf_comp (u := cramerRate μ X))
    _ ≤ liminf (fun m => ∫⁻ t in Icc (0 : ℝ) 1, cramerRate μ X (w m t)) atTop :=
      lintegral_liminf_le' hw
    _ ≤ _ := liminf_le_of_frequently_le'
      (Frequently.of_forall fun m => meshAction_le_disjointIntervalAction _ φ
        (finite_disjointIntervalAction_start hφ) (Nat.succ_pos m))

theorem goodRate_cramerPathRate {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (hgrow : ∀ q > (0 : ℝ), ∃ M ≥ 0, ∀ v : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (q * ‖v‖ - M) ≤ cramerRate μ X v) :
    GoodRate (pathRate (cramerRate μ X)) := by
  rw [funext (pathRate_eq_disjointIntervalAction μ X hgrow)]
  exact goodRate_disjointIntervalAction (lowerSemicontinuous_cramerRate μ X) hgrow

end Mogulskii
