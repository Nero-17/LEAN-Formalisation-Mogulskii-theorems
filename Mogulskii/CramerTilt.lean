import Mogulskii.CramerRate
import Mogulskii.GridBlocks
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

theorem integrable_exp_dual
    (hExp : ∀ q ≥ 0, Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    (t : E →L[ℝ] ℝ) : Integrable (fun y ↦ Real.exp (1 * t y)) ν := by
  refine (hExp ‖t‖ (norm_nonneg _)).mono' (by fun_prop) (Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp, one_mul]
  exact (le_abs_self _).trans (t.le_opNorm y)

theorem integrable_id_tilted [SecondCountableTopology E]
    (hExp : ∀ q ≥ 0, Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    (t : E →L[ℝ] ℝ) : Integrable id (ν.tilted t) := by
  have ht : Integrable (fun y => Real.exp (t y)) ν := by
    simpa only [one_mul] using integrable_exp_dual hExp t
  rw [integrable_tilted_iff ht id]
  refine (hExp (‖t‖ + 1) (by positivity)).mono' ?_ (Eventually.of_forall fun y ↦ ?_)
  · exact ((Real.continuous_exp.comp t.continuous).smul continuous_id).measurable.aestronglyMeasurable
  · change ‖Real.exp (t y) • y‖ ≤ Real.exp ((‖t‖ + 1) * ‖y‖)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _), add_mul, one_mul, Real.exp_add]
    have h1 : Real.exp (t y) ≤ Real.exp (‖t‖ * ‖y‖) :=
      Real.exp_le_exp.2 ((le_abs_self _).trans (t.le_opNorm y))
    have h2 : ‖y‖ ≤ Real.exp ‖y‖ := by linarith [Real.add_one_le_exp ‖y‖]
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)

/-- The finite product of a tilted law is the corresponding tilt of the finite product. -/
theorem pi_tilted_eq_tilted_pi
    (t : E →L[ℝ] ℝ) (hExp : Integrable (fun y ↦ Real.exp (1 * t y)) ν) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ ν.tilted t) =
      (Measure.pi fun _ : Fin n ↦ ν).tilted (fun x ↦ ∑ i, t (x i)) := by
  letI : IsProbabilityMeasure (ν.tilted t) :=
    isProbabilityMeasure_tilted (by simpa only [one_mul] using hExp)
  let P := Measure.pi fun _ : Fin n ↦ ν
  let X : Fin n → (Fin n → E) → ℝ := fun i x ↦ t (x i)
  have hX : ∀ i, Measurable (X i) := fun i ↦ t.continuous.measurable.comp (measurable_pi_apply i)
  have hind : iIndepFun X P := iIndepFun_pi (fun _ ↦ t.continuous.measurable.aemeasurable)
  have hmap (i : Fin n) : MeasurePreserving (fun x : Fin n → E ↦ x i) P ν :=
    measurePreserving_eval _ i
  have hXi (i : Fin n) : Integrable (fun x ↦ Real.exp (1 * X i x)) P :=
    (hmap i).integrable_comp_of_integrable hExp
  have hsum := hind.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ ↦ hXi i)
  have hcgf (i : Fin n) : cgf (X i) P 1 = cgf t ν 1 := by
    have hmeas : AEStronglyMeasurable (fun y => Real.exp (1 * t y))
        (P.map fun x : Fin n → E => x i) := by
      rw [(hmap i).map_eq]
      exact hExp.aestronglyMeasurable
    change Real.log (mgf ((t : E → ℝ) ∘ (fun x : Fin n → E => x i)) P 1) =
      Real.log (mgf t ν 1)
    rw [← mgf_map (hmap i).measurable.aemeasurable hmeas, (hmap i).map_eq]
  have hcgfsum : cgf (fun x ↦ ∑ i, t (x i)) P 1 = n * cgf t ν 1 := by
    change cgf (fun x ↦ ∑ i, X i x) P 1 = _
    simp_rw [← Finset.sum_apply]
    rw [hind.cgf_sum hX (fun i _ ↦ hXi i)]
    simp [hcgf, nsmul_eq_mul]
  have hp_exp : Integrable (fun x ↦ Real.exp (1 * ∑ i, t (x i))) P := by
    simpa only [Finset.sum_apply, X] using hsum
  refine Measure.pi_eq fun s hs ↦ ?_
  have htilt (i : Fin n) : ν.tilted t (s i) =
      ∫⁻ y, (s i).indicator (fun y ↦ ENNReal.ofReal (Real.exp (t y - cgf t ν 1))) y ∂ν := by
    simpa only [one_mul, lintegral_indicator (hs i)] using tilted_mul_apply_cgf' (hs i) hExp
  have hprod (x : Fin n → E) :
      (Set.univ.pi s).indicator
          (fun x ↦ ENNReal.ofReal (Real.exp ((∑ i, t (x i)) - n * cgf t ν 1))) x =
      ∏ i, (s i).indicator (fun y ↦ ENNReal.ofReal (Real.exp (t y - cgf t ν 1))) (x i) := by
    by_cases h : x ∈ Set.univ.pi s
    · have h' : ∀ i, x i ∈ s i := fun i ↦ h i (mem_univ i)
      simp only [indicator_of_mem h, indicator_of_mem (h' _)]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _), ← Real.exp_sum,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have h' : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using h
      obtain ⟨i, hi⟩ := h'
      rw [indicator_of_notMem h, Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)]
  let Z : Fin n → E → ℝ≥0∞ := fun i ↦
    (s i).indicator (fun y ↦ ENNReal.ofReal (Real.exp (t y - cgf t ν 1)))
  have hZ (i : Fin n) : Measurable (Z i) :=
    (by fun_prop : Measurable (fun y ↦ ENNReal.ofReal (Real.exp (t y - cgf t ν 1)))).indicator (hs i)
  change P.tilted (fun x ↦ ∑ i, t (x i)) (Set.univ.pi s) = _
  have ht := tilted_mul_apply_cgf' (MeasurableSet.univ_pi hs) hp_exp
  simp only [one_mul, hcgfsum] at ht
  rw [ht, ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hprod]
  change (∫⁻ x, ∏ i, Z i (x i) ∂P) = ∏ i, ν.tilted t (s i)
  calc
    _ = ∏ i, ∫⁻ x, Z i (x i) ∂P :=
      lintegral_prod_eq_prod_lintegral_of_indepFun (μ := P) Finset.univ
        (fun i x ↦ Z i (x i)) (iIndepFun_pi fun i ↦ (hZ i).aemeasurable)
        (fun i ↦ (hZ i).comp (measurable_pi_apply i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [(hmap i).lintegral_comp (hZ i)]
      exact (htilt i).symm

/-- Under the product law, a fixed ball about the expectation eventually has mass at least one half. -/
theorem eventually_meanLaw_ball_ge [ProperSpace E]
    (hν : Integrable id ν) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ≥0∞) ≤ meanLaw ν n (Metric.ball (∫ y, y ∂ν) δ) := by
  obtain ⟨Ω, mΩ, μ, X, hm, hlaw, hind, hprob⟩ := exists_iid ℕ ν
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hprob
  let Y : ℕ → Ω → E := fun n ω ↦ (n : ℝ)⁻¹ • ∑ j : Fin n, X j.val ω
  have hY (n : ℕ) : Measurable (Y n) :=
    (measurable_mean n).comp (measurable_pi_lambda _ fun j : Fin n ↦ hm j.val)
  have hl (i : ℕ) : μ.map (X i) = ν := (hlaw i).map_eq
  have hi (i : ℕ) : IdentDistrib (X i) id μ ν :=
    ⟨(hm i).aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hl i⟩
  have hyLaw (n : ℕ) : μ.map (Y n) = meanLaw ν n := by
    have hj : iIndepFun (fun j : Fin n ↦ X j.val) μ := hind.precomp Fin.val_injective
    change μ.map ((fun x : Fin n → E ↦ (n : ℝ)⁻¹ • ∑ j, x j) ∘
        (fun ω (j : Fin n) ↦ X j.val ω)) = meanLaw ν n
    unfold meanLaw
    rw [← Measure.map_map (measurable_mean n) (measurable_pi_lambda _ fun j : Fin n ↦ hm j.val)]
    have hjLaw : μ.map (fun ω (j : Fin n) ↦ X j.val ω) =
        Measure.pi (fun j : Fin n ↦ μ.map (X j.val)) :=
      hj.map_fun_eq_pi_map (fun j : Fin n ↦ (hm j.val).aemeasurable)
    rw [hjLaw]
    simp_rw [hl]
  have hstrong := strong_law_ae X ((hi 0).symm.integrable_snd hν)
    (fun i j hij ↦ hind.indepFun hij) (fun i ↦ (hi i).trans (hi 0).symm)
  have hmean : (∫ ω, X 0 ω ∂μ) = ∫ y, y ∂ν := (hi 0).integral_eq
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (∫ y, y ∂ν)) := by
    rw [← hmean]
    filter_upwards [hstrong] with ω hω
    refine hω.congr fun n ↦ ?_
    change (n : ℝ)⁻¹ • (∑ j ∈ Finset.range n, X j ω) =
      (n : ℝ)⁻¹ • (∑ j : Fin n, X j.val ω)
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ X j ω)]
  have hconv := tendstoInMeasure_of_tendsto_ae (fun n ↦ (hY n).aestronglyMeasurable) hae
  have hsmall := (tendsto_order.1 ((tendstoInMeasure_iff_dist.1 hconv) δ hδ)).2
    (1 / 2 : ℝ≥0∞) (by norm_num)
  filter_upwards [hsmall] with n hn
  have hmeas : MeasurableSet ((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ) :=
    (hY n) Metric.isOpen_ball.measurableSet
  have heq : {ω | δ ≤ dist (Y n ω) (∫ y, y ∂ν)} =
      ((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ)ᶜ := by
    ext ω
    simp [Metric.mem_ball, not_lt]
  rw [heq] at hn
  rw [← hyLaw, Measure.map_apply (hY n) Metric.isOpen_ball.measurableSet]
  have hsum : 1 ≤ μ ((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ) + (1 / 2 : ℝ≥0∞) := by
    calc
      _ = μ ((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ) +
          μ (((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ)ᶜ) := by
        rw [measure_add_measure_compl hmeas, measure_univ]
      _ ≤ _ := add_le_add_right hn.le _
  have h : (1 : ℝ≥0∞) - 1 / 2 ≤ μ ((Y n) ⁻¹' Metric.ball (∫ y, y ∂ν) δ) :=
    tsub_le_iff_right.2 hsum
  have he : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 := by norm_num
  exact he ▸ h

/-- The exponential change of measure gives the local lower bound at each tilted mean. -/
theorem cramer_lower_at_tilted_mean [ProperSpace E]
    (hExp : ∀ q ≥ 0, Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    (t : E →L[ℝ] ℝ) {U : Set E} (hU : IsOpen U)
    (hy : (∫ y, y ∂(ν.tilted t)) ∈ U) {r : ℝ}
    (hr : t (∫ y, y ∂(ν.tilted t)) - cgf t ν 1 < r) :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n * r))) ≤ meanLaw ν n U := by
  let y := ∫ z, z ∂(ν.tilted t)
  have htExp := integrable_exp_dual hExp t
  letI : IsProbabilityMeasure (ν.tilted t) :=
    isProbabilityMeasure_tilted (by simpa only [one_mul] using htExp)
  have hV : U ∩ {x | t x < r + cgf t ν 1} ∈ 𝓝 y :=
    (hU.inter (isOpen_lt t.continuous continuous_const)).mem_nhds
      ⟨hy, by
        change t y < r + cgf t ν 1
        exact (sub_lt_iff_lt_add).mp hr⟩
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 hV
  filter_upwards [eventually_meanLaw_ball_ge (integrable_id_tilted hExp t) hδ,
    eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  let P := Measure.pi fun _ : Fin n ↦ ν
  let S : (Fin n → E) → E := fun z ↦ (n : ℝ)⁻¹ • ∑ i, z i
  let A := S ⁻¹' Metric.ball y δ
  have hA : MeasurableSet A := (measurable_mean n) Metric.isOpen_ball.measurableSet
  have hSA : A ⊆ S ⁻¹' U := fun z hz ↦ (hsub hz).1
  rw [meanLaw, Measure.map_apply (measurable_mean n) Metric.isOpen_ball.measurableSet,
    pi_tilted_eq_tilted_pi t htExp] at hn
  rw [meanLaw, Measure.map_apply (measurable_mean n) hU.measurableSet]
  have hs (z : Fin n → E) : ∑ i, t (z i) = n * t (S z) := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hnpos)
    simp only [S, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnR, one_mul]
  have hPExp : Integrable (fun z : Fin n → E ↦ Real.exp (1 * ∑ i, t (z i))) P := by
    let X : Fin n → (Fin n → E) → ℝ := fun i z ↦ t (z i)
    have hX (i : Fin n) : Measurable (X i) := t.continuous.measurable.comp (measurable_pi_apply i)
    have hind : iIndepFun X P := iIndepFun_pi (fun _ ↦ t.continuous.measurable.aemeasurable)
    simpa only [Finset.sum_apply, X] using hind.integrable_exp_mul_sum hX (s := Finset.univ)
      (fun i _ ↦ (measurePreserving_eval (fun _ : Fin n ↦ ν) i).integrable_comp_of_integrable htExp)
  have hPcgf : cgf (fun z : Fin n → E ↦ ∑ i, t (z i)) P 1 = n * cgf t ν 1 := by
    let X : Fin n → (Fin n → E) → ℝ := fun i z ↦ t (z i)
    have hX (i : Fin n) : Measurable (X i) := t.continuous.measurable.comp (measurable_pi_apply i)
    have hind : iIndepFun X P := iIndepFun_pi (fun _ ↦ t.continuous.measurable.aemeasurable)
    have hcgf (i : Fin n) : cgf (X i) P 1 = cgf t ν 1 := by
      have hm := measurePreserving_eval (fun _ : Fin n ↦ ν) i
      have hmeas : AEStronglyMeasurable (fun y => Real.exp (1 * t y))
          (P.map fun x : Fin n → E => x i) := by
        rw [hm.map_eq]
        exact htExp.aestronglyMeasurable
      change Real.log (mgf ((t : E → ℝ) ∘ (fun x : Fin n → E => x i)) P 1) =
        Real.log (mgf t ν 1)
      rw [← mgf_map hm.measurable.aemeasurable hmeas, hm.map_eq]
    change cgf (fun z ↦ ∑ i, X i z) P 1 = _
    simp_rw [← Finset.sum_apply]
    have hXi (i : Fin n) : Integrable (fun x ↦ Real.exp (1 * X i x)) P :=
      (measurePreserving_eval (fun _ : Fin n ↦ ν) i).integrable_comp_of_integrable htExp
    rw [hind.cgf_sum hX (fun i _ ↦ hXi i)]
    simp [hcgf, nsmul_eq_mul]
  have hbound : (P.tilted (fun z ↦ ∑ i, t (z i))) A ≤
      ENNReal.ofReal (Real.exp (n * r)) * P A := by
    have ht := tilted_mul_apply_cgf' hA hPExp
    simp only [one_mul, hPcgf] at ht
    rw [ht, ← setLIntegral_const]
    refine setLIntegral_mono_ae' hA (Eventually.of_forall fun z hz ↦ ?_)
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp, hs]
    have hz' : t (S z) < r + cgf t ν 1 := (hsub hz).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.le (Nat.cast_nonneg (α := ℝ) n)]
  have hprod := mul_le_mul_right (hn.trans hbound) (ENNReal.ofReal (Real.exp (-(n * r))))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul, mul_comm] at hprod
  exact hprod.trans (measure_mono hSA)

end Mogulskii

