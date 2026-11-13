import Mogulskii.Polygon
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mogulskii.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Tactic.GCongr

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval

namespace Mogulskii

def zeroTime : UnitTime := ⟨0, by norm_num⟩

open Classical in
/-- The maximum discrete cost over finite families of disjoint intervals. -/
noncomputable def disjointIntervalAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : E → ℝ≥0∞) (φ : C(UnitTime, E)) : ℝ≥0∞ :=
  if φ zeroTime = 0 then
    ⨆ n : ℕ, ⨆ s : ℕ → UnitTime, ⨆ t : ℕ → UnitTime,
      ⨆ _ : (∀ i < n, s i ≤ t i),
      ⨆ _ : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
        (fun i => Ioc (s i : ℝ) (t i : ℝ)),
      ∑ i ∈ Finset.range n, ENNReal.ofReal ((t i : ℝ) - (s i : ℝ)) *
        I (((t i : ℝ) - (s i : ℝ))⁻¹ • (φ (t i) - φ (s i)))
  else ⊤

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {I : E → ℝ≥0∞}

theorem lowerSemicontinuous_disjointIntervalAction
    (hI : LowerSemicontinuous I) : LowerSemicontinuous (disjointIntervalAction I) := by
  let K : Set C(UnitTime, E) := {φ | φ zeroTime = 0}
  have hK : IsClosed K := isClosed_eq (continuous_eval_const _) continuous_const
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a = ⊤
  · simp [ha]
  have heq : {φ | disjointIntervalAction I φ ≤ a} = K ∩
      ⋂ n : ℕ, ⋂ s : ℕ → UnitTime, ⋂ t : ℕ → UnitTime,
        ⋂ _ : (∀ i < n, s i ≤ t i),
        ⋂ _ : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
          (fun i => Ioc (s i : ℝ) (t i : ℝ)),
        {φ | ∑ i ∈ Finset.range n, ENNReal.ofReal ((t i : ℝ) - (s i : ℝ)) *
          I (((t i : ℝ) - (s i : ℝ))⁻¹ • (φ (t i) - φ (s i))) ≤ a} := by
    ext φ
    by_cases hφ : φ zeroTime = 0
    · simp [disjointIntervalAction, hφ, K, iSup_le_iff]
    · simp [disjointIntervalAction, hφ, K, ha]
  change IsClosed {φ | disjointIntervalAction I φ ≤ a}
  rw [heq]
  refine hK.inter (isClosed_iInter fun n => isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => ?_)
  have hsum : LowerSemicontinuous (fun φ : C(UnitTime, E) =>
      ∑ i ∈ Finset.range n, ENNReal.ofReal ((t i : ℝ) - (s i : ℝ)) *
        I (((t i : ℝ) - (s i : ℝ))⁻¹ • (φ (t i) - φ (s i)))) := by
    apply lowerSemicontinuous_sum
    intro i _
    refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      (hI.comp ?_) (fun _ _ h => mul_le_mul_right h _)
    exact ((continuous_eval_const _).sub (continuous_eval_const _)).const_smul _
  exact hsum.isClosed_preimage a

theorem finite_disjointIntervalAction_start {φ : C(UnitTime, E)}
    (hφ : disjointIntervalAction I φ ≠ ⊤) : φ zeroTime = 0 := by
  by_contra h
  exact hφ (by simp [disjointIntervalAction, h])

theorem secantSum_le_disjointIntervalAction
    {φ : C(UnitTime, E)} (hφ : φ zeroTime = 0) (n : ℕ) (s t : ℕ → UnitTime)
    (hst : ∀ i < n, s i ≤ t i)
    (hd : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
      (fun i => Ioc (s i : ℝ) (t i : ℝ))) :
    ∑ i ∈ Finset.range n, ENNReal.ofReal ((t i : ℝ) - (s i : ℝ)) *
      I (((t i : ℝ) - (s i : ℝ))⁻¹ • (φ (t i) - φ (s i))) ≤
    disjointIntervalAction I φ := by
  simp only [disjointIntervalAction, if_pos hφ]
  refine le_iSup_of_le n (le_iSup_of_le s (le_iSup_of_le t (le_iSup_of_le hst ?_)))
  exact le_iSup_of_le hd le_rfl

/-- A bound on discrete costs controls the total variation across a disjoint family. -/
private theorem variation_le_disjointIntervalAction
    {φ : C(UnitTime, E)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hφ : disjointIntervalAction I φ ≤ c) {q M : ℝ} (hq : 0 < q)
    (hgrow : ∀ v : E, ENNReal.ofReal (q * ‖v‖ - M) ≤ I v)
    (n : ℕ) (s t : ℕ → UnitTime)
    (hst : ∀ i < n, s i ≤ t i)
    (hd : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
      (fun i => Ioc (s i : ℝ) (t i : ℝ))) :
    q * (∑ i ∈ Finset.range n, dist (φ (t i)) (φ (s i))) ≤
      c.toReal + M * (∑ i ∈ Finset.range n, ((t i : ℝ) - (s i : ℝ))) := by
  have h0 := finite_disjointIntervalAction_start (ne_top_of_le_ne_top hc hφ)
  have hsec := (secantSum_le_disjointIntervalAction h0 n s t hst hd).trans hφ
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
      ENNReal.ofReal (q * dist (φ (t i)) (φ (s i)) - M * ((t i : ℝ) - (s i : ℝ))) ≤
      ENNReal.ofReal ((t i : ℝ) - (s i : ℝ)) *
        I (((t i : ℝ) - (s i : ℝ))⁻¹ • (φ (t i) - φ (s i))) := by
    have hle : (s i : ℝ) ≤ (t i : ℝ) := hst i (Finset.mem_range.mp hi)
    rcases eq_or_lt_of_le hle with heq | hlt
    · have he : s i = t i := Subtype.ext heq
      simp [he]
    · have hlen := sub_pos.mpr hlt
      refine le_trans ?_ (mul_le_mul_right (hgrow _) _)
      rw [← ENNReal.ofReal_mul hlen.le, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hlen), dist_eq_norm]
      apply ENNReal.ofReal_le_ofReal
      field_simp [hlen.ne'] <;> ring_nf <;> exact le_rfl
  have hsum := (Finset.sum_le_sum hterm).trans hsec
  have hofReal_sum (s : Finset ℕ) (f : ℕ → ℝ) :
      ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ENNReal.ofReal_add_le.trans (add_le_add_right ih _)
  have hs : ENNReal.ofReal (∑ i ∈ Finset.range n,
      (q * dist (φ (t i)) (φ (s i)) - M * ((t i : ℝ) - (s i : ℝ)))) ≤ c :=
    (hofReal_sum _ _).trans hsum
  rw [ENNReal.ofReal_le_iff_le_toReal hc, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hs
  linarith

/-- The continuous extension by constant values at the endpoints. -/
noncomputable def extendPath (φ : C(UnitTime, E)) (t : ℝ) : E :=
  φ ⟨max 0 (min 1 t), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

theorem extendPath_eq (φ : C(UnitTime, E)) (t : UnitTime) :
    extendPath φ t = φ t := by
  unfold extendPath
  congr 1
  apply Subtype.ext
  exact (congrArg (max 0) (min_eq_right t.property.2)).trans (max_eq_right t.property.1)

/-- Superlinear growth of the slope rate makes every finite-action path absolutely continuous. -/
theorem absolutelyContinuous_extendPath
    (hgrow : ∀ q > (0 : ℝ), ∃ M ≥ 0, ∀ v : E, ENNReal.ofReal (q * ‖v‖ - M) ≤ I v)
    {φ : C(UnitTime, E)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hφ : disjointIntervalAction I φ ≤ c) :
    AbsolutelyContinuousOnInterval (extendPath φ) 0 1 := by
  classical
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  let q := (c.toReal + 1) / ε
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨M, hM, hg⟩ := hgrow q hq
  refine ⟨(M + 1)⁻¹, by positivity, ?_⟩
  rintro ⟨n, intervals⟩ ⟨hends, hd⟩ hshort
  simp only at hends hd hshort ⊢
  let s (i : ℕ) : UnitTime := if hi : i < n then
    ⟨min (intervals i).1 (intervals i).2, by
      have hs := hends i (Finset.mem_range.mpr hi)
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact ⟨le_min hs.1.1 hs.2.1, (min_le_left _ _).trans hs.1.2⟩⟩
    else zeroTime
  let t (i : ℕ) : UnitTime := if hi : i < n then
    ⟨max (intervals i).1 (intervals i).2, by
      have hs := hends i (Finset.mem_range.mpr hi)
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact ⟨hs.1.1.trans (le_max_left _ _), max_le hs.1.2 hs.2.2⟩⟩
    else zeroTime
  have hs (i : ℕ) (hi : i < n) : (s i : ℝ) = min (intervals i).1 (intervals i).2 := by
    simp [s, hi]
  have ht (i : ℕ) (hi : i < n) : (t i : ℝ) = max (intervals i).1 (intervals i).2 := by
    simp [t, hi]
  have hst (i : ℕ) (hi : i < n) : s i ≤ t i := by
    change (s i : ℝ) ≤ (t i : ℝ)
    rw [hs i hi, ht i hi]
    exact (min_le_left _ _).trans (le_max_left _ _)
  have hd' : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
      (fun i => Ioc (s i : ℝ) (t i : ℝ)) := by
    intro i hi j hj hij
    simpa [uIoc, hs i (Finset.mem_range.mp hi), ht i (Finset.mem_range.mp hi),
      hs j (Finset.mem_range.mp hj), ht j (Finset.mem_range.mp hj)] using hd hi hj hij
  have hlength : ∑ i ∈ Finset.range n, ((t i : ℝ) - (s i : ℝ)) =
      ∑ i ∈ Finset.range n, dist (intervals i).1 (intervals i).2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ht i (Finset.mem_range.mp hi), hs i (Finset.mem_range.mp hi), Real.dist_eq,
      max_sub_min_eq_abs']
  have hdist : ∑ i ∈ Finset.range n, dist (φ (t i)) (φ (s i)) =
      ∑ i ∈ Finset.range n, dist (extendPath φ (intervals i).1) (extendPath φ (intervals i).2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← extendPath_eq φ (t i), ← extendPath_eq φ (s i), ht i (Finset.mem_range.mp hi),
      hs i (Finset.mem_range.mp hi)]
    rcases le_total (intervals i).1 (intervals i).2 with h | h
    · rw [max_eq_right h, min_eq_left h, dist_comm]
    · rw [max_eq_left h, min_eq_right h]
  have hvar := variation_le_disjointIntervalAction hc hφ hq hg n s t hst hd'
  rw [hlength, hdist] at hvar
  have hM' : M + 1 > 0 := by linarith
  have hbound : M * (∑ i ∈ Finset.range n, dist (intervals i).1 (intervals i).2) < 1 := by
    calc
      _ ≤ (M + 1) * (∑ i ∈ Finset.range n, dist (intervals i).1 (intervals i).2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ => dist_nonneg)
      _ < (M + 1) * (M + 1)⁻¹ := mul_lt_mul_of_pos_left hshort hM'
      _ = 1 := mul_inv_cancel₀ hM'.ne'
  apply (mul_lt_mul_iff_right₀ hq).mp
  calc
    _ ≤ _ := hvar
    _ < c.toReal + 1 := by linarith
    _ = q * ε := by dsimp [q]; field_simp

private theorem dist_le_disjointIntervalAction {φ : C(UnitTime, E)} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (hφ : disjointIntervalAction I φ ≤ c)
    {q M : ℝ} (hq : 0 < q)
    (hgrow : ∀ v : E, ENNReal.ofReal (q * ‖v‖ - M) ≤ I v)
    (s t : UnitTime) :
    q * dist (φ s) (φ t) ≤ c.toReal + M * dist s t := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t s (le_of_not_ge hst)
  have h := variation_le_disjointIntervalAction hc hφ hq hgrow 1
    (fun _ => s) (fun _ => t) (fun _ _ => hst) (by
      intro i hi j hj hij
      have hi' : i = 0 := by simpa using hi
      have hj' : j = 0 := by simpa using hj
      exact (hij (hi'.trans hj'.symm)).elim)
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  have hdist : dist s t = (t : ℝ) - (s : ℝ) := by
    change dist (s : ℝ) (t : ℝ) = _
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst')]
  simpa [dist_comm (φ s) (φ t), hdist] using h

/-- The disjoint-interval action has compact sublevel sets in the uniform topology. -/
theorem goodRate_disjointIntervalAction [ProperSpace E] (hI : LowerSemicontinuous I)
    (hgrow : ∀ q > (0 : ℝ), ∃ M ≥ 0, ∀ v : E, ENNReal.ofReal (q * ‖v‖ - M) ≤ I v) :
    GoodRate (disjointIntervalAction I) := by
  let hcont := lowerSemicontinuous_disjointIntervalAction hI
  refine ⟨hcont, fun c hc => ?_⟩
  let K := {φ | disjointIntervalAction I φ ≤ c}
  let e := (ContinuousMap.isometryEquivBoundedOfCompact UnitTime E).toHomeomorph
  let A := e.symm ⁻¹' K
  have hA : IsClosed A := (hcont.isClosed_preimage c).preimage e.symm.continuous
  suffices h : IsCompact A by
    have heq : K = e.symm '' A := by
      ext φ
      constructor
      · exact fun hφ => ⟨e φ, by simpa [A], e.symm_apply_apply φ⟩
      · rintro ⟨g, hg, rfl⟩
        exact hg
    change IsCompact K
    rw [heq]
    exact h.image e.symm.continuous
  obtain ⟨M, hM, hg⟩ := hgrow 1 one_pos
  refine BoundedContinuousFunction.arzela_ascoli₂ _ (isCompact_closedBall (0 : E) (c.toReal + M))
    A hA ?_ ?_
  · intro f t hf
    let φ := e.symm f
    have hφ : disjointIntervalAction I φ ≤ c := hf
    have h0 := finite_disjointIntervalAction_start (ne_top_of_le_ne_top hc hφ)
    have hdist := dist_le_disjointIntervalAction hc hφ one_pos hg t zeroTime
    have ht : dist t zeroTime ≤ 1 := by
      change dist (t : ℝ) 0 ≤ 1
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] using t.property.2
    rw [Metric.mem_closedBall]
    change dist (φ t) 0 ≤ _
    rw [← h0]
    calc
      dist (φ t) (φ zeroTime) ≤ c.toReal + M * dist t zeroTime := by
        simpa only [one_mul] using hdist
      _ ≤ c.toReal + M := by
        simpa only [mul_one] using add_le_add_right (mul_le_mul_of_nonneg_left ht hM) c.toReal
  · intro t
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    let q := (c.toReal + 1) / ε
    have hq : 0 < q := by dsimp [q]; positivity
    obtain ⟨M, hM, hg⟩ := hgrow q hq
    refine ⟨(M + 1)⁻¹, by positivity, fun s hs f => ?_⟩
    let φ := e.symm f.val
    have hφ : disjointIntervalAction I φ ≤ c := f.property
    change dist (φ t) (φ s) < ε
    have hM' : M + 1 > 0 := by linarith
    have hsmall : M * dist s t < 1 := by
      calc
        _ ≤ (M + 1) * dist s t := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < (M + 1) * (M + 1)⁻¹ := mul_lt_mul_of_pos_left hs hM'
        _ = 1 := mul_inv_cancel₀ hM'.ne'
    apply (mul_lt_mul_iff_right₀ hq).mp
    calc
      q * dist (φ t) (φ s) ≤ c.toReal + M * dist s t := by
        simpa only [dist_comm t s] using dist_le_disjointIntervalAction hc hφ hq hg t s
      _ < c.toReal + 1 := by linarith
      _ = q * ε := by dsimp [q]; field_simp

end Mogulskii


