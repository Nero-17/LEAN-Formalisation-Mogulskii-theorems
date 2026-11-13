import Mogulskii.CramerRate
import Mogulskii.GridBlocks
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

private theorem measure_sum_ge_cgf (f : E → ℝ) (hf : Measurable f)
    (hExp : Integrable (fun y ↦ Real.exp (1 * f y)) ν) (n : ℕ) (b : ℝ) :
    (Measure.pi fun _ : Fin n ↦ ν) {x | (n : ℝ) * b ≤ ∑ i, f (x i)} ≤
      ENNReal.ofReal (Real.exp (-(n * (b - cgf f ν 1)))) := by
  let μ := Measure.pi fun _ : Fin n ↦ ν
  let X : Fin n → (Fin n → E) → ℝ := fun i x ↦ f (x i)
  have hX : ∀ i, Measurable (X i) := fun i ↦ hf.comp (measurable_pi_apply i)
  have hind : iIndepFun X μ := iIndepFun_pi (fun _ ↦ hf.aemeasurable)
  have hmap (i : Fin n) : MeasurePreserving (fun x : Fin n → E ↦ x i) μ ν :=
    measurePreserving_eval _ i
  have hXi (i : Fin n) : Integrable (fun x ↦ Real.exp (1 * X i x)) μ :=
    (hmap i).integrable_comp_of_integrable hExp
  have hsum := hind.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ ↦ hXi i)
  have hbound := measure_ge_le_exp_cgf (X := ∑ i, X i) ((n : ℝ) * b) zero_le_one hsum
  rw [hind.cgf_sum hX (fun i _ ↦ hXi i)] at hbound
  have hcgf (i : Fin n) : cgf (X i) μ 1 = cgf f ν 1 := by
    have hmeas : AEStronglyMeasurable (fun y => Real.exp (1 * f y))
        (μ.map fun x : Fin n → E => x i) := by
      rw [(hmap i).map_eq]
      exact hExp.aestronglyMeasurable
    change Real.log (mgf (f ∘ (fun x : Fin n → E => x i)) μ 1) =
      Real.log (mgf f ν 1)
    rw [← (mgf_map (hmap i).measurable.aemeasurable hmeas), (hmap i).map_eq]
  simp only [hcgf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_apply] at hbound
  have h := ENNReal.ofReal_le_ofReal hbound
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  convert h using 3 <;> ring

private theorem measure_mean_dual_ge (t : E →L[ℝ] ℝ)
    (hExp : Integrable (fun y ↦ Real.exp (1 * t y)) ν) {n : ℕ} (hn : 0 < n) (r : ℝ) :
    meanLaw ν n {x | r + cgf t ν 1 ≤ t x} ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  rw [meanLaw, Measure.map_apply (measurable_mean n)
    (isClosed_le continuous_const t.continuous).measurableSet]
  have hsub : (fun x : Fin n → E ↦ (n : ℝ)⁻¹ • ∑ j, x j) ⁻¹'
      {x | r + cgf t ν 1 ≤ t x} ⊆ {x | (n : ℝ) * (r + cgf t ν 1) ≤ ∑ j, t (x j)} := by
    intro x hx
    change r + cgf t ν 1 ≤ t ((n : ℝ)⁻¹ • ∑ j, x j) at hx
    change (n : ℝ) * (r + cgf t ν 1) ≤ ∑ j, t (x j)
    rw [map_smul, map_sum, smul_eq_mul, ← div_eq_inv_mul] at hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa only [mul_comm] using (le_div_iff₀ hn').mp hx
  refine (measure_mono hsub).trans ?_
  simpa only [add_sub_cancel_right] using measure_sum_ge_cgf t t.continuous.measurable
    hExp n (r + cgf t ν 1)

private theorem measure_mean_norm_ge
    (hExp : Integrable (fun y : E ↦ Real.exp ‖y‖) ν) {n : ℕ} (hn : 0 < n) (r : ℝ) :
    meanLaw ν n {x | r + cgf (fun y : E ↦ ‖y‖) ν 1 ≤ ‖x‖} ≤
      ENNReal.ofReal (Real.exp (-(n * r))) := by
  rw [meanLaw, Measure.map_apply (measurable_mean n)
    (isClosed_le continuous_const continuous_norm).measurableSet]
  have hsub : (fun x : Fin n → E ↦ (n : ℝ)⁻¹ • ∑ j, x j) ⁻¹'
      {x | r + cgf (fun y : E ↦ ‖y‖) ν 1 ≤ ‖x‖} ⊆
      {x | (n : ℝ) * (r + cgf (fun y : E ↦ ‖y‖) ν 1) ≤ ∑ j, ‖x j‖} := by
    intro x hx
    change r + cgf (fun y : E ↦ ‖y‖) ν 1 ≤ ‖(n : ℝ)⁻¹ • ∑ j, x j‖ at hx
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul] at hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (le_div_iff₀ hn').mp hx
    rw [mul_comm] at h
    exact h.trans (norm_sum_le _ _)
  refine (measure_mono hsub).trans ?_
  have h := measure_sum_ge_cgf (ν := ν) (fun y : E ↦ ‖y‖) continuous_norm.measurable
    (by simpa using hExp) n (r + cgf (fun y : E ↦ ‖y‖) ν 1)
  rw [add_sub_cancel_right] at h
  exact h

theorem cramer_upper
    (hExp : ∀ q ≥ 0, Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    {F : Set E} (hF : IsClosed F) {r : ℝ}
    (hr : (r : EReal) < (⨅ x ∈ F, cramerRateLaw ν x : ℝ≥0∞)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      meanLaw ν n F ≤ C * ENNReal.ofReal (Real.exp (-(n * r))) := by
  have hmeanProb (n : ℕ) : IsProbabilityMeasure (meanLaw ν n) :=
    Measure.isProbabilityMeasure_map (measurable_mean n).aemeasurable
  rcases le_or_gt r 0 with hr0 | hr0
  · refine ⟨1, ENNReal.one_ne_top, Eventually.of_forall fun n ↦ ?_⟩
    rw [one_mul]
    exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (Real.one_le_exp
      (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hr0))))
  let R := r + cgf (fun y : E ↦ ‖y‖) ν 1
  let K := F ∩ Metric.closedBall (0 : E) R
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left hF
  have hrx (x : E) (hx : x ∈ F) : ENNReal.ofReal r < cramerRateLaw ν x := by
    apply EReal.coe_ennreal_lt_coe_ennreal_iff.1
    rw [EReal.coe_ennreal_ofReal, max_eq_left hr0.le]
    exact hr.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x hx))
  have hdual (x : E) (hx : x ∈ F) : ∃ t : E →L[ℝ] ℝ, r + cgf t ν 1 < t x := by
    obtain ⟨t, ht⟩ := lt_iSup_iff.1 (hrx x hx)
    exact ⟨t, by linarith [(ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0.le).1 ht]⟩
  classical
  choose! t ht using hdual
  obtain ⟨cover, hcover, hc⟩ := hK.elim_nhds_subcover
    (fun x ↦ {y | r + cgf (t x) ν 1 < t x y}) fun x hx ↦
      (isOpen_lt continuous_const (t x).continuous).mem_nhds (ht x hx.1)
  have hsub : F ⊆
      (⋃ x ∈ cover, {y | r + cgf (t x) ν 1 ≤ t x y}) ∪ {y | R ≤ ‖y‖} := by
    intro y hy
    by_cases h : R ≤ ‖y‖
    · exact Or.inr h
    · have hyK : y ∈ K := ⟨hy, by simpa [Metric.mem_closedBall, dist_zero_right] using
          (lt_of_not_ge h).le⟩
      obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (hc hyK)
      refine Or.inl (mem_iUnion₂.2 ⟨x, hx, ?_⟩)
      change r + cgf (t x) ν 1 ≤ t x y
      exact le_of_lt hxy
  refine ⟨(cover.card : ℝ≥0∞) + 1, by simp, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hb (x : E) : meanLaw ν n {y | r + cgf (t x) ν 1 ≤ t x y} ≤
      ENNReal.ofReal (Real.exp (-(n * r))) := by
    apply measure_mean_dual_ge (t x) _ hn
    refine (hExp ‖t x‖ (norm_nonneg _)).mono' (by fun_prop) (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp, one_mul]
    exact (le_abs_self _).trans ((t x).le_opNorm y)
  have hU := (measure_biUnion_finset_le (μ := meanLaw ν n) cover
    (fun x ↦ {y | r + cgf (t x) ν 1 ≤ t x y})).trans (Finset.sum_le_sum fun x _ ↦ hb x)
  have htail : meanLaw ν n {y | R ≤ ‖y‖} ≤ ENNReal.ofReal (Real.exp (-(n * r))) :=
    measure_mean_norm_ge (by simpa using hExp 1 zero_le_one) hn r
  calc
    _ ≤ meanLaw ν n (⋃ x ∈ cover, {y | r + cgf (t x) ν 1 ≤ t x y}) +
      meanLaw ν n {y | R ≤ ‖y‖} := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ _ := by simpa [add_mul, nsmul_eq_mul] using add_le_add hU htail

end Mogulskii

