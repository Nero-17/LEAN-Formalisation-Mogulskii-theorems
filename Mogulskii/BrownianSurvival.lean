import Mogulskii.KilledSine

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Mogulskii

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

theorem uniform_closed_survival_lower
    {left right lower upper : ℝ} (hleft : left < lower) (hle : lower ≤ upper)
    (hright : upper < right) :
    ∃ c > 0, ∀ (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω), IsBrownianReal B P →
      (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) →
      ∀ x ∈ Icc lower upper, ∀ T : ℝ≥0,
        c * Real.exp (-intervalEigenvalue 1 left right * (T : ℝ)) ≤
          P.real (intervalSurvival (fun t ω ↦ x + B t ω) left right T) := by
  have hlr := (hleft.trans_le hle).trans hright
  obtain ⟨c, hcpos, hmin⟩ := exists_pos_le_intervalSine hleft hle hright
  refine ⟨c, hcpos, fun B P hB hm hc x hx T ↦ ?_⟩
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let S := intervalSurvival (fun t ω ↦ x + B t ω) left right T
  have hmoment := killed_brownian_sine_moment hB hm hc hlr
    ⟨hleft.le.trans hx.1, hx.2.trans hright.le⟩ T
  have hmeas : Measurable (fun ω ↦ intervalSine left right (x + B T ω)) := by
    have hSine : Continuous (intervalSine left right) := by unfold intervalSine; fun_prop
    exact hSine.measurable.comp (measurable_const.add (hm T))
  have hint : Integrable (fun ω ↦ intervalSine left right (x + B T ω))
      (P.restrict S) := Integrable.of_bound hmeas.aestronglyMeasurable 1
        (ae_of_all _ fun _ ↦ Real.abs_sin_le_one _)
  calc
    _ ≤ intervalSine left right x * Real.exp (-intervalEigenvalue 1 left right * (T : ℝ)) :=
      mul_le_mul_of_nonneg_right (hmin x hx) (Real.exp_pos _).le
    _ = ∫ ω in S, intervalSine left right (x + B T ω) ∂P := by rw [hmoment, mul_comm]
    _ ≤ ∫ _ in S, (1 : ℝ) ∂P := integral_mono hint (integrable_const _) (fun _ ↦ Real.sin_le_one _)
    _ = _ := by simp [S]

theorem uniform_closed_survival_upper
    {left right lower upper : ℝ} (hleft : left < lower) (hle : lower ≤ upper)
    (hright : upper < right) :
    ∃ C > 0, ∀ (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω), IsBrownianReal B P →
      (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) →
      ∀ x : ℝ, ∀ T : ℝ≥0,
        P.real (intervalSurvival (fun t ω ↦ x + B t ω) lower upper T) ≤
          C * Real.exp (-intervalEigenvalue 1 left right * (T : ℝ)) := by
  have hlr := (hleft.trans_le hle).trans hright
  obtain ⟨c, hcpos, hmin⟩ := exists_pos_le_intervalSine hleft hle hright
  refine ⟨c⁻¹, inv_pos.mpr hcpos, fun B P hB hm hc x T ↦ ?_⟩
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let wide := intervalSurvival (fun t ω ↦ x + B t ω) left right T
  let narrow := intervalSurvival (fun t ω ↦ x + B t ω) lower upper T
  have hwide : MeasurableSet wide :=
    measurableSet_intervalSurvival (fun t ↦ measurable_const.add (hm t))
      (fun ω ↦ continuous_const.add (hc ω)) left right T
  have hnarrow : MeasurableSet narrow :=
    measurableSet_intervalSurvival (fun t ↦ measurable_const.add (hm t))
      (fun ω ↦ continuous_const.add (hc ω)) lower upper T
  by_cases hx : x ∈ Icc lower upper
  · have hmoment := killed_brownian_sine_moment hB hm hc hlr
      ⟨hleft.le.trans hx.1, hx.2.trans hright.le⟩ T
    have hmeas : Measurable (fun ω ↦ intervalSine left right (x + B T ω)) := by
      have hSine : Continuous (intervalSine left right) := by unfold intervalSine; fun_prop
      exact hSine.measurable.comp (measurable_const.add (hm T))
    have hint (A : Set Ω) : Integrable (fun ω ↦ intervalSine left right (x + B T ω))
        (P.restrict A) := Integrable.of_bound hmeas.aestronglyMeasurable 1
          (ae_of_all _ fun _ ↦ Real.abs_sin_le_one _)
    have hsubset : narrow ⊆ wide :=
      fun ω hω t ht ↦ ⟨hleft.le.trans (hω t ht).1, (hω t ht).2.trans hright.le⟩
    have hnonneg : 0 ≤ᵐ[P.restrict wide] (fun ω ↦ intervalSine left right (x + B T ω)) := by
      refine (ae_restrict_iff' hwide).2 (ae_of_all _ fun ω hω ↦ ?_)
      have h := hω T le_rfl
      unfold intervalSine
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h.1)) (sub_pos.mpr hlr).le
      · exact (div_le_iff₀ (sub_pos.mpr hlr)).2
          (mul_le_mul_of_nonneg_left (sub_le_sub_right h.2 _) Real.pi_pos.le)
    have hbound : c * P.real narrow ≤ Real.exp (-intervalEigenvalue 1 left right * (T : ℝ)) := calc
      _ = ∫ _ in narrow, c ∂P := by simp [mul_comm]
      _ ≤ ∫ ω in narrow, intervalSine left right (x + B T ω) ∂P := by
        refine integral_mono_ae (integrable_const _) (hint narrow) ((ae_restrict_iff' hnarrow).2 ?_)
        exact ae_of_all _ (fun ω hω ↦ hmin _ (hω T le_rfl))
      _ ≤ ∫ ω in wide, intervalSine left right (x + B T ω) ∂P :=
        setIntegral_mono_set (hint wide) hnonneg (ae_of_all _ hsubset)
      _ = _ * intervalSine left right x := hmoment
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le (Real.sin_le_one _)
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀' hcpos).2 hbound
  · have hnull : P narrow = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      intro hn
      exact hx (by simpa [hω] using hn 0 (show 0 ≤ T from zero_le))
    change (P narrow).toReal ≤ _
    rw [hnull, ENNReal.toReal_zero]
    positivity

end Mogulskii
