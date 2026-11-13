import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open Filter Set MeasureTheory
open scoped Topology

namespace Mogulskii

/-- The lowest Dirichlet eigenfunction on an interval. -/
noncomputable def intervalSine (left right x : ℝ) : ℝ :=
  Real.sin (Real.pi * (x - left) / (right - left))

/-- The lowest eigenvalue for the Brownian generator with variance rate `variance`. -/
noncomputable def intervalEigenvalue (variance left right : ℝ) : ℝ :=
  Real.pi ^ 2 * variance / (2 * (right - left) ^ 2)

theorem intervalSine_pos {left right x : ℝ} (hx : x ∈ Ioo left right) :
    0 < intervalSine left right x := by
  have hwidth : 0 < right - left := sub_pos.mpr (hx.1.trans hx.2)
  unfold intervalSine
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr hx.1)) hwidth
  · apply (div_lt_iff₀ hwidth).2
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hx.2 left) Real.pi_pos

@[simp] theorem intervalSine_left (left right : ℝ) :
    intervalSine left right left = 0 := by simp [intervalSine]

@[simp] theorem intervalSine_right {left right : ℝ} (h : left ≠ right) :
    intervalSine left right right = 0 := by
  unfold intervalSine
  rw [mul_div_cancel_right₀ _ (sub_ne_zero.mpr h.symm), Real.sin_pi]

/-- The law of the final position carried by paths in the survival event. -/
noncomputable def killedEndpointLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (survival : Set Ω) (endpoint : Ω → ℝ) : Measure ℝ :=
  (P.restrict survival).map endpoint

theorem killedEndpointLaw_apply_Icc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {survival : Set Ω} {endpoint : Ω → ℝ} {left right : ℝ}
    (hendpoint : Measurable endpoint) (_hsurvival : MeasurableSet survival)
    (hstay : ∀ ω ∈ survival, endpoint ω ∈ Icc left right) :
    killedEndpointLaw P survival endpoint (Icc left right) = P survival := by
  rw [killedEndpointLaw, Measure.map_apply hendpoint measurableSet_Icc,
    Measure.restrict_apply (hendpoint measurableSet_Icc)]
  congr 1
  exact inter_eq_right.2 hstay

theorem killedEndpointLaw_mono {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {small large : Set Ω} {endpoint : Ω → ℝ}
    (h : small ⊆ large) (hendpoint : Measurable endpoint) :
    killedEndpointLaw P small endpoint ≤ killedEndpointLaw P large endpoint :=
  Measure.map_mono (Measure.restrict_mono h le_rfl) hendpoint

theorem exists_pos_le_intervalSine {left right lower upper : ℝ}
    (hleft : left < lower) (hle : lower ≤ upper) (hright : upper < right) :
    ∃ c > 0, ∀ x ∈ Icc lower upper, c ≤ intervalSine left right x := by
  have hc : Continuous (intervalSine left right) := by unfold intervalSine; fun_prop
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hle) hc.continuousOn
  exact ⟨_, intervalSine_pos ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩, hmin⟩

/-- A subprobability law of the endpoint weighted by survival has mass bounded
below by its integral against the Dirichlet eigenfunction. -/
theorem intervalSine_integral_le_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (left right : ℝ) :
    (∫ y in Icc left right, intervalSine left right y ∂μ) ≤ μ.real (Icc left right) := by
  have hmeas : AEStronglyMeasurable (intervalSine left right)
      (μ.restrict (Icc left right)) := by
    apply Continuous.aestronglyMeasurable
    unfold intervalSine
    fun_prop
  have hint := Integrable.of_bound hmeas 1 (ae_of_all _ fun y ↦ by
    simpa [intervalSine, Real.norm_eq_abs] using
      Real.abs_sin_le_one (Real.pi * (y - left) / (right - left)))
  calc
    _ ≤ ∫ _ in Icc left right, (1 : ℝ) ∂μ :=
      integral_mono hint (integrable_const _) (fun y ↦ Real.sin_le_one _)
    _ = _ := by simp

/-- On a compact interval in the interior, the endpoint mass is bounded by its
integral against the wider interval's Dirichlet eigenfunction. -/
theorem exists_mass_le_intervalSine_integral {left right lower upper : ℝ}
    (hleft : left < lower) (hle : lower ≤ upper) (hright : upper < right) :
    ∃ c > 0, ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
      c * μ.real (Icc lower upper) ≤
        ∫ y in Icc lower upper, intervalSine left right y ∂μ := by
  obtain ⟨c, hc, hmin⟩ := exists_pos_le_intervalSine hleft hle hright
  refine ⟨c, hc, ?_⟩
  intro μ _
  have hmeas : AEStronglyMeasurable (intervalSine left right)
      (μ.restrict (Icc lower upper)) := by
    apply Continuous.aestronglyMeasurable
    unfold intervalSine
    fun_prop
  have hint := Integrable.of_bound hmeas 1 (ae_of_all _ fun y ↦ by
    simpa [intervalSine, Real.norm_eq_abs] using
      Real.abs_sin_le_one (Real.pi * (y - left) / (right - left)))
  calc
    _ = ∫ _ in Icc lower upper, c ∂μ := by simp [mul_comm]
    _ ≤ _ := by
      refine integral_mono_ae (integrable_const _) hint ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hmin)

/-- A killed sine moment gives an exponential lower bound uniformly over any
compact set of interior starting points. -/
theorem exists_uniform_survival_lower_of_sine_moment
    {left right lower upper rate : ℝ} (hleft : left < lower) (hle : lower ≤ upper)
    (hright : upper < right) :
    ∃ c > 0, ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], ∀ (x : ℝ) (_ : x ∈ Icc lower upper) (T : ℝ),
      (∫ y in Icc left right, intervalSine left right y ∂μ) =
        Real.exp (-rate * T) * intervalSine left right x →
      c * Real.exp (-rate * T) ≤ μ.real (Icc left right) := by
  obtain ⟨c, hc, hmin⟩ := exists_pos_le_intervalSine hleft hle hright
  refine ⟨c, hc, ?_⟩
  intro μ _ x hx T hmoment
  calc
    c * Real.exp (-rate * T) ≤ intervalSine left right x * Real.exp (-rate * T) :=
      mul_le_mul_of_nonneg_right (hmin x hx) (Real.exp_pos _).le
    _ = ∫ y in Icc left right, intervalSine left right y ∂μ := by rw [hmoment, mul_comm]
    _ ≤ _ := intervalSine_integral_le_mass μ left right

/-- The sine moment in a wider tube bounds the mass in a narrower tube, uniformly
over the starting point. The measure inequality comes from inclusion of the path events. -/
theorem exists_uniform_survival_upper_of_sine_moment
    {left right lower upper rate : ℝ} (hleft : left < lower) (hle : lower ≤ upper)
    (hright : upper < right) :
    ∃ C > 0, ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      μ ≤ ν → ∀ (x T : ℝ),
      (∫ y in Icc left right, intervalSine left right y ∂ν) =
        Real.exp (-rate * T) * intervalSine left right x →
      μ.real (Icc lower upper) ≤ C * Real.exp (-rate * T) := by
  obtain ⟨c, hc, hmin⟩ := exists_mass_le_intervalSine_integral hleft hle hright
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro μ ν _ _ hmeasure x T hmoment
  have hint : Integrable (intervalSine left right) (ν.restrict (Icc left right)) := by
    apply Integrable.of_bound (C := 1)
    · apply Continuous.aestronglyMeasurable
      unfold intervalSine
      fun_prop
    · exact ae_of_all _ fun y ↦ Real.abs_sin_le_one _
  have hnonneg : 0 ≤ᵐ[ν.restrict (Icc left right)] intervalSine left right := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun y hy ↦ ?_)
    have hwidth : 0 < right - left := sub_pos.mpr (hleft.trans_le hle |>.trans hright)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hy.1)) hwidth.le
    · exact (div_le_iff₀ hwidth).2 (mul_le_mul_of_nonneg_left (sub_le_sub_right hy.2 _) Real.pi_pos.le)
  have hsubset : Icc lower upper ⊆ Icc left right :=
    fun _ hy ↦ ⟨hleft.le.trans hy.1, hy.2.trans hright.le⟩
  have hmass : μ.real (Icc lower upper) ≤ ν.real (Icc lower upper) :=
    ENNReal.toReal_mono (measure_ne_top ν _) (hmeasure _)
  have hcomparison : c * μ.real (Icc lower upper) ≤ Real.exp (-rate * T) := calc
    _ ≤ c * ν.real (Icc lower upper) := mul_le_mul_of_nonneg_left hmass hc.le
    _ ≤ ∫ y in Icc lower upper, intervalSine left right y ∂ν := hmin ν
    _ ≤ ∫ y in Icc left right, intervalSine left right y ∂ν :=
      setIntegral_mono_set hint hnonneg (ae_of_all _ hsubset)
    _ = Real.exp (-rate * T) * intervalSine left right x := hmoment
    _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le (Real.sin_le_one _)
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀' hc).2 hcomparison

theorem tendsto_log_div_of_exponential_bounds {p : ℝ → ℝ} {c C rate : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᶠ T in atTop, c * Real.exp (-rate * T) ≤ p T)
    (hupper : ∀ᶠ T in atTop, p T ≤ C * Real.exp (-rate * T)) :
    Tendsto (fun T ↦ Real.log (p T) / T) atTop (𝓝 (-rate)) := by
  have hbound (a : ℝ) : Tendsto (fun T : ℝ ↦ Real.log a / T - rate) atTop (𝓝 (-rate)) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log a)).sub_const rate
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hbound c) (hbound C) ?_ ?_
  · filter_upwards [hlower, eventually_gt_atTop (0 : ℝ)] with T hT ht
    have hpos := mul_pos hc (Real.exp_pos (-rate * T))
    have hlog := Real.log_le_log hpos hT
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    rw [le_div_iff₀ ht, sub_mul, div_mul_cancel₀ _ ht.ne']
    linarith
  · filter_upwards [hlower, hupper, eventually_gt_atTop (0 : ℝ)] with T hlow hup ht
    have hpos := (mul_pos hc (Real.exp_pos (-rate * T))).trans_le hlow
    have hlog := Real.log_le_log hpos hup
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    rw [div_le_iff₀ ht, sub_mul, div_mul_cancel₀ _ ht.ne']
    linarith

/-- Allow either exponent to approach the target eigenvalue from its respective side. -/
theorem tendsto_log_div_of_approximate_exponential_bounds {p : ℝ → ℝ} {rate : ℝ}
    (hlower : ∀ ε > 0, ∃ c > 0, ∀ᶠ T in atTop, c * Real.exp (-(rate + ε) * T) ≤ p T)
    (hupper : ∀ ε > 0, ∃ C > 0, ∀ᶠ T in atTop, p T ≤ C * Real.exp (-(rate - ε) * T)) :
    Tendsto (fun T ↦ Real.log (p T) / T) atTop (𝓝 (-rate)) := by
  have hbound (a b : ℝ) : Tendsto (fun T : ℝ ↦ Real.log a / T - b) atTop (𝓝 (-b)) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log a)).sub_const b
  rw [tendsto_order]
  constructor
  · intro b hb
    let ε := (-rate - b) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨c, hc, hlow⟩ := hlower ε hε
    have hlim : b < -(rate + ε) := by dsimp [ε]; linarith
    have hev := (hbound c (rate + ε)).eventually (eventually_gt_nhds hlim)
    filter_upwards [hlow, hev, eventually_gt_atTop (0 : ℝ)] with T hT hlogT ht
    refine hlogT.trans_le ?_
    have hlog := Real.log_le_log (mul_pos hc (Real.exp_pos (-(rate + ε) * T))) hT
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    rw [le_div_iff₀ ht, sub_mul, div_mul_cancel₀ _ ht.ne']
    linarith
  · intro b hb
    let ε := (b + rate) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨C, hC, hup⟩ := hupper ε hε
    obtain ⟨c, hc, hlow⟩ := hlower 1 zero_lt_one
    have hlim : -(rate - ε) < b := by dsimp [ε]; linarith
    have hev := (hbound C (rate - ε)).eventually (eventually_lt_nhds hlim)
    filter_upwards [hlow, hup, hev, eventually_gt_atTop (0 : ℝ)] with T hT hT' hlogT ht
    refine lt_of_le_of_lt ?_ hlogT
    have hlog := Real.log_le_log ((mul_pos hc (Real.exp_pos _)).trans_le hT) hT'
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    rw [div_le_iff₀ ht, sub_mul, div_mul_cancel₀ _ ht.ne']
    linarith

end Mogulskii

