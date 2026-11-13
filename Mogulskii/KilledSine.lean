import Mogulskii.SineMartingale
import Mogulskii.StoppedGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Mogulskii

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

private theorem integral_gridSine_stopped (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (left right x : ℝ) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, gridSine B left right x T n (gridExit B left right x T n ω) ω ∂P) =
      intervalSine left right x := by
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F := brownianGridFiltration hm (monotone_uniformGrid T n)
  let τ : Ω → WithTop ℕ := fun ω ↦ ↑(gridExit B left right x T n ω)
  have hM : Martingale (gridSine B left right x T n) F P :=
    martingale_brownianSine_grid hB hm _ _ (monotone_uniformGrid T n)
  have hA : Adapted F (fun k ω ↦ x + B (uniformGrid T n k) ω) := by
    intro i
    exact measurable_const.add ((Filtration.stronglyAdapted_natural
      (fun u ↦ (hm u).stronglyMeasurable) (uniformGrid T n i)).measurable)
  have hτ : IsStoppingTime F τ :=
    hA.isStoppingTime_hittingBtwn (n := 0) (n' := n + 1) measurableSet_Icc.compl
  have hbdd : ∀ ω, τ ω ≤ ((n + 1 : ℕ) : WithTop ℕ) := by
    intro ω
    have hexit : gridExit B left right x T n ω ≤ n + 1 := hittingBtwn_le ω
    exact WithTop.coe_le_coe.mpr hexit
  have h0 : IsStoppingTime F (fun _ : Ω ↦ ((0 : ℕ) : WithTop ℕ)) :=
    isStoppingTime_const F (0 : ℕ)
  have h0τ : (fun _ : Ω ↦ ((0 : ℕ) : WithTop ℕ)) ≤ τ := fun ω ↦
    WithTop.coe_le_coe.mpr (Nat.zero_le (gridExit B left right x T n ω))
  have hle := hM.submartingale.expected_stoppedValue_mono h0 hτ h0τ hbdd
  have hge := hM.neg.submartingale.expected_stoppedValue_mono h0 hτ h0τ hbdd
  have hle' : (∫ ω, gridSine B left right x T n 0 ω ∂P) ≤
       ∫ ω, gridSine B left right x T n (gridExit B left right x T n ω) ω ∂P := hle
  have hge' : (∫ ω, -gridSine B left right x T n 0 ω ∂P) ≤
       ∫ ω, -gridSine B left right x T n (gridExit B left right x T n ω) ω ∂P := hge
  rw [integral_neg, integral_neg, neg_le_neg_iff] at hge'
  rw [le_antisymm hge' hle']
  calc
    _ = ∫ _ : Ω, intervalSine left right x ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      simp [gridSine, brownianSine_eq, hω]
    _ = _ := by simp

/-- Brownian motion killed upon leaving a closed interval preserves the first sine moment
up to the exponential factor given by the Dirichlet eigenvalue. -/
theorem killed_brownian_sine_moment (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω))
    {left right x : ℝ} (hlr : left < right) (hx : x ∈ Icc left right) (T : ℝ≥0) :
    (∫ ω in intervalSurvival (fun t ω ↦ x + B t ω) left right T,
      intervalSine left right (x + B T ω) ∂P) =
      Real.exp (-intervalEigenvalue 1 left right * (T : ℝ)) * intervalSine left right x := by
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let S := intervalSurvival (fun t ω ↦ x + B t ω) left right T
  have hS : MeasurableSet S :=
    measurableSet_intervalSurvival (fun t ↦ measurable_const.add (hm t))
      (fun ω ↦ continuous_const.add (hc ω)) left right T
  let stopped := fun n ω ↦ gridSine B left right x T n (gridExit B left right x T n ω) ω
  have hExit (n : ℕ) (ω : Ω) : gridExit B left right x T n ω ≤ n + 1 :=
    hittingBtwn_le ω
  have hint (n : ℕ) : Integrable (stopped n) P := by
    let F := brownianGridFiltration hm (monotone_uniformGrid T n)
    let τ : Ω → WithTop ℕ := fun ω ↦ ↑(gridExit B left right x T n ω)
    have hM : Martingale (gridSine B left right x T n) F P :=
      martingale_brownianSine_grid hB.toIsPreBrownianReal hm _ _ (monotone_uniformGrid T n)
    have hA : Adapted F (fun k ω ↦ x + B (uniformGrid T n k) ω) := by
      intro i
      exact measurable_const.add ((Filtration.stronglyAdapted_natural
        (fun u ↦ (hm u).stronglyMeasurable) (uniformGrid T n i)).measurable)
    have hτ : IsStoppingTime F τ :=
      hA.isStoppingTime_hittingBtwn (n := 0) (n' := n + 1) measurableSet_Icc.compl
    have hstopped : stoppedValue (gridSine B left right x T n) τ = stopped n := rfl
    rw [← hstopped]
    exact hM.submartingale.integrable_stoppedValue hτ (N := n + 1)
      (fun ω ↦ WithTop.coe_le_coe.mpr (hExit n ω))
  have hlimit := tendsto_integral_of_dominated_convergence
    (μ := P) (F := stopped) (f := S.indicator
      (fun ω ↦ brownianSine (Real.pi / (right - left)) (x - left) T (B T ω)))
    (fun _ ↦ Real.exp (intervalEigenvalue 1 left right * (T : ℝ)))
    (fun n ↦ (hint n).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ ae_of_all _ (fun ω ↦ norm_brownianSine_le left right x _
      ((monotone_uniformGrid T n (hExit n ω)).trans_eq (uniformGrid_last T n))))
    (by filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
        exact gridSine_tendsto left right x hlr T (hc ω) hω hx)
  simp only [stopped, integral_gridSine_stopped hB.toIsPreBrownianReal hm] at hlimit
  have hEq := tendsto_nhds_unique hlimit tendsto_const_nhds
  rw [integral_indicator hS] at hEq
  simp only [brownianSine_eq, integral_const_mul] at hEq
  rw [neg_mul, Real.exp_neg, ← hEq, ← mul_assoc,
    inv_mul_cancel₀ (Real.exp_ne_zero _), one_mul]

end Mogulskii

