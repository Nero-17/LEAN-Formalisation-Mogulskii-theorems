import Mogulskii.ExponentialBounds
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- The Cramér transform, written using continuous linear functionals on the increment space. -/
noncomputable def cramerRateLaw (ν : Measure E) (x : E) : ℝ≥0∞ :=
  ⨆ t : E →L[ℝ] ℝ, ENNReal.ofReal (t x - cgf t ν 1)

theorem lowerSemicontinuous_cramerRateLaw (ν : Measure E) : LowerSemicontinuous (cramerRateLaw ν) :=
  lowerSemicontinuous_iSup fun t ↦
    (ENNReal.continuous_ofReal.comp (t.continuous.sub continuous_const)).lowerSemicontinuous

/-- All exponential moments of the norm bound the log moment generating function
uniformly on bounded dual balls. -/
theorem cgf_dual_le_cgf_norm {ν : Measure E} [IsProbabilityMeasure ν]
    {q : ℝ} (hq : 0 ≤ q) (hExp : Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    (t : E →L[ℝ] ℝ) (ht : ‖t‖ ≤ q) :
    cgf t ν 1 ≤ cgf (fun y : E ↦ ‖y‖) ν q := by
  have hle (y : E) : Real.exp (1 * t y) ≤ Real.exp (q * ‖y‖) := by
    rw [one_mul, Real.exp_le_exp]
    calc
      t y ≤ ‖t y‖ := le_abs_self _
      _ ≤ ‖t‖ * ‖y‖ := t.le_opNorm y
      _ ≤ q * ‖y‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  have htExp : Integrable (fun y ↦ Real.exp (1 * t y)) ν :=
    hExp.mono' (by fun_prop) (Eventually.of_forall fun y ↦ by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact hle y)
  exact Real.log_le_log (mgf_pos htExp) (integral_mono htExp hExp hle)

/-- The Cramér transform grows faster than every linear function of the norm. -/
theorem cramerRate_ge {ν : Measure E} [IsProbabilityMeasure ν]
    {q : ℝ} (hq : 0 ≤ q) (hExp : Integrable (fun y : E ↦ Real.exp (q * ‖y‖)) ν)
    (x : E) :
    ENNReal.ofReal (q * ‖x‖ - cgf (fun y : E ↦ ‖y‖) ν q) ≤ cramerRateLaw ν x := by
  obtain ⟨t, ht, htx⟩ := exists_dual_vector'' ℝ x
  have hs : ‖q • t‖ ≤ q := by
    rw [norm_smul, Real.norm_of_nonneg hq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hq
  refine le_trans ?_ (le_iSup (fun t : E →L[ℝ] ℝ ↦ ENNReal.ofReal (t x - cgf t ν 1)) (q • t))
  apply ENNReal.ofReal_le_ofReal
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, htx]
  exact sub_le_sub_left (cgf_dual_le_cgf_norm hq hExp (q • t) hs) _

theorem goodRate_cramerRate [ProperSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    (hExp : Integrable (fun y : E ↦ Real.exp ‖y‖) ν) : GoodRate (cramerRateLaw ν) := by
  refine ⟨lowerSemicontinuous_cramerRateLaw ν, fun c hc ↦ ?_⟩
  refine (isCompact_closedBall (0 : E) (c.toReal + cgf (fun y : E ↦ ‖y‖) ν 1)).of_isClosed_subset
    ((lowerSemicontinuous_cramerRateLaw ν).isClosed_preimage c) ?_
  intro x hx
  have h := (cramerRate_ge zero_le_one (by simpa using hExp) x).trans hx
  rw [ENNReal.ofReal_le_iff_le_toReal hc, one_mul] at h
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith

end Mogulskii

