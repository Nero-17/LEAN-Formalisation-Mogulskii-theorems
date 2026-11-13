import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Mogulskii

/-- A minimum of the regularized log moment generating function forces the
tilted mean to differ from the target by twice the regularization gradient. -/
theorem regularizedTilt_mean_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {logMGF : E → ℝ} {target tilt mean : E} {ε : ℝ}
    (hmin : ∀ t, logMGF tilt - inner ℝ tilt target + ε * ‖tilt‖ ^ 2 ≤
      logMGF t - inner ℝ t target + ε * ‖t‖ ^ 2)
    (hderiv : ∀ v : E, HasDerivAt (fun s : ℝ => logMGF (tilt + s • v))
      (inner ℝ v mean) 0) :
    mean = target - (2 * ε) • tilt := by
  have hstationary (v : E) :
      inner ℝ v mean - inner ℝ v target + 2 * ε * inner ℝ v tilt = 0 := by
    let f := fun s : ℝ =>
      logMGF (tilt + s • v) - inner ℝ (tilt + s • v) target +
      ε * ‖tilt + s • v‖ ^ 2
    have hlocal : IsLocalMin f 0 := by
      apply IsMinOn.isLocalMin (s := Set.univ) _ Filter.univ_mem
      intro s _
      simpa [f] using hmin (tilt + s • v)
    have hlin : HasDerivAt (fun s : ℝ => inner ℝ (tilt + s • v) target)
        (inner ℝ v target) 0 := by
      simp only [inner_add_left, real_inner_smul_left]
      exact (hasDerivAt_mul_const (x := (0 : ℝ)) (inner ℝ v target)).const_add
        (inner ℝ tilt target)
    have hquad : HasDerivAt (fun s : ℝ => ε * ‖tilt + s • v‖ ^ 2)
        (2 * ε * inner ℝ v tilt) 0 := by
      have heq (s : ℝ) : ε * ‖tilt + s • v‖ ^ 2 =
          ε * (inner ℝ tilt tilt + (2 * inner ℝ v tilt) * s + inner ℝ v v * s ^ 2) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
        rw [real_inner_comm v tilt]
        ring
      have hsquare : HasDerivAt (fun s : ℝ => s ^ 2) 0 0 := by
        simpa using (hasDerivAt_id' (0 : ℝ)).fun_pow 2
      have hpoly := (((hasDerivAt_const_mul (x := (0 : ℝ)) (2 * inner ℝ v tilt)).const_add
        (inner ℝ tilt tilt)).add (hsquare.const_mul (inner ℝ v v))).const_mul ε
      have hcoeff : ε * ((2 * inner ℝ v tilt) + inner ℝ v v * 0) =
          2 * ε * inner ℝ v tilt := by ring
      rw [hcoeff] at hpoly
      have hpoly' : HasDerivAt
          (fun s : ℝ => ε * (inner ℝ tilt tilt + (2 * inner ℝ v tilt) * s + inner ℝ v v * s ^ 2))
          (2 * ε * inner ℝ v tilt) 0 := hpoly
      exact hpoly'.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
    exact hlocal.hasDerivAt_eq_zero (show HasDerivAt f
      (inner ℝ v mean - inner ℝ v target + 2 * ε * inner ℝ v tilt) 0 from
      ((hderiv v).sub hlin).add hquad)
  let v := mean - (target - (2 * ε) • tilt)
  have hv : inner ℝ v v = 0 := by
    have h := hstationary v
    change inner ℝ v (mean - (target - (2 * ε) • tilt)) = 0
    rw [inner_sub_right, inner_sub_right, real_inner_smul_right]
    linarith
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hv)

/-- The penalty controls how far the mean at the regularized tilt can be from
the target, even if an exact tilt for the target does not exist. -/
theorem regularizedTilt_dist_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {logMGF : E → ℝ} {target tilt mean : E} {ε cost : ℝ}
    (hε : 0 < ε) (hzero : logMGF 0 = 0)
    (hmin : ∀ t, logMGF tilt - inner ℝ tilt target + ε * ‖tilt‖ ^ 2 ≤
      logMGF t - inner ℝ t target + ε * ‖t‖ ^ 2)
    (hcost : ∀ t, inner ℝ t target - logMGF t ≤ cost)
    (hmean : mean = target - (2 * ε) • tilt) :
    dist mean target ^ 2 ≤ 4 * ε * cost := by
  have hpen : ε * ‖tilt‖ ^ 2 ≤ cost := by
    have ht := hmin 0
    simp [hzero] at ht
    linarith [hcost tilt]
  have hd : mean - target = -((2 * ε) • tilt) := by
    rw [hmean]
    abel
  rw [dist_eq_norm, hd, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ = 4 * ε * (ε * ‖tilt‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpen (by positivity)

/-- The tilt likelihood exponent at the displaced mean is at most the target cost. -/
theorem regularizedTilt_exponent_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {logMGF : E → ℝ} {target tilt mean : E} {ε cost : ℝ}
    (hε : 0 ≤ ε) (hcost : inner ℝ tilt target - logMGF tilt ≤ cost)
    (hmean : mean = target - (2 * ε) • tilt) :
    inner ℝ tilt mean - logMGF tilt ≤ cost := by
  rw [hmean, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : 0 ≤ (2 * ε) * ‖tilt‖ ^ 2 := by positivity
  linarith

/-- The quadratic penalty attains its minimum whenever the unregularized
objective is continuous and bounded below. -/
theorem exists_regularizedTilt_minimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {logMGF : E → ℝ} (hcont : Continuous logMGF)
    {target : E} {ε cost : ℝ} (hε : 0 < ε) (hc : 0 ≤ cost)
    (hzero : logMGF 0 = 0)
    (hcost : ∀ t, inner ℝ t target - logMGF t ≤ cost) :
    ∃ tilt, ∀ t, logMGF tilt - inner ℝ tilt target + ε * ‖tilt‖ ^ 2 ≤
      logMGF t - inner ℝ t target + ε * ‖t‖ ^ 2 := by
  let f := fun t => logMGF t - inner ℝ t target + ε * ‖t‖ ^ 2
  have hf : Continuous f := (hcont.sub (continuous_id.inner continuous_const)).add
    (continuous_const.mul (continuous_norm.pow 2))
  let radius := Real.sqrt (cost / ε)
  have hrad : 0 ≤ radius := Real.sqrt_nonneg _
  have hrsq : radius ^ 2 = cost / ε := Real.sq_sqrt (div_nonneg hc hε.le)
  have h0 : (0 : E) ∈ Metric.closedBall (0 : E) radius := by
    simpa [Metric.mem_closedBall] using hrad
  obtain ⟨tilt, _, hmin⟩ := (isCompact_closedBall (0 : E) radius).exists_isMinOn
    ⟨0, h0⟩ hf.continuousOn
  refine ⟨tilt, fun t => ?_⟩
  by_cases ht : t ∈ Metric.closedBall (0 : E) radius
  · exact hmin ht
  · have hn : radius < ‖t‖ := by simpa [Metric.mem_closedBall, not_le] using ht
    have hsq : radius ^ 2 < ‖t‖ ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hn) (add_pos_of_nonneg_of_pos hrad (hrad.trans_lt hn))]
    have hεsq : cost < ε * ‖t‖ ^ 2 := by
      rw [hrsq] at hsq
      simpa only [mul_comm ε (‖t‖ ^ 2)] using (div_lt_iff₀ hε).mp hsq
    have hval : 0 < f t := by dsimp [f]; linarith [hcost t]
    have hzero' : f 0 = 0 := by simp [f, hzero]
    exact (hmin h0).trans (hzero'.trans_le hval.le)

end Mogulskii

