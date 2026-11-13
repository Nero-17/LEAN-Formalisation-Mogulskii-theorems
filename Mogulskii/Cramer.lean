import Mogulskii.CramerUpper
import Mogulskii.CramerTilt
import Mogulskii.RegularizedTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {ν : Measure E} [IsProbabilityMeasure ν]

/-- The moment generating function written using the real inner product. -/
noncomputable def innerMGF (ν : Measure E) (t : E) : ℝ :=
  ∫ x, Real.exp (inner ℝ t x) ∂ν

theorem continuous_innerMGF
    (hExp : ∀ q ≥ 0, Integrable (fun y : E => Real.exp (q * ‖y‖)) ν) :
    Continuous (innerMGF ν) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  unfold innerMGF
  apply continuousAt_of_dominated (bound := fun x => Real.exp ((‖t‖ + 1) * ‖x‖))
  · exact Eventually.of_forall fun s =>
      (Real.continuous_exp.comp (continuous_const.inner continuous_id) :
        Continuous (fun x : E => Real.exp (inner ℝ s x))).measurable.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with s hs
    have hsNorm : ‖s‖ ≤ ‖t‖ + 1 := by
      have hnorm := norm_le_norm_add_norm_sub' s t
      rw [Metric.mem_ball, dist_eq_norm] at hs
      linarith
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
      exact (real_inner_le_norm s x).trans (mul_le_mul_of_nonneg_right hsNorm (norm_nonneg _))
  · exact hExp _ (by positivity)
  · exact Eventually.of_forall fun x =>
      (Real.continuous_exp.comp (continuous_id.inner continuous_const)).continuousAt

theorem innerMGF_pos
    (hExp : ∀ q ≥ 0, Integrable (fun y : E => Real.exp (q * ‖y‖)) ν) (t : E) :
    0 < innerMGF ν t := by
  simpa only [innerMGF, mgf, one_mul, innerSL_apply_apply] using
    (mgf_pos (integrable_exp_dual hExp (innerSL ℝ t)))

theorem continuous_log_innerMGF
    (hExp : ∀ q ≥ 0, Integrable (fun y : E => Real.exp (q * ‖y‖)) ν) :
    Continuous (fun t => Real.log (innerMGF ν t)) :=
  (continuous_innerMGF hExp).log (fun t => (innerMGF_pos hExp t).ne')

theorem hasDerivAt_log_innerMGF [SecondCountableTopology E]
    (hExp : ∀ q ≥ 0, Integrable (fun y : E => Real.exp (q * ‖y‖)) ν) (t v : E) :
    HasDerivAt (fun s : ℝ => Real.log (innerMGF ν (t + s • v)))
      (inner ℝ v (∫ y, y ∂(ν.tilted (innerSL ℝ t)))) 0 := by
  let F (s : ℝ) (x : E) := Real.exp (inner ℝ (t + s • v) x)
  let F' (s : ℝ) (x : E) := Real.exp (inner ℝ (t + s • v) x) * inner ℝ v x
  have hFm (s : ℝ) : Continuous (F s) :=
    Real.continuous_exp.comp (continuous_const.inner continuous_id)
  have hFi : Integrable (F 0) ν := by
    simpa [F, innerSL_apply_apply] using integrable_exp_dual hExp (innerSL ℝ t)
  have hF'm : Continuous (F' 0) := (hFm 0).mul (continuous_const.inner continuous_id)
  have hbound : ∀ x : E, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖F' s x‖ ≤ ‖v‖ * Real.exp ((‖t‖ + ‖v‖ + 1) * ‖x‖) := by
    intro x s hs
    have hs' : |s| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs.le
    have hnorm : ‖t + s • v‖ ≤ ‖t‖ + ‖v‖ := calc
      _ ≤ ‖t‖ + ‖s • v‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) hs') _
    dsimp only [F']
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp ((‖t‖ + ‖v‖) * ‖x‖) * (‖v‖ * ‖x‖) := by
        exact mul_le_mul (Real.exp_le_exp.mpr ((real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))) (norm_inner_le_norm _ _)
          (norm_nonneg _) (Real.exp_nonneg _)
      _ ≤ ‖v‖ * Real.exp ((‖t‖ + ‖v‖ + 1) * ‖x‖) := by
        rw [add_mul (‖t‖ + ‖v‖) 1, one_mul, Real.exp_add]
        have hx : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
        calc
          _ ≤ Real.exp ((‖t‖ + ‖v‖) * ‖x‖) * (‖v‖ * Real.exp ‖x‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
              (Real.exp_nonneg _)
          _ = _ := by ring
  have hdiff (x : E) (s : ℝ) : HasDerivAt (F · x) (F' s x) s := by
    dsimp [F, F']
    simp only [inner_add_left, real_inner_smul_left]
    exact ((hasDerivAt_mul_const (x := s) (inner ℝ v x)).const_add (inner ℝ t x)).exp
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    (Eventually.of_forall fun s => (hFm s).measurable.aestronglyMeasurable) hFi
    hF'm.measurable.aestronglyMeasurable (Eventually.of_forall hbound)
    ((hExp _ (by positivity)).const_mul ‖v‖)
    (Eventually.of_forall fun x s _ => hdiff x s)).2
  have hvalue : (∫ x, F 0 x ∂ν) = innerMGF ν t := by simp [F, innerMGF]
  have hnonzero : (∫ x, F 0 x ∂ν) ≠ 0 := by
    rw [hvalue]
    exact (innerMGF_pos hExp t).ne'
  have hd := hi.log hnonzero
  have heq : (∫ x, F' 0 x ∂ν) / (∫ x, F 0 x ∂ν) =
      inner ℝ v (∫ y, y ∂(ν.tilted (innerSL ℝ t))) := by
    have hinner : (∫ y, inner ℝ v y ∂(ν.tilted (innerSL ℝ t))) =
        inner ℝ v (∫ y, y ∂(ν.tilted (innerSL ℝ t))) :=
      integral_inner (integrable_id_tilted hExp (innerSL ℝ t)) v
    rw [← hinner]
    have ht : (fun x => (1 : ℝ) * innerSL ℝ t x) = innerSL ℝ t := by
      funext x
      simp
    rw [← ht, integral_tilted_mul_eq_mgf]
    simp only [F', F, zero_smul, add_zero, smul_eq_mul, mgf, one_mul, innerSL_apply_apply]
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [heq] at hd
  simpa only [F, innerMGF] using hd

/-- The upper bound and the lower bound at regularized tilted means give
the finite-dimensional Cramér principle. -/
theorem hasExponentialBounds_meanLaw [ProperSpace E]
    (hExp : ∀ q ≥ 0, Integrable (fun y : E => Real.exp (q * ‖y‖)) ν) :
    HasExponentialBounds (meanLaw ν) (cramerRateLaw ν) := by
  refine ⟨goodRate_cramerRate (by simpa using hExp 1 zero_le_one), ?_, ?_⟩
  · intro F hF r hr
    exact cramer_upper hExp hF hr
  intro x U hU r hr
  have hxFinite : cramerRateLaw ν x ≠ ⊤ := by
    intro hx
    simp [hx] at hr
  let cost := (cramerRateLaw ν x).toReal
  have hcostNonneg : 0 ≤ cost := ENNReal.toReal_nonneg
  have hcostLt : cost < r := by
    have he : ENNReal.ofReal cost = cramerRateLaw ν x := ENNReal.ofReal_toReal hxFinite
    rw [← he, EReal.coe_ennreal_ofReal, max_eq_left hcostNonneg] at hr
    exact EReal.coe_lt_coe_iff.mp hr
  have hlog (t : E) : cgf (innerSL ℝ t) ν 1 = Real.log (innerMGF ν t) := by
    simp [cgf, mgf, innerMGF, innerSL_apply_apply]
  have hcost (t : E) : inner ℝ t x - Real.log (innerMGF ν t) ≤ cost := by
    apply (ENNReal.ofReal_le_iff_le_toReal hxFinite).mp
    rw [← hlog t]
    exact le_iSup (fun s : E →L[ℝ] ℝ => ENNReal.ofReal (s x - cgf s ν 1)) (innerSL ℝ t)
  obtain ⟨δ, hδ, V, hV, hVsub, hball⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∃ V : Set E, IsOpen V ∧ V ⊆ U ∧ Metric.ball x δ ⊆ V := by
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
    exact ⟨δ, hδ, V, hV, hVU, hball⟩
  let ε := δ ^ 2 / (8 * (cost + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hzero : Real.log (innerMGF ν (0 : E)) = 0 := by simp [innerMGF]
  obtain ⟨t, ht⟩ := exists_regularizedTilt_minimizer (continuous_log_innerMGF hExp)
    hε hcostNonneg hzero hcost
  have hmean := regularizedTilt_mean_eq (logMGF := fun z => Real.log (innerMGF ν z))
    (target := x) (tilt := t) (mean := ∫ y, y ∂(ν.tilted (innerSL ℝ t)))
    ht (hasDerivAt_log_innerMGF hExp t)
  have hdist := regularizedTilt_dist_le hε hzero ht hcost hmean
  have hsmall : 4 * ε * cost < δ ^ 2 := by
    dsimp [ε]
    have hden : 0 < 8 * (cost + 1) := by positivity
    rw [show 4 * (δ ^ 2 / (8 * (cost + 1))) * cost =
      (4 * δ ^ 2 * cost) / (8 * (cost + 1)) by ring]
    apply (div_lt_iff₀ hden).mpr
    have hδsq : 0 < δ ^ 2 := by positivity
    nlinarith [mul_nonneg hδsq.le hcostNonneg]
  have hy : (∫ y, y ∂(ν.tilted (innerSL ℝ t))) ∈ V := by
    apply hball
    rw [Metric.mem_ball]
    have hh := hdist.trans_lt hsmall
    by_contra! hlarge
    have hpositive := hδ.trans_le hlarge
    nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) (add_nonneg hpositive.le hδ.le)]
  have hexponent := regularizedTilt_exponent_le
    (logMGF := fun z => Real.log (innerMGF ν z)) hε.le (hcost t) hmean
  have hr' : innerSL ℝ t (∫ y, y ∂(ν.tilted (innerSL ℝ t))) -
      cgf (innerSL ℝ t) ν 1 < r := by
    rw [hlog, innerSL_apply_apply]
    exact hexponent.trans_lt hcostLt
  refine ⟨1 / 2, by norm_num, (cramer_lower_at_tilted_mean hExp (innerSL ℝ t) hV hy hr').mono ?_⟩
  intro n hn
  exact hn.trans (measure_mono hVsub)

end Mogulskii
