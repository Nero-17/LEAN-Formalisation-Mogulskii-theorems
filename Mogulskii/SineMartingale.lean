import Mogulskii.StoppedGrid
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Mogulskii

private noncomputable def phase (frequency x : ℝ) : ℂ :=
  Complex.exp ((↑(frequency * x) : ℂ) * Complex.I)

private theorem continuous_phase (frequency : ℝ) : Continuous (phase frequency) := by
  unfold phase
  fun_prop

@[simp] private theorem norm_phase (frequency x : ℝ) : ‖phase frequency x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phase_add (frequency x y : ℝ) :
    phase frequency (x + y) = phase frequency x * phase frequency y := by
  simp [phase, mul_add, add_mul, Complex.exp_add]

private theorem integral_phase_gaussian (frequency : ℝ) (t : ℝ≥0) :
    (∫ x, phase frequency x ∂gaussianReal 0 t) =
      ↑(Real.exp (-(frequency ^ 2 / 2 * (t : ℝ)))) := by
  have h : (∫ x, phase frequency x ∂gaussianReal 0 t) =
      charFun (gaussianReal 0 t) frequency := by
    rw [charFun_apply_real]
    simp [phase]
  rw [h, charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

theorem setIntegral_brownianSine_eq (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (frequency shift : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[(Filtration.natural B
      (fun u ↦ (hm u).stronglyMeasurable)) s] A) :
    (∫ ω in A, brownianSine frequency shift s (B s ω) ∂P) =
      ∫ ω in A, brownianSine frequency shift t (B t ω) ∂P := by
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let past := fun ω (u : Iic s) ↦ B u ω
  let increment := fun ω ↦ B t ω - B s ω
  have htime : s + (t - s) = t := add_tsub_cancel_of_le hst
  have hindep : IndepFun increment past P := by
    simpa [increment, past, Function.comp_def, htime] using
      (hB.indepFun_shift s).comp (ψ := id)
        (φ := fun f : ℝ≥0 → ℝ ↦ f (t - s)) (measurable_pi_apply _) measurable_id
  have hlaw : HasLaw increment (gaussianReal 0 (t - s)) P := by
    simpa [increment, htime] using (hB.shift s).hasLaw_eval (t - s)
  rw [Filtration.natural_eq_comap] at hA
  obtain ⟨C, hC, rfl⟩ := hA
  have hmpast : Measurable past := measurable_pi_lambda _ (fun u ↦ hm u)
  have hmincrement : Measurable increment := (hm t).sub (hm s)
  let pastPhase : (Iic s → ℝ) → ℂ :=
    C.indicator (fun path ↦ phase frequency (shift + path ⟨s, self_mem_Iic⟩))
  have hmPastPhase : Measurable pastPhase :=
    ((continuous_phase frequency).measurable.comp
      (measurable_const.add (measurable_pi_apply _))).indicator hC
  have hprod := hindep.symm.integral_fun_comp_mul_comp hmpast.aemeasurable
    hmincrement.aemeasurable hmPastPhase.aestronglyMeasurable
    (continuous_phase frequency).aestronglyMeasurable
  have hmoment : (∫ ω, phase frequency (increment ω) ∂P) =
      ↑(Real.exp (-(frequency ^ 2 / 2 * ((t - s : ℝ≥0) : ℝ)))) :=
    (hlaw.integral_comp (continuous_phase frequency).aestronglyMeasurable).trans
      (integral_phase_gaussian frequency (t - s))
  have hpiece : (fun ω ↦ pastPhase (past ω) * phase frequency (increment ω)) =
      (past ⁻¹' C).indicator (fun ω ↦ phase frequency (shift + B t ω)) := by
    funext ω
    by_cases hω : past ω ∈ C
    · have hω' : ω ∈ past ⁻¹' C := hω
      simp only [pastPhase, indicator_of_mem hω, indicator_of_mem hω', ← phase_add]
      change phase frequency (shift + B s ω + (B t ω - B s ω)) =
        phase frequency (shift + B t ω)
      exact congrArg (phase frequency) (by ring)
    · have hω' : ω ∉ past ⁻¹' C := hω
      simp only [pastPhase, indicator_of_notMem hω, indicator_of_notMem hω', zero_mul]
  have hpastPiece : (fun ω ↦ pastPhase (past ω)) =
      (past ⁻¹' C).indicator (fun ω ↦ phase frequency (shift + B s ω)) := by
    funext ω
    by_cases hω : past ω ∈ C
    · have hω' : ω ∈ past ⁻¹' C := hω
      simp only [pastPhase, indicator_of_mem hω, indicator_of_mem hω', past, Subtype.coe_mk]
    · have hω' : ω ∉ past ⁻¹' C := hω
      simp only [pastPhase, indicator_of_notMem hω, indicator_of_notMem hω']
  have hC' : MeasurableSet (past ⁻¹' C) := hmpast hC
  rw [hpiece, hpastPiece, hmoment] at hprod
  simp only [integral_indicator hC'] at hprod
  have hIm (u : ℝ≥0) :
      (∫ ω in past ⁻¹' C, Real.sin (frequency * (shift + B u ω)) ∂P) =
        (∫ ω in past ⁻¹' C, phase frequency (shift + B u ω) ∂P).im := by
    have hInt : Integrable (fun ω ↦ phase frequency (shift + B u ω))
        (P.restrict (past ⁻¹' C)) := Integrable.of_bound
      (((continuous_phase frequency).measurable.comp
        (measurable_const.add (hm u))).aestronglyMeasurable) 1
      (ae_of_all _ (fun _ ↦ by simp))
    simpa [phase, Complex.imCLM_apply, Complex.exp_im, Complex.mul_I_re, Complex.mul_I_im] using
      Complex.imCLM.integral_comp_comm hInt
  have hreal := congrArg Complex.im hprod
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add,
    ← hIm] at hreal
  have hfactor :
      Real.exp (frequency ^ 2 / 2 * (t : ℝ)) *
        Real.exp (-(frequency ^ 2 / 2 * ((t - s : ℝ≥0) : ℝ))) =
      Real.exp (frequency ^ 2 / 2 * (s : ℝ)) := by
    rw [← Real.exp_add, NNReal.coe_sub hst]
    congr 1
    ring
  simp only [brownianSine, integral_const_mul]
  rw [hreal, mul_comm _ (Real.exp (-(frequency ^ 2 / 2 * ((t - s : ℝ≥0) : ℝ)))),
    ← mul_assoc, hfactor]

/-- Observe the Brownian natural filtration on a monotone time grid. -/
def brownianGridFiltration (hm : ∀ t, Measurable (B t)) {grid : ℕ → ℝ≥0}
    (hgrid : Monotone grid) : Filtration ℕ mΩ where
  seq i := Filtration.natural B (fun u ↦ (hm u).stronglyMeasurable) (grid i)
  mono' _ _ h := (Filtration.natural B (fun u ↦ (hm u).stronglyMeasurable)).mono (hgrid h)
  le' i := (Filtration.natural B (fun u ↦ (hm u).stronglyMeasurable)).le (grid i)

/-- The sine eigenfunction with its compensating exponential on any ordered time grid. -/
theorem martingale_brownianSine_grid (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (frequency shift : ℝ)
    {grid : ℕ → ℝ≥0} (hgrid : Monotone grid) :
    Martingale (fun i ω ↦ brownianSine frequency shift (grid i) (B (grid i) ω))
      (brownianGridFiltration hm hgrid) P := by
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmeas (u : ℝ≥0) :
      StronglyMeasurable[(Filtration.natural B (fun u ↦ (hm u).stronglyMeasurable)) u]
        (fun ω ↦ brownianSine frequency shift u (B u ω)) := by
    have hc : Continuous (brownianSine frequency shift u) := by unfold brownianSine; fun_prop
    exact (hc.measurable.comp (Filtration.stronglyAdapted_natural
      (fun u ↦ (hm u).stronglyMeasurable) u).measurable).stronglyMeasurable
  apply martingale_of_setIntegral_eq_succ (fun i ↦ hmeas (grid i))
  · intro i
    refine Integrable.of_bound ((hmeas (grid i)).aestronglyMeasurable.mono
      ((Filtration.natural B (fun u ↦ (hm u).stronglyMeasurable)).le _))
      (Real.exp (frequency ^ 2 / 2 * (grid i : ℝ))) ?_
    refine ae_of_all _ (fun ω ↦ ?_)
    rw [brownianSine, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  · intro i A hA
    exact setIntegral_brownianSine_eq hB hm frequency shift (hgrid (Nat.le_succ i)) hA

end Mogulskii

