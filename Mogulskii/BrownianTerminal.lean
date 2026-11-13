import Mogulskii.BrownianSurvival
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Mogulskii

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

private def bridge (B : ℝ≥0 → Ω → ℝ) (t : Icc (0 : ℝ≥0) 1) (ω : Ω) : ℝ :=
  B t ω - (t.1 : ℝ) * B 1 ω

/-- The centered Brownian bridge on the unit interval is independent of the terminal value. -/
theorem indepFun_brownianBridge_endpoint (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) :
    IndepFun (fun ω t ↦ bridge B t ω) (B 1) P := by
  classical
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hG : IsGaussianProcess (Sum.elim (bridge B) (fun _ : Unit ↦ B 1)) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨⟩)
    · exact ⟨{t.1, 1},
        { toFun f := f ⟨t.1, by simp⟩ - (t.1 : ℝ) * f ⟨1, by simp⟩
          map_add' f g := by simp; ring
          map_smul' c f := by simp; ring }, fun ω ↦ rfl⟩
    · exact ⟨{1},
        { toFun f := f ⟨1, by simp⟩
          map_add' f g := by simp
          map_smul' c f := by simp }, fun ω ↦ rfl⟩
  have hcov (t : Icc (0 : ℝ≥0) 1) : cov[bridge B t, B 1; P] = 0 := by
    unfold bridge
    rw [covariance_fun_sub_left, covariance_const_mul_left, hB.covariance_eval t.1 1,
      hB.covariance_eval 1 1, min_eq_left t.2.2, min_self]
    · simp
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval t.1).memLp_two
    · change MemLp ((t.1 : ℝ) • B 1) 2 P
      exact (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two.const_smul (t.1 : ℝ)
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  have h := hG.indepFun_of_covariance_eq_zero
    (fun t ↦ ((hm t.1).sub ((hm 1).const_mul (t.1 : ℝ))).aemeasurable)
    (fun _ ↦ (hm 1).aemeasurable) (fun t _ ↦ hcov t)
  simpa [Function.comp_def] using h.comp (φ := id) (ψ := fun f : Unit → ℝ ↦ f ())
    measurable_id (measurable_pi_apply ())

private def bridgeGridEvent (radius : ℝ) : Set (Icc (0 : ℝ≥0) 1 → ℝ) :=
  ⋂ n : ℕ, ⋂ k : ℕ, ⋂ hk : k ≤ n + 1,
    {f | f ⟨uniformGrid 1 n k, zero_le,
      (monotone_uniformGrid 1 n hk).trans_eq (uniformGrid_last 1 n)⟩ ∈ Icc (-radius) radius}

private theorem measurableSet_bridgeGridEvent (radius : ℝ) :
    MeasurableSet (bridgeGridEvent radius) :=
  MeasurableSet.iInter (fun _ ↦ MeasurableSet.iInter (fun _ ↦
    MeasurableSet.iInter (fun _ ↦ measurable_pi_apply _ measurableSet_Icc)))

private theorem mem_bridgeGridEvent_iff {ω : Ω} (hc : Continuous (B · ω)) (radius : ℝ) :
    (fun t ↦ bridge B t ω) ∈ bridgeGridEvent radius ↔
      ∀ t ≤ (1 : ℝ≥0), B t ω - (t : ℝ) * B 1 ω ∈ Icc (-radius) radius := by
  have hcontinuous : Continuous (fun t : ℝ≥0 ↦ B t ω - (t : ℝ) * B 1 ω) :=
    hc.sub (continuous_subtype_val.mul continuous_const)
  simp only [bridgeGridEvent, mem_iInter, mem_setOf_eq, bridge]
  constructor
  · intro h t ht
    by_contra hn
    obtain ⟨n, k, hk, he⟩ :=
      (eventually_exists_uniformGrid_exit hcontinuous ⟨t, ht, hn⟩).exists
    exact he (h n k hk)
  · intro h n k hk
    exact h _ ((monotone_uniformGrid 1 n hk).trans_eq (uniformGrid_last 1 n))

private theorem gaussianReal_one_mass_lower {a b length : ℝ} (hab : a ≤ b)
    (hlength : 0 < length) :
    ∃ c > 0, ∀ {u v : ℝ}, a ≤ u → u + length ≤ v → v ≤ b →
      c ≤ (gaussianReal 0 1).real (Icc u v) := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    fun_prop
  obtain ⟨z, hz, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont.continuousOn
  have hpos := gaussianPDFReal_pos 0 1 z one_ne_zero
  refine ⟨gaussianPDFReal 0 1 z * length, mul_pos hpos hlength, ?_⟩
  intro u v hu huv hv
  have huv' : u ≤ v := by linarith
  have hp : 0 ≤ ∫ y in Icc u v, gaussianPDFReal 0 1 y :=
    integral_nonneg (gaussianPDFReal_nonneg 0 1)
  change _ ≤ (gaussianReal 0 1 (Icc u v)).toReal
  rw [gaussianReal_apply_eq_integral 0 (v := 1) one_ne_zero, ENNReal.toReal_ofReal hp]
  calc
    _ ≤ gaussianPDFReal 0 1 z * (v - u) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos.le
    _ = ∫ _ in Icc u v, gaussianPDFReal 0 1 z := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr huv'), mul_comm]
    _ ≤ _ := by
      refine integral_mono_ae (integrable_const _) (integrable_gaussianPDFReal 0 1).restrict ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun y hy ↦
        hmin ⟨hu.trans hy.1, hy.2.trans hv⟩)

/-- Uniform positive chance of traversing a unit interval of time and landing in a
prescribed interior interval, for starting points in a compact interior interval. -/
theorem uniform_brownian_terminal_transition
    {left right lower upper finishLower finishUpper : ℝ}
    (hleft : left < lower) (hle : lower ≤ upper) (hright : upper < right)
    (hfinishLeft : left < finishLower) (hfinishWidth : finishLower < finishUpper)
    (hfinishRight : finishUpper < right) :
    ∃ c > 0, ∀ {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}, IsBrownianReal B P →
      (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) →
      ∀ x ∈ Icc lower upper,
        c ≤ P.real (intervalSurvival (fun t ω ↦ x + B t ω) left right 1 ∩
          {ω | x + B 1 ω ∈ Icc finishLower finishUpper}) := by
  let radius := min (min (lower - left) (right - upper))
    (min (finishLower - left) (right - finishUpper))
  have hradius : 0 < radius := by
    dsimp [radius]
    simp only [lt_min_iff]
    exact ⟨⟨sub_pos.mpr hleft, sub_pos.mpr hright⟩,
      ⟨sub_pos.mpr hfinishLeft, sub_pos.mpr hfinishRight⟩⟩
  have hL : radius ≤ lower - left := (min_le_left ..).trans (min_le_left ..)
  have hR : radius ≤ right - upper := (min_le_left ..).trans (min_le_right ..)
  have hfL : radius ≤ finishLower - left := (min_le_right ..).trans (min_le_left ..)
  have hfR : radius ≤ right - finishUpper := (min_le_right ..).trans (min_le_right ..)
  obtain ⟨cBridge, hcBridge, hBridge⟩ := uniform_closed_survival_lower (Ω := Ω)
    (left := -(radius / 2)) (right := radius / 2) (lower := 0) (upper := 0)
    (by linarith) le_rfl (by linarith)
  let bridgeBound := cBridge * Real.exp (-intervalEigenvalue 1 (-(radius / 2)) (radius / 2) * 1)
  have hBridgePos : 0 < bridgeBound := mul_pos hcBridge (Real.exp_pos _)
  obtain ⟨cEnd, hcEnd, hEnd⟩ :=
    gaussianReal_one_mass_lower (a := finishLower - upper) (b := finishUpper - lower)
      (length := finishUpper - finishLower) (by linarith) (sub_pos.mpr hfinishWidth)
  refine ⟨bridgeBound * cEnd, mul_pos hBridgePos hcEnd, ?_⟩
  intro B P hB hm hc x hx
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hBridgeProb : bridgeBound ≤ P.real ((fun ω t ↦ bridge B t ω) ⁻¹' bridgeGridEvent radius) := by
    have hcontain : intervalSurvival B (-(radius / 2)) (radius / 2) 1 ⊆
        (fun ω t ↦ bridge B t ω) ⁻¹' bridgeGridEvent radius := by
      intro ω hω
      apply (mem_bridgeGridEvent_iff (hc ω) radius).2
      intro t ht
      have ht₀ : (0 : ℝ) ≤ t := t.2
      have ht₁ : (t : ℝ) ≤ 1 := by exact_mod_cast ht
      have hnow := hω t ht
      have hend := hω 1 le_rfl
      have hnow' : |B t ω| ≤ radius / 2 := abs_le.mpr hnow
      have hend' : |B 1 ω| ≤ radius / 2 := abs_le.mpr hend
      apply abs_le.mp
      calc
        |B t ω - (t : ℝ) * B 1 ω| ≤ |B t ω| + |(t : ℝ) * B 1 ω| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (B t ω) (-((t : ℝ) * B 1 ω))
        _ ≤ radius / 2 + radius / 2 := by
          rw [abs_mul, abs_of_nonneg ht₀]
          exact add_le_add hnow' ((mul_le_of_le_one_left (abs_nonneg _) ht₁).trans hend')
        _ = radius := by ring
    have hsmall : bridgeBound ≤ P.real (intervalSurvival B (-(radius / 2)) (radius / 2) 1) := by
      simpa only [bridgeBound, zero_add, NNReal.coe_one] using
        hBridge B P hB hm hc 0 ⟨le_rfl, le_rfl⟩ 1
    calc
      _ ≤ P.real (intervalSurvival B (-(radius / 2)) (radius / 2) 1) := hsmall
      _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcontain)
  let terminal := Icc (finishLower - x) (finishUpper - x)
  let good := ((fun ω t ↦ bridge B t ω) ⁻¹' bridgeGridEvent radius) ∩ (B 1 ⁻¹' terminal)
  have hind := IndepFun.measure_inter_preimage_eq_mul
    (indepFun_brownianBridge_endpoint hB.toIsPreBrownianReal hm) (bridgeGridEvent radius) terminal
    (measurableSet_bridgeGridEvent radius) measurableSet_Icc
  have hgauss : P (B 1 ⁻¹' terminal) = gaussianReal 0 1 terminal := by
    rw [← (hB.hasLaw_eval 1).map_eq, Measure.map_apply (hm 1) measurableSet_Icc]
  have hterminal : cEnd ≤ P.real (B 1 ⁻¹' terminal) := by
    change cEnd ≤ (P (B 1 ⁻¹' terminal)).toReal
    rw [hgauss]
    exact hEnd (by linarith [hx.2]) (le_of_eq (by ring)) (by linarith [hx.1])
  have hcontain : good ⊆ intervalSurvival (fun t ω ↦ x + B t ω) left right 1 ∩
      {ω | x + B 1 ω ∈ Icc finishLower finishUpper} := by
    rintro ω ⟨hω, hend⟩
    have hend' : x + B 1 ω ∈ Icc finishLower finishUpper := by
      change finishLower - x ≤ B 1 ω ∧ B 1 ω ≤ finishUpper - x at hend
      exact ⟨by linarith [hend.1], by linarith [hend.2]⟩
    refine ⟨fun t ht ↦ ?_, hend'⟩
    have hb := (mem_bridgeGridEvent_iff (hc ω) radius).1 hω t ht
    have ht₀ : (0 : ℝ) ≤ t := t.2
    have ht₁ : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    change left ≤ x + B t ω ∧ x + B t ω ≤ right
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht₁)
        (show 0 ≤ x - (left + radius) by linarith [hx.1]),
        mul_nonneg ht₀ (show 0 ≤ x + B 1 ω - (left + radius) by linarith [hend'.1]), hb.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht₁)
        (show 0 ≤ right - radius - x by linarith [hx.2]),
        mul_nonneg ht₀ (show 0 ≤ right - radius - (x + B 1 ω) by linarith [hend'.2]), hb.2]
  calc
    _ ≤ P.real good := by
      change _ ≤ (P good).toReal
      rw [show P good = _ from hind, ENNReal.toReal_mul]
      exact mul_le_mul hBridgeProb hterminal hcEnd.le ENNReal.toReal_nonneg
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcontain)

end Mogulskii
