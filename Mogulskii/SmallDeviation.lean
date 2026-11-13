import Mogulskii.Statements
import Mogulskii.BrownianBlockTransfer
import Mogulskii.BrownianExistence
import Mogulskii.RepeatBlocks
import MathlibExt.Probability.ContinuousMapBorel
import MathlibExt.Probability.Donsker
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
open MathlibExt.Probability.DonskerWanted

namespace Mogulskii

/-- Mogulskii's moving-tube small-deviation theorem for centered, independent and identically
distributed real increments of positive finite variance. -/
theorem smallDeviationStatement : SmallDeviationStatement := by
  intro Ω _ μ _ X a f g hX hind hid hL2 hmean hvar ha haTop hasqrt hf hg hfg hf0 hg0
  let σ := Real.sqrt (variance (X 0) μ)
  have hσ : 0 < σ := Real.sqrt_pos.2 hvar
  have hσsq : σ ^ 2 = variance (X 0) μ := Real.sq_sqrt hvar.le
  let Z : ℕ → Ω → ℝ := fun i ω => X i ω / σ
  let b : ℕ → ℝ := fun n => a n / σ
  have hmDiv : Measurable (fun x : ℝ => x / σ) := measurable_id.div_const σ
  have hZ (i : ℕ) : Measurable (Z i) := hmDiv.comp (hX i)
  have hindZ : iIndepFun Z μ := hind.comp (fun _ x => x / σ) (fun _ => hmDiv)
  have hidZ (i : ℕ) : IdentDistrib (Z i) (Z 0) μ μ := (hid i).comp hmDiv
  have hnorm (i : ℕ) : Z i = fun ω => σ⁻¹ * X i ω := by
    funext ω
    simp [Z, div_eq_mul_inv, mul_comm]
  have hZL2 : MemLp (Z 0) 2 μ := by
    rw [hnorm]
    exact hL2.const_mul σ⁻¹
  have hZmean : (∫ ω, Z 0 ω ∂μ) = 0 := by
    rw [hnorm, integral_const_mul, hmean, mul_zero]
  have hZvar : variance (Z 0) μ = 1 := by
    rw [hnorm, variance_const_mul, ← hσsq, ← mul_pow, inv_mul_cancel₀ hσ.ne', one_pow]
  have hb (n : ℕ) : 0 < b n := div_pos (ha n) hσ
  have hbTop : Tendsto b atTop atTop := haTop.atTop_div_const hσ
  have hbSqTop : Tendsto (fun n => b n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hbTop
  have hbsqrt : Tendsto (fun n : ℕ => b n / Real.sqrt n) atTop (𝓝 0) := by
    have hscale (n : ℕ) : a n / Real.sqrt n / σ = b n / Real.sqrt n :=
      div_right_comm _ _ _
    simpa only [hscale, zero_div] using hasqrt.div_const σ
  have hbSq : Tendsto (fun n : ℕ => b n ^ 2 / n) atTop (𝓝 0) := by
    simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), zero_pow (by decide : 2 ≠ 0)]
      using hbsqrt.pow 2
  obtain ⟨Q, B, hB, hmB, hcB⟩ := exists_continuous_standard_brownian
  haveI : IsProbabilityMeasure Q := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨Y, hY, hD⟩ := donsker_invariance_principle Z hZ hindZ hidZ
    (hZL2.integrable (by norm_num)) hZL2 hZmean hZvar B hB
  have hLower := SmallDeviation.singleBlockLower_of_donsker hb hbTop hD hY hB hmB hcB
  have hUpper := SmallDeviation.singleBlockUpper_of_donsker hb hbTop hD hY hB hmB hcB
  obtain ⟨hRectLower, hRectUpper⟩ := SmallDeviation.rectangularBounds_of_singleBlockBounds
    μ Z hZ hindZ hidZ b hb hbSqTop hbSq (Real.pi ^ 2 / 2) hLower hUpper
  have hbound := SmallDeviation.movingTube_exponential_of_rectangular μ Z hZ hindZ hidZ b hb
    hf hg hfg hf0 hg0 (Real.pi ^ 2 / 2) (by positivity) hRectLower hRectUpper
  have hevent (n : ℕ) :
      SmallDeviation.tubeEvent Z n 0
        (fun k => b n * f ((k : ℝ) / n)) (fun k => b n * g ((k : ℝ) / n)) =
          tubeEvent X a f g n := by
    ext ω
    simp only [SmallDeviation.tubeEvent, SmallDeviation.walk, Mogulskii.tubeEvent,
      partialSum, mem_setOf_eq, mem_Icc, zero_add, Z, b, ← Finset.sum_div,
      div_mul_eq_mul_div]
    exact forall_congr' fun k => forall_congr' fun _ => and_congr
      (div_le_div_iff_of_pos_right hσ) (div_le_div_iff_of_pos_right hσ)
  let rate := Real.pi ^ 2 / 2 * ∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2
  have hrate :
      Real.pi ^ 2 * variance (X 0) μ / 2 * (∫ t in (0 : ℝ)..1, (g t - f t)⁻¹ ^ 2) =
        rate * variance (X 0) μ := by
    dsimp only [rate]
    simp only [inv_pow, one_div]
    ring
  have hspeed (n : ℕ) : (n : ℝ) / b n ^ 2 = variance (X 0) μ * ((n : ℝ) / a n ^ 2) := by
    rw [show b n = a n / σ from rfl, div_pow, div_div_eq_mul_div, hσsq]
    ring
  dsimp only
  intro ε hε
  filter_upwards [hbound (ε / variance (X 0) μ) (div_pos hε hvar)] with n hn
  change ENNReal.ofReal (Real.exp (-(rate + ε / variance (X 0) μ) * ((n : ℝ) / b n ^ 2))) ≤
      μ (SmallDeviation.tubeEvent Z n 0
        (fun k => b n * f ((k : ℝ) / n)) (fun k => b n * g ((k : ℝ) / n))) ∧
    μ (SmallDeviation.tubeEvent Z n 0
        (fun k => b n * f ((k : ℝ) / n)) (fun k => b n * g ((k : ℝ) / n))) ≤
      ENNReal.ofReal (Real.exp (-(rate - ε / variance (X 0) μ) * ((n : ℝ) / b n ^ 2))) at hn
  rw [hevent, hspeed] at hn
  rw [hrate]
  have hexp (e : ℝ) :
      -(rate + e / variance (X 0) μ) * (variance (X 0) μ * ((n : ℝ) / a n ^ 2)) =
        -(rate * variance (X 0) μ + e) * ((n : ℝ) / a n ^ 2) := by
    rw [← mul_assoc, neg_mul, add_mul, div_mul_cancel₀ _ hvar.ne']
  have hexpUpper :
      -(rate - ε / variance (X 0) μ) * (variance (X 0) μ * ((n : ℝ) / a n ^ 2)) =
        -(rate * variance (X 0) μ - ε) * ((n : ℝ) / a n ^ 2) := by
    rw [← mul_assoc, neg_mul, sub_mul, div_mul_cancel₀ _ hvar.ne']
  refine ⟨?_, ?_⟩
  · simpa only [hexp ε] using hn.1
  · simpa only [hexpUpper] using hn.2

/-- The moving-tube asymptotic in normalized log-probability form. -/
theorem smallDeviation_log_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (f g : ℝ → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ) (hL2 : MemLp (X 0) 2 μ)
    (hmean : (∫ ω, X 0 ω ∂μ) = 0) (hvar : 0 < variance (X 0) μ)
    (ha : ∀ n, 0 < a n) (haTop : Tendsto a atTop atTop)
    (hasqrt : Tendsto (fun n : ℕ => a n / Real.sqrt n) atTop (𝓝 0))
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f t < g t) (hf0 : f 0 < 0) (hg0 : 0 < g 0) :
    Tendsto (fun n : ℕ => a n ^ 2 / n * Real.log (μ.real (tubeEvent X a f g n))) atTop
      (𝓝 (-(Real.pi ^ 2 * variance (X 0) μ / 2 *
        ∫ t in (0 : ℝ)..1, (g t - f t)⁻¹ ^ 2))) := by
  let rate := Real.pi ^ 2 * variance (X 0) μ / 2 *
    ∫ t in (0 : ℝ)..1, (g t - f t)⁻¹ ^ 2
  have hb := smallDeviationStatement μ X a f g hX hind hid hL2 hmean hvar ha haTop
    hasqrt hf hg hfg hf0 hg0
  have hlog (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, -(rate + ε) ≤ a n ^ 2 / n * Real.log (μ.real (tubeEvent X a f g n)) ∧
        a n ^ 2 / n * Real.log (μ.real (tubeEvent X a f g n)) ≤ -(rate - ε) := by
    filter_upwards [hb ε hε, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hapos : 0 < a n ^ 2 := pow_pos (ha n) _
    have hfinite := measure_ne_top μ (tubeEvent X a f g n)
    have hpositive : 0 < μ.real (tubeEvent X a f g n) :=
      ENNReal.toReal_pos (ne_of_gt ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le hn.1)) hfinite
    have hleft := ENNReal.toReal_mono hfinite hn.1
    have hright := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hleft hright
    have hleftLog := Real.log_le_log (Real.exp_pos _) hleft
    have hrightLog := Real.log_le_log hpositive hright
    rw [Real.log_exp] at hleftLog hrightLog
    have hscale : a n ^ 2 / (n : ℝ) * ((n : ℝ) / a n ^ 2) = 1 := by
      field_simp [hnreal.ne', (ha n).ne']
    have hmul (r : ℝ) : a n ^ 2 / (n : ℝ) * (r * ((n : ℝ) / a n ^ 2)) = r := by
      rw [mul_left_comm, hscale, mul_one]
    constructor
    · simpa only [rate, Measure.real, hmul] using
        mul_le_mul_of_nonneg_left hleftLog (div_nonneg hapos.le hnreal.le)
    · simpa only [rate, Measure.real, hmul] using
        mul_le_mul_of_nonneg_left hrightLog (div_nonneg hapos.le hnreal.le)
  change Tendsto _ atTop (𝓝 (-rate))
  rw [tendsto_order]
  constructor
  · intro x hx
    filter_upwards [hlog ((-rate - x) / 2) (by linarith)] with n hn
    exact (show x < -(rate + (-rate - x) / 2) by linarith).trans_le hn.1
  · intro x hx
    filter_upwards [hlog ((x + rate) / 2) (by linarith)] with n hn
    exact hn.2.trans_lt (show -(rate - (x + rate) / 2) < x by linarith)

end Mogulskii
