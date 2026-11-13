import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Conditioning on independent block increments

The variable `history` records the information from completed blocks. The variable
`increment` records all the increments of the next block.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace Mogulskii.SmallDeviation

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- For an independent next block, the probability of a past event and a joint survival
condition is the integral of the one-block survival probabilities over the surviving past. -/
theorem measure_independent_step {μ : Measure Ω} [IsProbabilityMeasure μ]
    {history : Ω → α} {increment : Ω → β}
    (hh : Measurable history) (hi : Measurable increment)
    (hind : IndepFun history increment μ) {past : Set α} (hpast : MeasurableSet past)
    {survive : Set (α × β)} (hsurvive : MeasurableSet survive) :
    μ {ω | history ω ∈ past ∧ (history ω, increment ω) ∈ survive} =
      ∫⁻ x in past, (μ.map increment) (Prod.mk x ⁻¹' survive) ∂(μ.map history) := by
  have hjoint : Measurable (fun ω => (history ω, increment ω)) := hh.prodMk hi
  have hset : MeasurableSet (Prod.fst ⁻¹' past ∩ survive) :=
    (measurable_fst hpast).inter hsurvive
  change μ ((fun ω => (history ω, increment ω)) ⁻¹' (Prod.fst ⁻¹' past ∩ survive)) = _
  rw [← Measure.map_apply hjoint hset, hind.map_prod_eq_prod_map_map hh.aemeasurable hi.aemeasurable,
    Measure.prod_apply hset, ← lintegral_indicator hpast]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ past
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext y
    simp [hx]
  · rw [Set.indicator_of_notMem hx]
    have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' past ∩ survive) = ∅ := by
      ext y
      simp [hx]
    rw [he, measure_empty]

/-- A uniform lower bound on one block multiplies the probability of survival so far. -/
theorem mul_measure_le_independent_step {μ : Measure Ω} [IsProbabilityMeasure μ]
    {history : Ω → α} {increment : Ω → β}
    (hh : Measurable history) (hi : Measurable increment)
    (hind : IndepFun history increment μ) {past : Set α} (hpast : MeasurableSet past)
    {survive : Set (α × β)} (hsurvive : MeasurableSet survive) {lower : ℝ≥0∞}
    (hlower : ∀ x ∈ past, lower ≤ (μ.map increment) (Prod.mk x ⁻¹' survive)) :
    lower * μ (history ⁻¹' past) ≤
      μ {ω | history ω ∈ past ∧ (history ω, increment ω) ∈ survive} := by
  rw [measure_independent_step hh hi hind hpast hsurvive, ← Measure.map_apply hh hpast,
    ← setLIntegral_const]
  exact lintegral_mono_ae ((ae_restrict_iff' hpast).2 (Eventually.of_forall hlower))

/-- A uniform upper bound on one block multiplies the probability of survival so far. -/
theorem measure_independent_step_le_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    {history : Ω → α} {increment : Ω → β}
    (hh : Measurable history) (hi : Measurable increment)
    (hind : IndepFun history increment μ) {past : Set α} (hpast : MeasurableSet past)
    {survive : Set (α × β)} (hsurvive : MeasurableSet survive) {upper : ℝ≥0∞}
    (hupper : ∀ x ∈ past, (μ.map increment) (Prod.mk x ⁻¹' survive) ≤ upper) :
    μ {ω | history ω ∈ past ∧ (history ω, increment ω) ∈ survive} ≤
      upper * μ (history ⁻¹' past) := by
  rw [measure_independent_step hh hi hind hpast hsurvive, ← Measure.map_apply hh hpast,
    ← setLIntegral_const]
  exact lintegral_mono_ae ((ae_restrict_iff' hpast).2 (Eventually.of_forall hupper))

end Mogulskii.SmallDeviation


