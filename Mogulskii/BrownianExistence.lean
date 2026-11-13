import BrownianMotion.Gaussian.BrownianMotion

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Mogulskii

/-- A standard Brownian motion with measurable evaluations and continuous paths on
the Gaussian projective-limit probability space. -/
theorem exists_continuous_standard_brownian :
    ∃ (P : Measure (ℝ≥0 → ℝ)) (B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
      IsBrownianReal B P ∧ (∀ t, Measurable (B t)) ∧ (∀ ω, Continuous (B · ω)) :=
  ⟨gaussianLimit, brownian, isBrownianReal_brownian, measurable_brownian, continuous_brownian⟩

end Mogulskii
