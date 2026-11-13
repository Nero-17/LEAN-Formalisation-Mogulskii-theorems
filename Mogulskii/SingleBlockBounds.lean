import Mogulskii.PartitionTube
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Mogulskii.SmallDeviation

/-- Fixed large-time bounds for individual diffusive blocks. -/
def SingleBlockLower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (l u startLo startHi endLo endHi : ℝ),
    l < startLo → startLo ≤ startHi → startHi < u →
    l < endLo → endLo < endHi → endHi < u →
    ∀ η > 0, ∀ᶠ T : ℝ in atTop, ∀ length : ℕ → ℕ,
      Tendsto (fun n => (length n : ℝ) / a n ^ 2) atTop (𝓝 T) →
      ∀ᶠ n in atTop, ∀ y ∈ Icc (a n * startLo) (a n * startHi),
        ENNReal.ofReal (Real.exp (-(C / (u - l) ^ 2 + η) * T)) ≤
          μ (endpointTube X (length n) y (fun _ => a n * l) (fun _ => a n * u)
            (Icc (a n * endLo) (a n * endHi)))

def SingleBlockUpper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (l u : ℝ), l < u → ∀ η > 0, ∀ᶠ T : ℝ in atTop, ∀ length : ℕ → ℕ,
    Tendsto (fun n => (length n : ℝ) / a n ^ 2) atTop (𝓝 T) →
    ∀ᶠ n in atTop, ∀ y : ℝ,
      μ (tubeEvent X (length n) y (fun _ => a n * l) (fun _ => a n * u)) ≤
        ENNReal.ofReal (Real.exp (-(C / (u - l) ^ 2 - η) * T))

end Mogulskii.SmallDeviation


