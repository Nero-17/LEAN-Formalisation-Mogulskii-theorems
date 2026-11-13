import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Mogulskii

/-- A good rate function is lower semicontinuous and has compact finite sublevel sets. -/
structure GoodRate {E : Type*} [TopologicalSpace E] (I : E → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  isCompact_sublevel (c : ℝ≥0∞) (hc : c ≠ ⊤) : IsCompact {x | I x ≤ c}

/-- The exponential bounds for a large deviation principle at speed (n).
Finite positive prefactors do not affect the rate. -/
structure HasExponentialBounds {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (P : ℕ → Measure E) (I : E → ℝ≥0∞) : Prop where
  isGood : GoodRate I
  upper {F : Set E} (hF : IsClosed F) {r : ℝ} (hr : (r : EReal) < (⨅ x ∈ F, I x : ℝ≥0∞)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, P n F ≤ C * ENNReal.ofReal (Real.exp (-(n * r)))
  lower {x : E} {U : Set E} (hU : U ∈ 𝓝 x) {r : ℝ} (hr : (I x : EReal) < r) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(n * r))) ≤ P n U

end Mogulskii

