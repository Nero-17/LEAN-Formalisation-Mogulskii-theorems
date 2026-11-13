import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Random-walk block geometry
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Mogulskii.SmallDeviation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The position after `n` increments, with increments indexed starting at zero. -/
def walk (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

theorem walk_add (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    walk X (m + n) ω = walk X m ω + walk (fun i => X (m + i)) n ω := by
  simp only [walk, Finset.sum_range_add]

theorem measurable_walk {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (walk X n) := by
  exact Finset.measurable_sum _ (fun i _ => hX i)

/-- The discrete path remains inside a prescribed time-dependent interval. -/
def tubeEvent (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (lower upper : ℕ → ℝ) : Set Ω :=
  {ω | ∀ k ≤ n, x + walk X k ω ∈ Icc (lower k) (upper k)}

theorem measurableSet_tubeEvent {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (n : ℕ) (x : ℝ) (lower upper : ℕ → ℝ) :
    MeasurableSet (tubeEvent X n x lower upper) := by
  rw [show tubeEvent X n x lower upper =
    ⋂ k : ℕ, ⋂ _ : k ≤ n,
      (fun ω => x + walk X k ω) ⁻¹' Icc (lower k) (upper k) by
        ext ω
        simp [tubeEvent]]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    (measurable_const.add (measurable_walk hX k)) measurableSet_Icc

/-- Staying in a tube up to time `m+n` is equivalent to surviving the first segment and
then surviving the shifted segment from the position at time `m`. -/
theorem mem_tubeEvent_add_iff (X : ℕ → Ω → ℝ) (m n : ℕ) (x : ℝ)
    (lower upper : ℕ → ℝ) (ω : Ω) :
    ω ∈ tubeEvent X (m + n) x lower upper ↔
      ω ∈ tubeEvent X m x lower upper ∧
        ω ∈ tubeEvent (fun i => X (m + i)) n (x + walk X m ω)
          (fun j => lower (m + j)) (fun j => upper (m + j)) := by
  constructor
  · intro h
    refine ⟨fun k hk => h k (by omega), ?_⟩
    intro j hj
    have h' := h (m + j) (by omega)
    rwa [walk_add, ← add_assoc] at h'
  · rintro ⟨hfirst, hsecond⟩ k hk
    by_cases hkm : k ≤ m
    · exact hfirst k hkm
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hkm))
      rw [walk_add, ← add_assoc]
      exact hsecond j (by omega)

end Mogulskii.SmallDeviation


