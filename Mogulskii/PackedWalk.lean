import Mogulskii.WalkTube

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Mogulskii.SmallDeviation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The increments in a finite block starting at time `m`. -/
def blockVector (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) (i : Fin n) : ℝ :=
  X (m + i.val) ω

/-- Extend the finite vector of increments by zero. -/
def blockExtension {n : ℕ} (v : Fin n → ℝ) (i : ℕ) (_ : Unit) : ℝ :=
  if h : i < n then v ⟨i, h⟩ else 0

theorem measurable_blockVector {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (m n : ℕ) : Measurable (blockVector X m n) :=
  measurable_pi_lambda _ fun i => hX (m + i.val)

theorem measurable_blockExtension (n i : ℕ) :
    Measurable (fun v : Fin n → ℝ => blockExtension v i ()) := by
  by_cases hi : i < n
  · simpa [blockExtension, hi] using
      (measurable_pi_apply (⟨i, hi⟩ : Fin n) : Measurable (fun v : Fin n → ℝ => v ⟨i, hi⟩))
  · simp [blockExtension, hi]

theorem measurable_walk_blockExtension (n k : ℕ) :
    Measurable (fun v : Fin n → ℝ => walk (blockExtension v) k ()) :=
  Finset.measurable_sum _ fun i _ => measurable_blockExtension n i

theorem walk_blockExtension_blockVector (X : ℕ → Ω → ℝ) (m n k : ℕ) (ω : Ω)
    (hk : k ≤ n) :
    walk (blockExtension (blockVector X m n ω)) k () =
      walk (fun i => X (m + i)) k ω := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [blockExtension, blockVector, (Finset.mem_range.mp hi).trans_le hk]

theorem indepFun_blockVector {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (m n : ℕ) :
    IndepFun (blockVector X 0 m) (blockVector X m n) μ := by
  have hdisj : Disjoint (Finset.range m) (Finset.Ico m (m + n)) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_range, Finset.mem_Ico]
    exact fun i hi hj => (Nat.not_le_of_lt hi) hj.1
  let history (v : (i : Finset.range m) → ℝ) (i : Fin m) : ℝ :=
    v ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  let future (v : (i : Finset.Ico m (m + n)) → ℝ) (i : Fin n) : ℝ :=
    v ⟨m + i.val, Finset.mem_Ico.mpr ⟨Nat.le_add_right m i.val,
      Nat.add_lt_add_left i.isLt m⟩⟩
  have h := (hind.indepFun_finset _ _ hdisj hX).comp
    (φ := history) (ψ := future)
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  change IndepFun (fun ω (i : Fin m) => X (0 + i.val) ω)
    (fun ω (i : Fin n) => X (m + i.val) ω) μ
  simpa [history, future, Function.comp_def] using h

theorem map_blockVector_shift {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (m n : ℕ) :
    μ.map (blockVector X m n) = μ.map (blockVector X 0 n) := by
  have shifted (j : ℕ) : iIndepFun (fun i : Fin n => X (j + i.val)) μ :=
    hind.precomp fun i k h => Fin.ext (Nat.add_left_cancel h)
  unfold blockVector
  rw [(shifted m).map_fun_eq_pi_map (fun i => (hX _).aemeasurable),
    (shifted 0).map_fun_eq_pi_map (fun i => (hX _).aemeasurable)]
  congr 1
  funext i
  exact (hid (m + i.val)).map_eq.trans (hid (0 + i.val)).map_eq.symm

end Mogulskii.SmallDeviation



