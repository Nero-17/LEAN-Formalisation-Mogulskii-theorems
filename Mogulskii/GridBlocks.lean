import Mogulskii.IndependentBlocks
import Mogulskii.ProductLDP
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Mogulskii

/-- Number of steps before the grid point `a / k`. -/
def gridIndex (n k a : ℕ) : ℕ := n * a / k

/-- Number of increments in the block between two successive grid points. -/
def gridCount (n k : ℕ) (a : Fin k) : ℕ :=
  gridIndex n k (a.val + 1) - gridIndex n k a.val

lemma gridIndex_mono (n k : ℕ) : Monotone (gridIndex n k) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul_left n hab)

lemma gridBlockIndex_injective (n k : ℕ) :
    Function.Injective (fun p : Σ a : Fin k, Fin (gridCount n k a) ↦
      gridIndex n k p.1.val + p.2.val) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  change gridIndex n k a.val + i.val = gridIndex n k b.val + j.val at h
  have hi := i.isLt
  have hj := j.isLt
  simp only [gridCount] at hi hj
  have hab : a.val = b.val := by
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have hmono := gridIndex_mono n k (show a.val + 1 ≤ b.val from hlt)
      omega
    · exact heq
    · have hmono := gridIndex_mono n k (show b.val + 1 ≤ a.val from hgt)
      omega
  obtain rfl : a = b := Fin.ext hab
  obtain rfl : i = j := Fin.ext (by omega)
  rfl

lemma gridIndex_rounding (n : ℕ) {k : ℕ} (hk : 0 < k) (a : ℕ) :
    (n : ℝ) * a / k - 1 < (gridIndex n k a : ℝ) ∧
      (gridIndex n k a : ℝ) ≤ (n : ℝ) * a / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmod : ((n * a) % k : ℝ) < k := by
    exact_mod_cast Nat.mod_lt (n * a) hk
  have heq : ((n * a) % k : ℝ) + (k : ℝ) * (gridIndex n k a : ℝ) = (n : ℝ) * a := by
    exact_mod_cast Nat.mod_add_div (n * a) k
  constructor
  · have hmul : (n : ℝ) * a < ((gridIndex n k a : ℝ) + 1) * k := by nlinarith
    have hdiv := (div_lt_iff₀ hkR).2 hmul
    linarith
  · exact (le_div_iff₀ hkR).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) ((n * a) % k)])

/-- Rounding the two endpoints changes the length of a block by at most one increment. -/
lemma gridCount_rounding (n : ℕ) {k : ℕ} (hk : 0 < k) (a : Fin k) :
    |(gridCount n k a : ℝ) - (n : ℝ) * (1 / k)| ≤ 1 := by
  have hm := gridIndex_mono n k (Nat.le_succ a.val)
  have hcast : (gridCount n k a : ℝ) =
      (gridIndex n k (a.val + 1) : ℝ) - (gridIndex n k a.val : ℝ) := by
    exact Nat.cast_sub hm
  rw [hcast, abs_le]
  obtain ⟨hleft₁, hleft₂⟩ := gridIndex_rounding n hk a.val
  obtain ⟨hright₁, hright₂⟩ := gridIndex_rounding n hk (a.val + 1)
  have hs : (n : ℝ) * ((a.val + 1 : ℕ) : ℝ) / k =
      (n : ℝ) * a.val / k + (n : ℝ) * (1 / k) := by
    push_cast
    ring
  rw [hs] at hright₁ hright₂
  constructor <;> linarith

section

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure E} [IsProbabilityMeasure ν]

/-- The law of the mean of `n` independent observations with law `ν`. -/
noncomputable def meanLaw (ν : Measure E) (n : ℕ) : Measure E :=
  (Measure.pi fun _ : Fin n ↦ ν).map (fun x ↦ (n : ℝ)⁻¹ • ∑ j, x j)

theorem measurable_mean (n : ℕ) :
    Measurable (fun x : Fin n → E ↦ (n : ℝ)⁻¹ • ∑ j, x j) := by
  have hc : Continuous (fun x : Fin n → E ↦ (n : ℝ)⁻¹ • ∑ j, x j) :=
    continuous_const.smul (continuous_finsetSum Finset.univ fun j _ ↦ continuous_apply j)
  exact hc.measurable

/-- The averages of the disjoint blocks between integer grid endpoints. -/
noncomputable def gridAverages (X : ℕ → Ω → E) (n k : ℕ) (ω : Ω) (a : Fin k) : E :=
  (gridCount n k a : ℝ)⁻¹ •
    ∑ j : Fin (gridCount n k a), X (gridIndex n k a.val + j.val) ω

theorem measurable_gridAverages {X : ℕ → Ω → E} (hm : ∀ i, Measurable (X i))
    (n k : ℕ) : Measurable (gridAverages X n k) := by
  apply measurable_pi_lambda
  intro a
  exact (measurable_mean (E := E) (gridCount n k a)).comp
    (measurable_pi_lambda _ fun j : Fin (gridCount n k a) ↦
      hm (gridIndex n k a.val + j.val))

omit [ProperSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
theorem gridCount_smul_gridAverages (X : ℕ → Ω → E) (n k : ℕ) (ω : Ω) (a : Fin k) :
    (gridCount n k a : ℝ) • gridAverages X n k ω a =
      ∑ i ∈ Finset.Ico (gridIndex n k a.val) (gridIndex n k (a.val + 1)), X i ω := by
  rw [Finset.sum_Ico_eq_sum_range]
  change (gridCount n k a : ℝ) • ((gridCount n k a : ℝ)⁻¹ •
    ∑ j : Fin (gridCount n k a), X (gridIndex n k a.val + j.val) ω) =
      ∑ j ∈ Finset.range (gridCount n k a), X (gridIndex n k a.val + j) ω
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ X (gridIndex n k a.val + j) ω), smul_smul]
  by_cases h : gridCount n k a = 0
  · simp [h]
  · have hcast : (gridCount n k a : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_inv_cancel₀ hcast, one_smul]

theorem map_gridAverages_eq_pi {X : ℕ → Ω → E}
    (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hν : ∀ i, μ.map (X i) = ν)
    (n k : ℕ) :
    μ.map (gridAverages X n k) = Measure.pi fun a : Fin k ↦ meanLaw ν (gridCount n k a) := by
  exact map_block_statistics_eq_pi hX hm hν
    (fun p : Σ a : Fin k, Fin (gridCount n k a) ↦ gridIndex n k p.1.val + p.2.val)
    (gridBlockIndex_injective n k)
    (fun a x ↦ (gridCount n k a : ℝ)⁻¹ • ∑ j, x j)
    (fun a ↦ measurable_mean (E := E) (gridCount n k a))

/-- The grid averages satisfy the finite-dimensional LDP as soon as the sample mean does.
Each block contributes its own rate with weight `1 / k`. -/
theorem hasExponentialBounds_gridAverages {X : ℕ → Ω → E} {I : E → ℝ≥0∞}
    (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hν : ∀ i, μ.map (X i) = ν)
    (hmean : HasExponentialBounds (meanLaw ν) I) {k : ℕ} (hk : 0 < k) :
    HasExponentialBounds (fun n ↦ μ.map (gridAverages X n k))
      (fun x ↦ ∑ a : Fin k, ENNReal.ofReal (1 / (k : ℝ)) * I (x a)) := by
  simp_rw [map_gridAverages_eq_pi hX hm hν]
  exact hasExponentialBounds_pi (P := fun _ : Fin k ↦ meanLaw ν) (I := fun _ ↦ I)
    (hProb := fun _ n ↦
      Measure.isProbabilityMeasure_map (measurable_mean (E := E) n).aemeasurable)
    (w := fun _ ↦ 1 / (k : ℝ)) (fun _ ↦ hmean)
    (fun _ ↦ one_div_pos.mpr (by exact_mod_cast hk)) (fun n ↦ gridCount n k) 1
    (fun n a ↦ gridCount_rounding n hk a)

end

end Mogulskii

