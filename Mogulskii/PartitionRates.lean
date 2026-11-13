import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Comparing partition rates to the integral rate

On each time interval the moving width is bounded above and below by fixed widths.
The inverse square reverses those inequalities. Integration on each interval and
addition across the partition give the comparison for the complete trajectory.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Mogulskii.SmallDeviation

theorem invSq_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ^ 2 ≤ 1 / a ^ 2 := by
  exact one_div_le_one_div_of_le (pow_pos ha 2) (pow_le_pow_left₀ ha.le hab 2)

/-- Compare a partition sum with the integral using pointwise comparisons on each cell. -/
theorem weighted_sum_le_intervalIntegral
    {m : ℕ} {t : ℕ → ℝ} {F : ℝ → ℝ} {c : ℕ → ℝ}
    (ht : ∀ j < m, t j ≤ t (j + 1))
    (hF : ∀ j < m, IntervalIntegrable F volume (t j) (t (j + 1)))
    (hc : ∀ j < m, ∀ x ∈ Icc (t j) (t (j + 1)), c j ≤ F x) :
    (∑ j ∈ Finset.range m, (t (j + 1) - t j) * c j) ≤ ∫ x in t 0..t m, F x := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hF]
  apply Finset.sum_le_sum
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have h := intervalIntegral.integral_mono_on (ht j hjm)
    (intervalIntegrable_const (c := c j)) (hF j hjm) (hc j hjm)
  simpa [intervalIntegral.integral_const] using h

/-- The reverse comparison for a partition sum and an integral. -/
theorem intervalIntegral_le_weighted_sum
    {m : ℕ} {t : ℕ → ℝ} {F : ℝ → ℝ} {c : ℕ → ℝ}
    (ht : ∀ j < m, t j ≤ t (j + 1))
    (hF : ∀ j < m, IntervalIntegrable F volume (t j) (t (j + 1)))
    (hc : ∀ j < m, ∀ x ∈ Icc (t j) (t (j + 1)), F x ≤ c j) :
    (∫ x in t 0..t m, F x) ≤ ∑ j ∈ Finset.range m, (t (j + 1) - t j) * c j := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hF]
  apply Finset.sum_le_sum
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have h := intervalIntegral.integral_mono_on (ht j hjm)
    (hF j hjm) (intervalIntegrable_const (c := c j)) (hc j hjm)
  simpa [intervalIntegral.integral_const] using h

/-- Inner and outer rectangles give lower and upper sums for the positive integral in
Mogulskii's small-deviation rate. -/
theorem sandwich_invSq_width
    {m : ℕ} {t : ℕ → ℝ} {width : ℝ → ℝ} {inner outer : ℕ → ℝ}
    (ht : ∀ j < m, t j ≤ t (j + 1))
    (hF : ∀ j < m, IntervalIntegrable (fun x => 1 / width x ^ 2) volume (t j) (t (j + 1)))
    (hinner : ∀ j < m, 0 < inner j)
    (hb : ∀ j < m, ∀ x ∈ Icc (t j) (t (j + 1)), inner j ≤ width x ∧ width x ≤ outer j) :
    (∑ j ∈ Finset.range m, (t (j + 1) - t j) * (1 / outer j ^ 2)) ≤
        (∫ x in t 0..t m, 1 / width x ^ 2) ∧
      (∫ x in t 0..t m, 1 / width x ^ 2) ≤
        ∑ j ∈ Finset.range m, (t (j + 1) - t j) * (1 / inner j ^ 2) := by
  exact ⟨weighted_sum_le_intervalIntegral ht hF fun j hj x hx =>
      invSq_anti ((hinner j hj).trans_le (hb j hj x hx).1) (hb j hj x hx).2,
    intervalIntegral_le_weighted_sum ht hF fun j hj x hx =>
      invSq_anti (hinner j hj) (hb j hj x hx).1⟩

/-- If cell values approximate the integrand uniformly on their respective cells, then
the error of their weighted sum is bounded by the mesh-independent error tolerance times
the length of the entire partition. -/
theorem abs_weighted_sum_sub_integral_le
    {m : ℕ} {t : ℕ → ℝ} {F : ℝ → ℝ} {c : ℕ → ℝ} {ε : ℝ}
    (ht : ∀ j < m, t j ≤ t (j + 1))
    (hF : ∀ j < m, IntervalIntegrable F volume (t j) (t (j + 1)))
    (hc : ∀ j < m, ∀ x ∈ Icc (t j) (t (j + 1)), |c j - F x| ≤ ε) :
    |(∑ j ∈ Finset.range m, (t (j + 1) - t j) * c j) -
      (∫ x in t 0..t m, F x)| ≤ (t m - t 0) * ε := by
  have hsum : (∑ j ∈ Finset.range m, (t (j + 1) - t j)) = t m - t 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih (fun j hj => ht j (Nat.lt_succ_of_lt hj))
        (fun j hj => hF j (Nat.lt_succ_of_lt hj))
        (fun j hj => hc j (Nat.lt_succ_of_lt hj))]
      abel
  have hlo := weighted_sum_le_intervalIntegral (c := fun j => c j - ε) ht hF
    (fun j hj x hx => sub_le_comm.mp (le_of_abs_le (hc j hj x hx)))
  have hhi := intervalIntegral_le_weighted_sum (c := fun j => c j + ε) ht hF
    (fun j hj x hx => by
      have h := neg_le_of_abs_le (hc j hj x hx)
      linarith)
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum] at hlo
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum] at hhi
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Mogulskii.SmallDeviation


