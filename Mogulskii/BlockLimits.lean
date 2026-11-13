import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

/-!
# Passing from block estimates to a logarithmic limit
-/

open Filter
open scoped Topology BigOperators

namespace Mogulskii.SmallDeviation

/-- A fixed finite collection of blocks contributes the sum of its scaled logarithmic
probabilities. -/
theorem tendsto_scaled_log_prod {ι : Type*} {s : Finset ι}
    {scale : ℕ → ℝ} {prob : ι → ℕ → ℝ} {rate : ι → ℝ}
    (hpos : ∀ᶠ n in atTop, ∀ i ∈ s, 0 < prob i n)
    (hlim : ∀ i ∈ s, Tendsto (fun n => scale n * Real.log (prob i n)) atTop (𝓝 (rate i))) :
    Tendsto (fun n => scale n * Real.log (∏ i ∈ s, prob i n)) atTop
      (𝓝 (∑ i ∈ s, rate i)) := by
  have hsum : Tendsto (fun n => ∑ i ∈ s, scale n * Real.log (prob i n)) atTop
      (𝓝 (∑ i ∈ s, rate i)) := tendsto_finsetSum s hlim
  refine hsum.congr' ?_
  filter_upwards [hpos] with n hn
  rw [Real.log_prod (fun i hi => (hn i hi).ne'), Finset.mul_sum]

/-- Inner and outer approximations may each be indexed by a partition parameter. If both
limiting rates approach the same value, their bounds give the desired limit. -/
theorem tendsto_of_approximating_bounds {q : ℕ → ℝ}
    {lower upper : ℕ → ℕ → ℝ} {lowerRate upperRate : ℕ → ℝ} {rate : ℝ}
    (hlo : ∀ m, Tendsto (lower m) atTop (𝓝 (lowerRate m)))
    (hhi : ∀ m, Tendsto (upper m) atTop (𝓝 (upperRate m)))
    (hbound : ∀ m, ∀ᶠ n in atTop, lower m n ≤ q n ∧ q n ≤ upper m n)
    (hloRate : Tendsto lowerRate atTop (𝓝 rate))
    (hhiRate : Tendsto upperRate atTop (𝓝 rate)) :
    Tendsto q atTop (𝓝 rate) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hloRate).1 a ha).exists
    filter_upwards [(tendsto_order.1 (hlo m)).1 a hm, hbound m] with n hn hb
    exact hn.trans_le hb.1
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hhiRate).2 a ha).exists
    filter_upwards [(tendsto_order.1 (hhi m)).2 a hm, hbound m] with n hn hb
    exact hb.2.trans_lt hn

/-- Probability bounds for each fixed inner and outer partition suffice to identify the
scaled logarithmic limit for the full event. -/
theorem tendsto_scaled_log_of_block_bounds
    {scale q : ℕ → ℝ} {blockCount : ℕ → ℕ}
    {lower upper : ℕ → ℕ → ℕ → ℝ} {lowerRate upperRate : ℕ → ℕ → ℝ} {rate : ℝ}
    (hscale : ∀ᶠ n in atTop, 0 ≤ scale n)
    (hlower : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ Finset.range (blockCount m), 0 < lower m i n)
    (hupper : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ Finset.range (blockCount m), 0 < upper m i n)
    (hlo : ∀ m i, i ∈ Finset.range (blockCount m) →
      Tendsto (fun n => scale n * Real.log (lower m i n)) atTop (𝓝 (lowerRate m i)))
    (hhi : ∀ m i, i ∈ Finset.range (blockCount m) →
      Tendsto (fun n => scale n * Real.log (upper m i n)) atTop (𝓝 (upperRate m i)))
    (hbound : ∀ m, ∀ᶠ n in atTop,
      (∏ i ∈ Finset.range (blockCount m), lower m i n) ≤ q n ∧
      q n ≤ ∏ i ∈ Finset.range (blockCount m), upper m i n)
    (hloRate : Tendsto (fun m => ∑ i ∈ Finset.range (blockCount m), lowerRate m i) atTop (𝓝 rate))
    (hhiRate : Tendsto (fun m => ∑ i ∈ Finset.range (blockCount m), upperRate m i) atTop (𝓝 rate)) :
    Tendsto (fun n => scale n * Real.log (q n)) atTop (𝓝 rate) := by
  refine tendsto_of_approximating_bounds
    (fun m => tendsto_scaled_log_prod (hlower m) (hlo m))
    (fun m => tendsto_scaled_log_prod (hupper m) (hhi m)) ?_ hloRate hhiRate
  intro m
  filter_upwards [hscale, hlower m, hupper m, hbound m] with n hs hl hu hb
  have hp : 0 < ∏ i ∈ Finset.range (blockCount m), lower m i n := Finset.prod_pos hl
  have hq : 0 < q n := hp.trans_le hb.1
  have hr : 0 < ∏ i ∈ Finset.range (blockCount m), upper m i n := Finset.prod_pos hu
  exact ⟨mul_le_mul_of_nonneg_left ((Real.log_le_log_iff hp hq).2 hb.1) hs,
    mul_le_mul_of_nonneg_left ((Real.log_le_log_iff hq hr).2 hb.2) hs⟩

/-- Repetition counts need only converge after rescaling. This is the form used when the
common short block has length approximately `T * aₙ²`. -/
theorem tendsto_scaled_log_pow {scale prob : ℕ → ℝ} {count : ℕ → ℕ}
    {countRate probLimit : ℝ}
    (hcount : Tendsto (fun n => scale n * (count n : ℝ)) atTop (𝓝 countRate))
    (hprob : Tendsto prob atTop (𝓝 probLimit)) (hpos : 0 < probLimit) :
    Tendsto (fun n => scale n * Real.log (prob n ^ count n)) atTop
      (𝓝 (countRate * Real.log probLimit)) := by
  have hlog : Tendsto (fun n => Real.log (prob n)) atTop (𝓝 (Real.log probLimit)) :=
    (Real.continuousAt_log hpos.ne').tendsto.comp hprob
  refine (hcount.mul hlog).congr ?_
  intro n
  rw [Real.log_pow, mul_assoc]

/-- A fixed number of transition blocks with probabilities bounded away from zero does
not contribute to the scaled logarithmic rate. -/
theorem tendsto_scaled_log_of_uniform_bounds {scale prob : ℕ → ℝ} {c : ℝ}
    (hscale : Tendsto scale atTop (𝓝 0))
    (hs : ∀ᶠ n in atTop, 0 ≤ scale n)
    (hc : 0 < c)
    (hp : ∀ᶠ n in atTop, c ≤ prob n ∧ prob n ≤ 1) :
    Tendsto (fun n => scale n * Real.log (prob n)) atTop (𝓝 0) := by
  have hlo : Tendsto (fun n => scale n * Real.log c) atTop (𝓝 0) := by
    simpa using hscale.mul_const (Real.log c)
  refine tendsto_of_approximating_bounds (lower := fun _ n => scale n * Real.log c)
    (upper := fun _ _ => 0) (lowerRate := fun _ => 0) (upperRate := fun _ => 0)
    (fun _ => hlo) (fun _ => tendsto_const_nhds) ?_ tendsto_const_nhds tendsto_const_nhds
  intro m
  filter_upwards [hs, hp] with n hn hb
  have hpos := hc.trans_le hb.1
  refine ⟨mul_le_mul_of_nonneg_left ((Real.log_le_log_iff hc hpos).2 hb.1) hn, ?_⟩
  have hlog : Real.log (prob n) ≤ 0 := by
    simpa using (Real.log_le_log_iff hpos zero_lt_one).2 hb.2
  exact mul_nonpos_of_nonneg_of_nonpos hn hlog

end Mogulskii.SmallDeviation



