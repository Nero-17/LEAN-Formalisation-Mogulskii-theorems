import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace Mogulskii.SmallDeviation

/-- A partition of `total` into `count` blocks, with any extra steps placed in the first blocks. -/
def balancedCut (total count k : ℕ) : ℕ :=
  k * (total / count) + min k (total % count)

theorem balancedCut_zero (total count : ℕ) : balancedCut total count 0 = 0 := by
  simp [balancedCut]

theorem balancedCut_end (total count : ℕ) (hc : 0 < count) :
    balancedCut total count count = total := by
  rw [balancedCut, min_eq_right (Nat.mod_lt _ hc).le]
  exact Nat.div_add_mod total count

theorem balancedCut_mono (total count : ℕ) : Monotone (balancedCut total count) :=
  fun _ _ h => Nat.add_le_add (Nat.mul_le_mul_right _ h) (min_le_min_right _ h)

theorem balancedCut_succ (total count k : ℕ) :
    balancedCut total count (k + 1) - balancedCut total count k =
      if k < total % count then total / count + 1 else total / count := by
  unfold balancedCut
  rw [Nat.add_mul, Nat.one_mul]
  generalize total / count = q
  generalize total % count = r
  split_ifs with hk
  · rw [min_eq_left (Nat.succ_le_of_lt hk), min_eq_left hk.le]
    omega
  · have hk' := Nat.le_of_not_gt hk
    rw [min_eq_right hk', min_eq_right (hk'.trans (Nat.le_succ k))]
    omega

/-- Rounding down on a diverging scale preserves a finite positive limit. -/
theorem tendsto_natFloor_div_scale {scale x : ℕ → ℝ} {limit : ℝ}
    (hscale : Tendsto scale atTop atTop)
    (hx : ∀ᶠ n in atTop, 0 ≤ x n)
    (hlim : Tendsto (fun n => x n / scale n) atTop (𝓝 limit)) :
    Tendsto (fun n => (⌊x n⌋₊ : ℝ) / scale n) atTop (𝓝 limit) := by
  have hsmall : Tendsto (fun n => (scale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  have hl : Tendsto (fun n => x n / scale n - (scale n)⁻¹) atTop (𝓝 limit) := by
    simpa using hlim.sub hsmall
  have hpos : ∀ᶠ n in atTop, 0 < scale n :=
    (tendsto_atTop.1 hscale 1).mono fun _ h => zero_lt_one.trans_le h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hlim
  · filter_upwards [hpos] with n hn
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have h : x n - 1 ≤ (⌊x n⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (x n)]
    have hm := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hn.le)
    simpa only [sub_mul, one_mul] using hm
  · filter_upwards [hx, hpos] with n hxn hn
    exact div_le_div_of_nonneg_right (Nat.floor_le hxn) hn.le

/-- Both possible integer block lengths have the same diffusive limit. -/
theorem tendsto_balanced_length {scale : ℕ → ℝ} {total count : ℕ → ℕ} {T : ℝ}
    (hscale : Tendsto scale atTop atTop)
    (hmean : Tendsto (fun n => ((total n : ℝ) / count n) / scale n) atTop (𝓝 T)) :
    (Tendsto (fun n => ((total n / count n : ℕ) : ℝ) / scale n) atTop (𝓝 T)) ∧
      (Tendsto (fun n => ((total n / count n + 1 : ℕ) : ℝ) / scale n) atTop (𝓝 T)) := by
  have h₀ : Tendsto (fun n => (⌊(total n : ℝ) / count n⌋₊ : ℝ) / scale n) atTop (𝓝 T) :=
    tendsto_natFloor_div_scale hscale (.of_forall fun _ => by positivity) hmean
  have hfloor : ∀ n : ℕ, ⌊(total n : ℝ) / count n⌋₊ = total n / count n := by
    intro n
    exact Nat.floor_div_eq_div (total n) (count n)
  have h₁ : Tendsto (fun n => ((total n / count n : ℕ) : ℝ) / scale n) atTop (𝓝 T) := by
    simpa only [hfloor] using h₀
  refine ⟨h₁, ?_⟩
  have hinv : Tendsto (fun n => (scale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero] using h₁.add hinv

/-- Rounding the number of subblocks changes it by at most one and does not
affect the diffusive length of either integer subblock size. -/
theorem tendsto_balanced_at_diffusive_scale {scale : ℕ → ℝ} {total : ℕ → ℕ} {T : ℝ}
    (hscale : Tendsto scale atTop atTop) (hT : 0 < T)
    (hquot : Tendsto (fun n => (total n : ℝ) / scale n) atTop atTop) :
    let count := fun n => ⌊((total n : ℝ) / scale n) / T⌋₊
    (∀ᶠ n in atTop, 0 < count n) ∧
    Tendsto (fun n => ((total n / count n : ℕ) : ℝ) / scale n) atTop (𝓝 T) ∧
    Tendsto (fun n => ((total n / count n + 1 : ℕ) : ℝ) / scale n) atTop (𝓝 T) := by
  let count := fun n => ⌊((total n : ℝ) / scale n) / T⌋₊
  change (∀ᶠ n in atTop, 0 < count n) ∧ _ ∧ _
  have hlarge : Tendsto (fun n => ((total n : ℝ) / scale n) / T) atTop atTop :=
    hquot.atTop_div_const hT
  have hcount : ∀ᶠ n in atTop, 0 < count n := by
    filter_upwards [tendsto_atTop.1 hlarge 1] with n hn
    change 0 < ⌊((total n : ℝ) / scale n) / T⌋₊
    exact Nat.floor_pos.mpr hn
  have hratio : Tendsto (fun n => (count n : ℝ) / (((total n : ℝ) / scale n) / T))
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp hlarge
  have hmean : Tendsto (fun n => ((total n : ℝ) / count n) / scale n) atTop (𝓝 T) := by
    have h := (tendsto_const_nhds (x := T)).div hratio (by norm_num)
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [hcount, tendsto_atTop.1 hscale 1, tendsto_atTop.1 hlarge 1] with n hcn hsn hln
    have hcn' : (count n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcn)
    have hsn' : scale n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hsn)
    have hln' : ((total n : ℝ) / scale n) / T ≠ 0 := ne_of_gt (zero_lt_one.trans_le hln)
    change T / ((count n : ℝ) / (((total n : ℝ) / scale n) / T)) =
      ((total n : ℝ) / count n) / scale n
    have ht' : (total n : ℝ) ≠ 0 := by
      intro he
      exact hln' (by simp [he])
    field_simp [hcn', hsn', ht', hT.ne'] <;> ring
  exact ⟨hcount, tendsto_balanced_length hscale hmean⟩

/-- The block count, multiplied by the scaled length of a single block,
converges to the fraction of time spent in the original interval. -/
theorem tendsto_balanced_count_mul {scale : ℕ → ℝ} {total : ℕ → ℕ} {T δ : ℝ}
    (hT : 0 < T) (hquot : Tendsto (fun n => (total n : ℝ) / scale n) atTop atTop)
    (htotal : Tendsto (fun n => (total n : ℝ) / n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ =>
      (⌊((total n : ℝ) / scale n) / T⌋₊ : ℝ) * T * (scale n / n)) atTop (𝓝 δ) := by
  have hlarge : Tendsto (fun n => ((total n : ℝ) / scale n) / T) atTop atTop :=
    hquot.atTop_div_const hT
  have hratio := tendsto_nat_floor_div_atTop.comp hlarge
  have h := hratio.mul htotal
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [tendsto_atTop.1 hlarge 1, eventually_ge_atTop (1 : ℕ)] with n hn hn'
  have hden : ((total n : ℝ) / scale n) / T ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have htotal' : (total n : ℝ) ≠ 0 := by
    intro he
    apply hden
    rw [he, zero_div, zero_div]
  have hscale' : scale n ≠ 0 := by
    intro he
    apply hden
    rw [he, div_zero, zero_div]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (⌊((total n : ℝ) / scale n) / T⌋₊ : ℝ) /
    (((total n : ℝ) / scale n) / T) * ((total n : ℝ) / n) =
    (⌊((total n : ℝ) / scale n) / T⌋₊ : ℝ) * T * (scale n / n)
  generalize (⌊((total n : ℝ) / scale n) / T⌋₊ : ℝ) = count
  field_simp [htotal', hscale', hn0, hT.ne'] <;> ring

end Mogulskii.SmallDeviation
