/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Probability.DonskerWanted
/-- Clamps a real to `[0,1]`. -/
noncomputable def donskerClamp (x : ℝ) : ℝ :=
  min (max x 0) 1

/-- Weight `t ↦ clamp(n·t - i)` for the polygonal interpolation. -/
noncomputable def donskerWeight (n i : ℕ) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  donskerClamp ((n : ℝ) * t.val - (i : ℝ))

/-- Bundled continuous version of `donskerWeight` in `C([0,1],ℝ)`. -/
noncomputable def donskerWeightCM (n i : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) where
  toFun := donskerWeight n i
  continuous_toFun := by
    unfold donskerWeight donskerClamp
    have h_val : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (t.val : ℝ)) :=
      continuous_subtype_val
    have h_lin : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (n : ℝ) * t.val - (i : ℝ)) := by
      fun_prop
    have h_clamp : Continuous (fun x : ℝ => min (max x 0) 1) := by
      fun_prop
    exact h_clamp.comp h_lin

private lemma donskerWeight_eq_one_of_lt_floor (n i : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (hi : i < Nat.floor ((n : ℝ) * t.1)) : donskerWeight n i t = 1 := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hi' : (i : ℝ) + 1 ≤ (n : ℝ) * t.1 := by
    calc
      (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ (Nat.floor ((n : ℝ) * t.1) : ℝ) := by exact_mod_cast hi
      _ ≤ (n : ℝ) * t.1 := Nat.floor_le ha0
  have hweight : 1 ≤ (n : ℝ) * t.1 - (i : ℝ) := by linarith
  simp [donskerWeight, donskerClamp, max_eq_left (le_trans zero_le_one hweight),
    min_eq_right hweight]

private lemma donskerWeight_floor (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    donskerWeight n (Nat.floor ((n : ℝ) * t.1)) t =
      (n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1) := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hfrac0 := Nat.zero_le_self_sub_floor ha0
  have hfrac1 := (Nat.self_sub_floor_lt_one ((n : ℝ) * t.1)).le
  simp [donskerWeight, donskerClamp, max_eq_left hfrac0, min_eq_left hfrac1]

private lemma donskerWeight_eq_zero_of_floor_lt (n i : ℕ) (t : Set.Icc (0 : ℝ) 1)
    (hi : Nat.floor ((n : ℝ) * t.1) < i) : donskerWeight n i t = 0 := by
  have ha0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg (Nat.cast_nonneg n) t.2.1
  have hi' : (n : ℝ) * t.1 < (i : ℝ) := (Nat.floor_lt ha0).mp hi
  have hweight : (n : ℝ) * t.1 - (i : ℝ) ≤ 0 := by linarith
  simp [donskerWeight, donskerClamp, max_eq_right hweight]

private lemma donsker_weighted_sum_eq {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) :
    (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) =
      (∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) +
        if Nat.floor ((n : ℝ) * t.1) < n then
          X (Nat.floor ((n : ℝ) * t.1)) ω *
            ((n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1))
        else 0 := by
  let m := Nat.floor ((n : ℝ) * t.1)
  have ha_le : (n : ℝ) * t.1 ≤ (n : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg n)
  have hm_le : m ≤ n := Nat.floor_le_of_le ha_le
  have hprefix : (∑ i ∈ Finset.range m, X i ω * donskerWeight n i t) =
      ∑ i ∈ Finset.range m, X i ω := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [donskerWeight_eq_one_of_lt_floor n i t (Finset.mem_range.mp hi)]
    simp
  by_cases hm_lt : m < n
  · have htail : (∑ i ∈ Finset.Ico (m + 1) n, X i ω * donskerWeight n i t) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [donskerWeight_eq_zero_of_floor_lt n i t]
      · simp
      · exact (Nat.succ_le_iff.mp (Finset.mem_Ico.mp hi).1)
    rw [← Finset.sum_range_add_sum_Ico (fun i => X i ω * donskerWeight n i t) hm_le,
      Finset.sum_eq_sum_Ico_succ_bot hm_lt, hprefix, donskerWeight_floor, htail]
    simp [m, hm_lt]
  · have hm_eq : m = n := le_antisymm hm_le (not_lt.mp hm_lt)
    change (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) =
      (∑ i ∈ Finset.range m, X i ω) +
        if m < n then X m ω * ((n : ℝ) * t.1 - m) else 0
    simp only [hm_lt, ↓reduceIte, add_zero]
    simpa [hm_eq] using hprefix

/-- Polygonal normalized partial-sum process as a `C([0,1],ℝ)`-valued variable. -/
noncomputable def donskerProcess {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  if n = 0 then 0
  else
    let sqrtInv : ℝ := (Real.sqrt (n : ℝ))⁻¹
    sqrtInv • (Finset.sum (Finset.range n) fun i => (X i ω) • donskerWeightCM n i)

/-- Explicit partial-sum interpolation formula for `donskerProcess`. -/
public theorem donskerProcess_apply_eq {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) (hn : n ≠ 0) :
    donskerProcess n X ω t =
      ((∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) +
        if Nat.floor ((n : ℝ) * t.1) < n then
          X (Nat.floor ((n : ℝ) * t.1)) ω *
            ((n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1))
        else 0) / Real.sqrt (n : ℝ) := by
  simp only [donskerProcess, hn, ↓reduceIte]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply]
  change (Real.sqrt (n : ℝ))⁻¹ *
      (∑ i ∈ Finset.range n, X i ω * donskerWeight n i t) = _
  rw [donsker_weighted_sum_eq]
  ring

/-- Multiplying each increment by a constant multiplies the polygonal path by that constant. -/
theorem donskerProcess_mul {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) (c : ℝ) :
    donskerProcess n (fun i u => c * X i u) ω = c • donskerProcess n X ω := by
  by_cases hn : n = 0
  · simp [donskerProcess, hn]
  · ext t
    simp only [donskerProcess, hn, ↓reduceIte, ContinuousMap.smul_apply,
      ContinuousMap.sum_apply, smul_eq_mul]
    simp_rw [mul_assoc c]
    rw [← Finset.mul_sum, mul_left_comm]

end MathlibExt.Probability.DonskerWanted

