import Mogulskii.TubeRectangles
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set
open scoped Topology

namespace Mogulskii.SmallDeviation

/-- Round the equal mesh down to integer walk times. -/
noncomputable def roundedMesh (m n j : ℕ) : ℕ :=
  ⌊(n : ℝ) * ((j : ℝ) / m)⌋₊

theorem roundedMesh_zero (m n : ℕ) : roundedMesh m n 0 = 0 := by
  simp [roundedMesh]

theorem roundedMesh_end {m : ℕ} (hm : 0 < m) (n : ℕ) : roundedMesh m n m = n := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [roundedMesh, hmR]

theorem monotone_roundedMesh (m n : ℕ) : Monotone (roundedMesh m n) := by
  intro i j hij
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)) (by positivity))

private theorem le_roundedMesh_div {m n : ℕ} (hn : 0 < n) (j : ℕ) :
    ((roundedMesh m n j : ℕ) : ℝ) / n ≤ (j : ℝ) / m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_iff₀ hnR).mpr <| by
    rw [mul_comm]
    exact Nat.floor_le (by positivity)

private theorem lt_roundedMesh_div_add {m n : ℕ} (hn : 0 < n) (j : ℕ) :
    (j : ℝ) / m < (roundedMesh m n j : ℝ) / n + 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← add_div, lt_div_iff₀ hnR, mul_comm]
  exact Nat.lt_floor_add_one _

/-- Rounding by at most one walk step keeps every discrete cell inside the real
neighborhood used to construct the rectangles. -/
theorem roundedMesh_cell_bounds {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {j k : ℕ} (hj : j < m) (hk : k ≤ roundedMesh m n (j + 1) - roundedMesh m n j) :
    ((roundedMesh m n j + k : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 ∧
    |((roundedMesh m n j + k : ℕ) : ℝ) / n - (j : ℝ) / m| ≤ 2 / m := by
  have hn := hm.trans_le hmn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmono := monotone_roundedMesh m n
  have hstep : roundedMesh m n j + k ≤ roundedMesh m n (j + 1) := by
    have hmono_step : roundedMesh m n j ≤ roundedMesh m n (j + 1) :=
      hmono (Nat.le_succ j)
    exact Nat.add_le_of_le_sub' hmono_step hk
  have htotal := hstep.trans (hmono (Nat.succ_le_of_lt hj))
  rw [roundedMesh_end hm] at htotal
  constructor
  · exact ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast htotal)⟩
  · have hupper : ((roundedMesh m n j + k : ℕ) : ℝ) / n ≤ ((j + 1 : ℕ) : ℝ) / m :=
      (div_le_div_of_nonneg_right (by exact_mod_cast hstep) hnR.le).trans
        (le_roundedMesh_div hn _)
    have hcast : (roundedMesh m n j : ℝ) ≤ ((roundedMesh m n j + k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right (roundedMesh m n j) k)
    have hlower : (j : ℝ) / m < ((roundedMesh m n j + k : ℕ) : ℝ) / n + 1 / n :=
      (lt_roundedMesh_div_add hn j).trans_le (add_le_add_left
        (div_le_div_of_nonneg_right hcast hnR.le) _)
    have hinv : (1 : ℝ) / n ≤ 1 / m :=
      one_div_le_one_div_of_le hmR (by exact_mod_cast hmn)
    have hnext : ((j + 1 : ℕ) : ℝ) / m = (j : ℝ) / m + 1 / m := by
      push_cast
      rw [add_div]
    have hdouble : (2 : ℝ) / m = 1 / m + 1 / m := by rw [← add_div]; norm_num
    have hpositive : (0 : ℝ) ≤ 1 / m := by positivity
    rw [hnext] at hupper
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_roundedMesh_div {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Tendsto (fun n : ℕ => (roundedMesh m n j : ℝ) / n) atTop (𝓝 ((j : ℝ) / m)) := by
  have hconst : Tendsto (fun _ : ℕ => (j : ℝ) / m) atTop (𝓝 ((j : ℝ) / m)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun n : ℕ => (j : ℝ) / m - 1 / (n : ℝ)) atTop
      (𝓝 ((j : ℝ) / m)) := by
    simpa only [sub_zero] using hconst.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    linarith [lt_roundedMesh_div_add (m := m) hn j]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact le_roundedMesh_div hn j

theorem tendsto_roundedMesh_length_div {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Tendsto (fun n : ℕ => ((roundedMesh m n (j + 1) - roundedMesh m n j : ℕ) : ℝ) / n)
      atTop (𝓝 (1 / (m : ℝ))) := by
  have h := (tendsto_roundedMesh_div hm (j + 1)).sub (tendsto_roundedMesh_div hm j)
  have hlimit : ((j + 1 : ℕ) : ℝ) / m - (j : ℝ) / m = 1 / (m : ℝ) := by
    rw [← sub_div]
    push_cast
    ring
  rw [hlimit] at h
  refine h.congr fun n => ?_
  rw [Nat.cast_sub (monotone_roundedMesh m n (Nat.le_succ j)), sub_div]

end Mogulskii.SmallDeviation
