import Mogulskii.PartitionTube
import Mogulskii.RoundedMesh
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Mogulskii.SmallDeviation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform lower estimates on fixed rectangles for all lengths proportional to the walk length. -/
def RectangularLower (μ : Measure Ω) (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (length : ℕ → ℕ) (δ l u startLo startHi endLo endHi : ℝ),
    0 < δ → l < startLo → startLo ≤ startHi → startHi < u →
    l < endLo → endLo < endHi → endHi < u →
    Tendsto (fun n => (length n : ℝ) / n) atTop (𝓝 δ) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ y ∈ Icc (a n * startLo) (a n * startHi),
      ENNReal.ofReal (Real.exp (-(δ * (C / (u - l) ^ 2) + ε) * ((n : ℝ) / a n ^ 2))) ≤
        μ (endpointTube X (length n) y (fun _ => a n * l) (fun _ => a n * u)
          (Icc (a n * endLo) (a n * endHi)))

/-- Uniform upper estimates on fixed rectangles, allowing every starting position. -/
def RectangularUpper (μ : Measure Ω) (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (length : ℕ → ℕ) (δ l u : ℝ),
    0 < δ → l < u →
    Tendsto (fun n => (length n : ℝ) / n) atTop (𝓝 δ) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ y : ℝ,
      μ (tubeEvent X (length n) y (fun _ => a n * l) (fun _ => a n * u)) ≤
        ENNReal.ofReal (Real.exp (-(δ * (C / (u - l) ^ 2) - ε) * ((n : ℝ) / a n ^ 2)))

private theorem prod_exp_block {m : ℕ} (r : ℕ → ℝ) (speed : ℝ) :
    (∏ j ∈ Finset.range m, ENNReal.ofReal (Real.exp (-(r j) * speed))) =
      ENNReal.ofReal (Real.exp (-(∑ j ∈ Finset.range m, r j) * speed)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos (-(r j) * speed)).le),
    ← Real.exp_sum, ← Finset.sum_mul, Finset.sum_neg_distrib]

/-- The fixed-rectangle estimates imply the complete moving-tube exponential estimates. -/
theorem movingTube_exponential_of_rectangular
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f t < g t) (hf0 : f 0 < 0) (hg0 : 0 < g 0)
    (C : ℝ) (hC : 0 ≤ C) (hLower : RectangularLower μ X a C)
    (hUpper : RectangularUpper μ X a C) :
    let rate := C * ∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(rate + ε) * ((n : ℝ) / a n ^ 2))) ≤
        μ (tubeEvent X n 0 (fun k => a n * f ((k : ℝ) / n)) (fun k => a n * g ((k : ℝ) / n))) ∧
      μ (tubeEvent X n 0 (fun k => a n * f ((k : ℝ) / n)) (fun k => a n * g ((k : ℝ) / n))) ≤
        ENNReal.ofReal (Real.exp (-(rate - ε) * ((n : ℝ) / a n ^ 2))) := by
  dsimp only
  intro ε hε
  let rect := tubeRectangles hf hg hfg hf0 hg0 (show 0 < ε / (2 * (C + 1)) by positivity)
  let m := rect.count
  have hm : 0 < m := rect.count_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let time (n : ℕ) := roundedMesh m n
  let length (j n : ℕ) := time n (j + 1) - time n j
  let endpoint (n j : ℕ) := Icc (a n * rect.endpointLower j) (a n * rect.endpointUpper j)
  let pRate (j : ℕ) := (1 / (m : ℝ)) * (C / (rect.innerUpper j - rect.innerLower j) ^ 2) + ε / (2 * m)
  let qRate (j : ℕ) := (1 / (m : ℝ)) * (C / (rect.outerUpper j - rect.outerLower j) ^ 2) - ε / (2 * m)
  let p (n j : ℕ) := ENNReal.ofReal (Real.exp (-(pRate j) * ((n : ℝ) / a n ^ 2)))
  let q (n j : ℕ) := ENNReal.ofReal (Real.exp (-(qRate j) * ((n : ℝ) / a n ^ 2)))
  have herror : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    have hpositive : 0 < C + 1 := by positivity
    have hle : C ≤ C + 1 := le_add_of_nonneg_right zero_le_one
    rw [div_mul_eq_div_div, ← mul_div_assoc]
    exact (div_le_iff₀ hpositive).2
      (by simpa only [mul_comm (C + 1)] using
        mul_le_mul_of_nonneg_right hle (show 0 ≤ ε / 2 by positivity))
  have hcellLower (j : ℕ) (hj : j < m) : ∀ᶠ n in atTop, ∀ y ∈ endpoint n j,
      p n j ≤ μ (endpointTube X (length j n) y (fun _ => a n * rect.innerLower j)
        (fun _ => a n * rect.innerUpper j) (endpoint n (j + 1))) := by
    have hsj := rect.endpoint_nonempty j hj.le
    have hej := rect.endpoint_nonempty (j + 1) (Nat.succ_le_of_lt hj)
    have hleft := rect.start_subset j hj (show rect.endpointLower j ∈ Icc _ _ from ⟨le_rfl, hsj.le⟩)
    have hright := rect.start_subset j hj (show rect.endpointUpper j ∈ Icc _ _ from ⟨hsj.le, le_rfl⟩)
    have hel := rect.end_subset j hj (show rect.endpointLower (j + 1) ∈ Icc _ _ from ⟨le_rfl, hej.le⟩)
    have her := rect.end_subset j hj (show rect.endpointUpper (j + 1) ∈ Icc _ _ from ⟨hej.le, le_rfl⟩)
    exact hLower (length j) (1 / m) _ _ _ _ _ _ (by positivity) hleft.1 hsj.le hright.2
      hel.1 hej her.2 (tendsto_roundedMesh_length_div hm j) _ (by positivity)
  have hcellUpper (j : ℕ) (hj : j < m) : ∀ᶠ n in atTop, ∀ y : ℝ,
      μ (tubeEvent X (length j n) y (fun _ => a n * rect.outerLower j)
        (fun _ => a n * rect.outerUpper j)) ≤ q n j :=
    hUpper (length j) (1 / m) _ _ (by positivity) (rect.outer_pos j hj)
      (tendsto_roundedMesh_length_div hm j) _ (by positivity)
  have hallLower : ∀ᶠ n in atTop, ∀ j ∈ Finset.range m, ∀ y ∈ endpoint n j,
      p n j ≤ μ (endpointTube X (length j n) y (fun _ => a n * rect.innerLower j)
        (fun _ => a n * rect.innerUpper j) (endpoint n (j + 1))) := by
    apply (Filter.eventually_all_finset (Finset.range m)).2
    exact fun j hj => hcellLower j (Finset.mem_range.mp hj)
  have hallUpper : ∀ᶠ n in atTop, ∀ j ∈ Finset.range m, ∀ y : ℝ,
      μ (tubeEvent X (length j n) y (fun _ => a n * rect.outerLower j)
        (fun _ => a n * rect.outerUpper j)) ≤ q n j := by
    apply (Filter.eventually_all_finset (Finset.range m)).2
    exact fun j hj => hcellUpper j (Finset.mem_range.mp hj)
  have hsum_error :
      (∑ _j ∈ Finset.range m, ε / (2 * (m : ℝ))) = ε / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hmR.ne'] <;> ring
  have hpRate : (∑ j ∈ Finset.range m, pRate j) ≤
      C * (∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2) + ε := by
    dsimp only [pRate]
    rw [Finset.sum_add_distrib, hsum_error]
    have h : (∑ j ∈ Finset.range m,
      (1 / (m : ℝ)) * (C / (rect.innerUpper j - rect.innerLower j) ^ 2)) =
        C * ∑ j ∈ Finset.range m,
          (1 / (m : ℝ)) * (1 / (rect.innerUpper j - rect.innerLower j) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h]
    have hrat := mul_le_mul_of_nonneg_left (le_of_abs_le rect.inner_rate) hC
    rw [mul_sub] at hrat
    linarith
  have hqRate : C * (∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2) - ε ≤
      ∑ j ∈ Finset.range m, qRate j := by
    dsimp only [qRate]
    rw [Finset.sum_sub_distrib, hsum_error]
    have h : (∑ j ∈ Finset.range m,
      (1 / (m : ℝ)) * (C / (rect.outerUpper j - rect.outerLower j) ^ 2)) =
        C * ∑ j ∈ Finset.range m,
          (1 / (m : ℝ)) * (1 / (rect.outerUpper j - rect.outerLower j) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h]
    have hrat := mul_le_mul_of_nonneg_left (neg_le_of_abs_le rect.outer_rate) hC
    rw [mul_neg, mul_sub] at hrat
    linarith
  filter_upwards [eventually_ge_atTop m, hallLower, hallUpper] with n hmn hlower hupper
  have hmon := monotone_roundedMesh m n
  have hzero := roundedMesh_zero m n
  have hlast : roundedMesh m n m = n := roundedMesh_end hm n
  have hstart : (0 : ℝ) ∈ endpoint n 0 := by
    have hleft := mul_le_mul_of_nonneg_left rect.start_mem.1 (ha n).le
    have hright := mul_le_mul_of_nonneg_left rect.start_mem.2 (ha n).le
    exact ⟨by simpa using hleft, by simpa using hright⟩
  have hinner := (measure_partitionTube_bounds hX hind hid 0 hmon hzero
    (fun j _ => a n * rect.innerLower j) (fun j _ => a n * rect.innerUpper j)
    (endpoint := endpoint n) (fun _ => measurableSet_Icc) hstart (p n) (fun _ => 1) m
    (fun j hj y hy => ⟨hlower j (Finset.mem_range.mpr hj) y hy, prob_le_one⟩)).1
  have houter := (measure_partitionTube_bounds hX hind hid 0 hmon hzero
    (fun j _ => a n * rect.outerLower j) (fun j _ => a n * rect.outerUpper j)
    (endpoint := fun _ => univ) (fun _ => MeasurableSet.univ) (mem_univ _)
    (fun _ => 0) (q n) m
    (fun j hj y _ => ⟨zero_le, by
      simpa [endpointTube] using hupper j (Finset.mem_range.mpr hj) y⟩)).2
  have hsubsetInner : partitionTube X 0 (time n) (fun j _ => a n * rect.innerLower j)
      (fun j _ => a n * rect.innerUpper j) (endpoint n) m ⊆
      tubeEvent X n 0 (fun k => a n * f ((k : ℝ) / n)) (fun k => a n * g ((k : ℝ) / n)) := by
    have hsubset := partitionTube_subset_tubeEvent (X := X) (x := 0)
      (endpoint := endpoint n) (f := fun k => a n * f ((k : ℝ) / n))
      (g := fun k => a n * g ((k : ℝ) / n))
      (lower := fun j _ => a n * rect.innerLower j) (upper := fun j _ => a n * rect.innerUpper j)
      hmon hzero hm
    have h := hsubset (by
      intro j hj k hk
      obtain ⟨hmem, hdist⟩ := roundedMesh_cell_bounds hm hmn hj hk
      have hb := rect.bounds j hj _ hmem hdist
      exact ⟨mul_le_mul_of_nonneg_left hb.2.1 (ha n).le,
        mul_le_mul_of_nonneg_left hb.2.2.1 (ha n).le⟩)
    simpa only [hlast] using h
  have hsubsetOuter : tubeEvent X n 0 (fun k => a n * f ((k : ℝ) / n)) (fun k => a n * g ((k : ℝ) / n)) ⊆
      partitionTube X 0 (time n) (fun j _ => a n * rect.outerLower j)
        (fun j _ => a n * rect.outerUpper j) (fun _ => univ) m := by
    have hsubset := tubeEvent_subset_partitionTube (X := X) (x := 0) (count := m)
      (f := fun k => a n * f ((k : ℝ) / n)) (g := fun k => a n * g ((k : ℝ) / n))
      (lower := fun j _ => a n * rect.outerLower j) (upper := fun j _ => a n * rect.outerUpper j) hmon
    have h := hsubset (by
      intro j hj k hk
      obtain ⟨hmem, hdist⟩ := roundedMesh_cell_bounds hm hmn hj hk
      have hb := rect.bounds j hj _ hmem hdist
      exact ⟨mul_le_mul_of_nonneg_left hb.1 (ha n).le,
        mul_le_mul_of_nonneg_left hb.2.2.2 (ha n).le⟩)
    simpa only [hlast] using h
  have hspeed : 0 ≤ (n : ℝ) / a n ^ 2 := by positivity
  constructor
  · refine le_trans ?_ (hinner.trans (measure_mono hsubsetInner))
    change _ ≤ ∏ j ∈ Finset.range m, ENNReal.ofReal (Real.exp (-(pRate j) * ((n : ℝ) / a n ^ 2)))
    rw [prod_exp_block]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg hpRate) hspeed))
  · refine (measure_mono hsubsetOuter).trans (houter.trans ?_)
    change (∏ j ∈ Finset.range m, ENNReal.ofReal (Real.exp (-(qRate j) * ((n : ℝ) / a n ^ 2)))) ≤ _
    rw [prod_exp_block]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg hqRate) hspeed))

end Mogulskii.SmallDeviation



