import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ENNReal
open ProbabilityTheory MeasureTheory Set Filter
open scoped Topology

namespace Mogulskii

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}

/-- Chernoff estimate for the union of finitely many blocks. The blocks need not be disjoint. -/
theorem measure_block_union_le {ι : Type*} (blocks : Finset ι) (B : ι → Finset ℕ)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hId : ∀ i, IdentDistrib (X i) (X 0) μ μ) {t ε b : ℝ}
    (ht : 0 ≤ t) (hExp : ∀ i, Integrable (fun ω => Real.exp (t * X i ω)) μ)
    (hcard : ∀ j ∈ blocks, ((B j).card : ℝ) ≤ b) :
    μ (⋃ j ∈ blocks, {ω | ε ≤ ∑ i ∈ B j, X i ω}) ≤
      (blocks.card : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-t * ε + b * max 0 (cgf (X 0) μ t))) := by
  classical
  refine (measure_biUnion_finset_le blocks _).trans ?_
  have hblock (j) (hj : j ∈ blocks) :
      μ {ω | ε ≤ ∑ i ∈ B j, X i ω} ≤
        ENNReal.ofReal (Real.exp (-t * ε + b * max 0 (cgf (X 0) μ t))) := by
    have hexp := hInd.integrable_exp_mul_sum hX (s := B j) (fun i _ => hExp i)
    have hchernoff := measure_ge_le_exp_cgf (X := ∑ i ∈ B j, X i) ε ht hexp
    rw [hInd.cgf_sum hX (fun i _ => hExp i)] at hchernoff
    have hcgf (i : ℕ) : cgf (X i) μ t = cgf (X 0) μ t :=
      congrArg Real.log (mgf_congr_of_identDistrib _ _ (hId i) _)
    simp only [hcgf, Finset.sum_const, nsmul_eq_mul, Finset.sum_apply] at hchernoff
    have hcgf_le :
        ((B j).card : ℝ) * cgf (X 0) μ t ≤ b * max 0 (cgf (X 0) μ t) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hcard j hj) (le_max_left _ _))
    have he := hchernoff.trans
      (Real.exp_le_exp.mpr (add_le_add_right hcgf_le _))
    have hh := ENNReal.ofReal_le_ofReal he
    rwa [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
  calc
    _ ≤ ∑ _j ∈ blocks,
        ENNReal.ofReal (Real.exp (-t * ε + b * max 0 (cgf (X 0) μ t))) :=
      Finset.sum_le_sum hblock
    _ = _ := by simp [nsmul_eq_mul]

/-- Blocks of relative length at most one over the mesh size have superexponential tails
at every fixed positive threshold when the mesh is refined. -/
theorem eventually_measure_block_union_le {ι : Type*}
    (blocks : ℕ → Finset ι) (B : ℕ → ℕ → ι → Finset ℕ)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hId : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hExp : ∀ t ≥ 0, ∀ i, Integrable (fun ω => Real.exp (t * X i ω)) μ)
    (hcard : ∀ m n j, j ∈ blocks m → ((B m n j).card : ℝ) ≤ (n : ℝ) / m + 2)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      μ (⋃ j ∈ blocks m, {ω | (n : ℝ) * δ ≤ ∑ i ∈ B m n j, X i ω}) ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * r))) := by
  let t := (max 0 r + 2) / δ
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htδ : r + 2 ≤ t * δ := by
    dsimp [t]
    rw [div_mul_cancel₀ _ hδ.ne']
    linarith [le_max_right 0 r]
  let c := max 0 (cgf (X 0) μ t)
  have hc : 0 ≤ c := le_max_left _ _
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * c + 1)
  filter_upwards [eventually_ge_atTop M] with m hm
  have hm' : 2 * c + 1 < m := hM.trans_le (by exact_mod_cast hm)
  have hm₀ : 0 < (m : ℝ) := by linarith
  have hcm : c / (m : ℝ) ≤ 1 / 2 := (div_le_iff₀ hm₀).mpr (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (4 * c) ((blocks m).card : ℝ))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : max (4 * c) ((blocks m).card : ℝ) < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast hn)
  have hcn : 4 * c ≤ n := (le_max_left _ _).trans hNn.le
  have hsize : ((blocks m).card : ℝ) ≤ n := (le_max_right _ _).trans hNn.le
  have hsize' : ((blocks m).card : ℝ) ≤ Real.exp n := hsize.trans (by
    linarith [Real.add_one_le_exp (n : ℝ)])
  have hcast : ((blocks m).card : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp n) := by
    simpa using ENNReal.ofReal_le_ofReal hsize'
  have hbound : -t * ((n : ℝ) * δ) + ((n : ℝ) / m + 2) * c ≤ -((n : ℝ) * (r + 1)) := by
    have h₁ := mul_le_mul_of_nonneg_left htδ (Nat.cast_nonneg (α := ℝ) n)
    have h₂ := mul_le_mul_of_nonneg_left hcm (Nat.cast_nonneg (α := ℝ) n)
    calc
      _ = -((n : ℝ) * (t * δ)) + (n : ℝ) * (c / m) + 2 * c := by ring
      _ ≤ -((n : ℝ) * (r + 1)) := by linarith
  calc
    _ ≤ ((blocks m).card : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-t * ((n : ℝ) * δ) + ((n : ℝ) / m + 2) * c)) :=
      measure_block_union_le (blocks m) (B m n) hX hInd hId ht (hExp _ ht)
        (fun j hj => hcard m n j hj)
    _ ≤ ENNReal.ofReal (Real.exp n) * ENNReal.ofReal (Real.exp (-((n : ℝ) * (r + 1)))) :=
      mul_le_mul' hcast (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hbound))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

end Mogulskii


