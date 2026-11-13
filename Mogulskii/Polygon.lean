import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators Topology
open Set
open Filter Metric

namespace Mogulskii

abbrev UnitTime := Set.Icc (0 : ℝ) 1

/-- The coefficient of increment `i` in the polygonal interpolation at time `t`. -/
noncomputable def ramp (n i : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 ((n : ℝ) * t - i))

theorem continuous_ramp (n i : ℕ) : Continuous (ramp n i) := by
  unfold ramp
  fun_prop

theorem ramp_nonneg (n i : ℕ) (t : ℝ) : 0 ≤ ramp n i t := le_max_left _ _

theorem ramp_le_one (n i : ℕ) (t : ℝ) : ramp n i t ≤ 1 := by
  unfold ramp
  exact max_le (by norm_num) (min_le_left _ _)

theorem ramp_mono (n i : ℕ) : Monotone (ramp n i) := by
  intro s t h
  unfold ramp
  exact max_le_max le_rfl (min_le_min le_rfl
    (sub_le_sub_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)) _))

theorem ramp_eq_zero (n i : ℕ) (t : ℝ) (h : (n : ℝ) * t ≤ i) : ramp n i t = 0 := by
  unfold ramp
  exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr h))

theorem ramp_eq_one (n i : ℕ) (t : ℝ) (h : (i : ℝ) + 1 ≤ (n : ℝ) * t) :
    ramp n i t = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith : 1 ≤ (n : ℝ) * t - i), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rescaled polygon with vertices given by the partial sums of the increments. -/
noncomputable def polygon (n : ℕ) (x : ℕ → E) : C(UnitTime, E) where
  toFun t := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ramp n i t • x i
  continuous_toFun := by
    apply Continuous.const_smul
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_ramp n i).comp continuous_subtype_val).smul continuous_const

theorem polygon_zero (n : ℕ) (x : ℕ → E) :
    polygon n x ⟨0, by norm_num⟩ = 0 := by
  change (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ramp n i 0 • x i = 0
  have h (i : ℕ) : ramp n i 0 = 0 := ramp_eq_zero _ _ _ (by simp)
  simp [h]

/-- Evaluation at a mesh point recovers the corresponding scaled partial sum. -/
theorem polygon_mesh (n k : ℕ) (hkn : k ≤ n) (hn : n ≠ 0) (x : ℕ → E) :
    polygon n x ⟨(k : ℝ) / n, by
      refine ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hkn)⟩⟩ =
        (n : ℝ)⁻¹ • ∑ i ∈ Finset.range k, x i := by
  change (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ramp n i ((k : ℝ) / n) • x i =
    (n : ℝ)⁻¹ • ∑ i ∈ Finset.range k, x i
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hk : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
  calc
    ∑ i ∈ Finset.range n, ramp n i ((k : ℝ) / n) • x i =
        ∑ i ∈ Finset.range k, ramp n i ((k : ℝ) / n) • x i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hkn)
      intro i hi hik
      have hik' : k ≤ i := by simpa using hik
      rw [ramp_eq_zero _ _ _ (by rw [hk]; exact_mod_cast hik'), zero_smul]
    _ = ∑ i ∈ Finset.range k, x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i + 1 ≤ k := Finset.mem_range.mp hi
      rw [ramp_eq_one _ _ _ (by rw [hk]; exact_mod_cast hi'), one_smul]

/-- Between mesh points the path is the corresponding affine interpolation. -/
theorem polygon_between (n k : ℕ) (hk : k < n) (x : ℕ → E) (t : UnitTime)
    (htl : (k : ℝ) ≤ (n : ℝ) * (t : ℝ))
    (htr : (n : ℝ) * (t : ℝ) ≤ (k : ℝ) + 1) :
    polygon n x t =
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range k, x i + ((n : ℝ) * (t : ℝ) - k) • x k) := by
  change (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, ramp n i t • x i = _
  congr 1
  calc
    ∑ i ∈ Finset.range n, ramp n i t • x i =
        ∑ i ∈ Finset.range (k + 1), ramp n i t • x i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i _ hi
      have hki : k + 1 ≤ i := by simpa using hi
      rw [ramp_eq_zero _ _ _ (htr.trans (by exact_mod_cast hki)), zero_smul]
    _ = _ := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have h : i + 1 ≤ k := Finset.mem_range.mp hi
        rw [ramp_eq_one _ _ _ ((by exact_mod_cast h : (i : ℝ) + 1 ≤ k).trans htl), one_smul]
      · unfold ramp
        rw [min_eq_right (by linarith), max_eq_right (sub_nonneg.mpr htl)]

/-- Varying the increments changes the path uniformly by at most the sum of their changes. -/
theorem dist_polygon_le (n : ℕ) (x y : ℕ → E) :
    dist (polygon n x) (polygon n y) ≤
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, dist (x i) (y i) := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  rw [dist_eq_norm]
  change ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i t • x i) -
    (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i t • y i)‖ ≤ _
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  calc
    ‖∑ i ∈ Finset.range n, (ramp n i t • x i - ramp n i t • y i)‖ ≤
        ∑ i ∈ Finset.range n, ‖ramp n i t • x i - ramp n i t • y i‖ := norm_sum_le _ _
    _ ≤ _ := by
      gcongr with i hi
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg n i t),
        dist_eq_norm]
      exact mul_le_of_le_one_left (norm_nonneg _) (ramp_le_one n i t)

/-- Continuity of polygonal interpolation in the product topology on increments. -/
theorem continuous_polygon (n : ℕ) : Continuous (polygon (E := E) n) := by
  rw [continuous_iff_continuousAt]
  intro x
  have h :
      Filter.Tendsto (fun y : ℕ → E =>
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, dist (y i) (x i)) (𝓝 x) (𝓝 0) := by
    have hc : Continuous fun y : ℕ → E =>
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, dist (y i) (x i) :=
      continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).dist continuous_const)
    have ht := hc.continuousAt (x := x)
    change Filter.Tendsto _ _ (𝓝 ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, dist (x i) (x i))) at ht
    simpa using ht
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun y => dist_polygon_le n y x) h)

/-- A polygon increment is controlled by the norms of the walk increments whose time
intervals meet the given interval. -/
theorem dist_polygon_le_sum (n : ℕ) (x : ℕ → E) {s t : UnitTime} (hst : s ≤ t) :
    dist (polygon n x t) (polygon n x s) ≤
      (n : ℝ)⁻¹ * ∑ i ∈ (Finset.range n).filter
        (fun i : ℕ => (i : ℝ) < (n : ℝ) * t ∧ (n : ℝ) * s < (i : ℝ) + 1), ‖x i‖ := by
  classical
  rw [dist_eq_norm]
  change ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i t • x i) -
    (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, ramp n i s • x i)‖ ≤ _
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  calc
    ‖∑ i ∈ Finset.range n, (ramp n i t • x i - ramp n i s • x i)‖ ≤
        ∑ i ∈ Finset.range n, ‖ramp n i t • x i - ramp n i s • x i‖ := norm_sum_le _ _
    _ = ∑ i ∈ (Finset.range n).filter
        (fun i : ℕ => (i : ℝ) < (n : ℝ) * t ∧ (n : ℝ) * s < (i : ℝ) + 1),
        ‖ramp n i t • x i - ramp n i s • x i‖ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi h
      have hs : (n : ℝ) * (s : ℝ) ≤ (n : ℝ) * (t : ℝ) :=
        mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n)
      have h' : ¬ ((i : ℝ) < (n : ℝ) * t ∧ (n : ℝ) * s < (i : ℝ) + 1) :=
        fun hh => h (Finset.mem_filter.mpr ⟨hi, hh⟩)
      rcases not_and_or.mp h' with h' | h'
      · rw [ramp_eq_zero _ _ _ (le_of_not_gt h'),
          ramp_eq_zero _ _ _ (hs.trans (le_of_not_gt h')), sub_self, norm_zero]
      · rw [ramp_eq_one _ _ _ ((le_of_not_gt h').trans hs),
          ramp_eq_one _ _ _ (le_of_not_gt h'), sub_self, norm_zero]
    _ ≤ _ := by
      gcongr with i hi
      rw [← sub_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (ramp_mono n i hst))]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        linarith [ramp_le_one n i t, ramp_nonneg n i s])

/-- Mesh times on the unit interval, with indices above the mesh clamped at its endpoint. -/
noncomputable def meshTime (m k : ℕ) : UnitTime :=
  ⟨(min k m : ℝ) / m, by
    refine ⟨by positivity, ?_⟩
    by_cases hm : m = 0
    · simp [hm]
    · exact (div_le_one (by positivity)).mpr (by exact_mod_cast min_le_right k m)⟩

theorem coe_meshTime {m k : ℕ} (hk : k ≤ m) : (meshTime m k : ℝ) = (k : ℝ) / m := by
  change (min (k : ℝ) (m : ℝ)) / m = _
  rw [min_eq_left (by exact_mod_cast hk)]

/-- The polygonal interpolation of the values of a continuous path on an equally spaced mesh. -/
noncomputable def meshInterpolate (m : ℕ) (φ : C(UnitTime, E)) : C(UnitTime, E) :=
  ContinuousMap.const _ (φ (meshTime m 0)) +
    polygon m (fun k => (m : ℝ) • (φ (meshTime m (k + 1)) - φ (meshTime m k)))

omit [NormedSpace ℝ E] in
private theorem sum_mesh_sub (m k : ℕ) (φ : C(UnitTime, E)) :
    ∑ i ∈ Finset.range k, (φ (meshTime m (i + 1)) - φ (meshTime m i)) =
      φ (meshTime m k) - φ (meshTime m 0) := by
  induction k with
  | zero => simp
  | succ k hk => rw [Finset.sum_range_succ, hk, sub_add_sub_cancel']

theorem meshInterpolate_between {m k : ℕ} (hk : k < m) (φ : C(UnitTime, E))
    (t : UnitTime) (htl : (k : ℝ) ≤ (m : ℝ) * (t : ℝ))
    (htr : (m : ℝ) * (t : ℝ) ≤ (k : ℝ) + 1) :
    meshInterpolate m φ t = φ (meshTime m k) +
      ((m : ℝ) * (t : ℝ) - k) • (φ (meshTime m (k + 1)) - φ (meshTime m k)) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hk).ne'
  simp only [meshInterpolate, ContinuousMap.add_apply, ContinuousMap.const_apply]
  rw [polygon_between _ _ hk _ _ htl htr, ← Finset.smul_sum, smul_add,
    inv_smul_smul₀ hm, sum_mesh_sub, smul_comm ((m : ℝ) * (t : ℝ) - k) (m : ℝ),
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hm, one_smul]
  abel

theorem exists_mesh_interval {m : ℕ} (hm : 0 < m) (t : UnitTime) :
    ∃ k : ℕ, k < m ∧ (k : ℝ) ≤ (m : ℝ) * (t : ℝ) ∧
      (m : ℝ) * (t : ℝ) ≤ (k : ℝ) + 1 := by
  have hn : 0 ≤ (m : ℝ) * (t : ℝ) := mul_nonneg (Nat.cast_nonneg _) t.property.1
  have hle : (m : ℝ) * (t : ℝ) ≤ m := mul_le_of_le_one_right (Nat.cast_nonneg _) t.property.2
  by_cases hlt : (m : ℝ) * (t : ℝ) < m
  · refine ⟨⌊(m : ℝ) * (t : ℝ)⌋₊, (Nat.floor_lt hn).mpr hlt, Nat.floor_le hn, ?_⟩
    exact (Nat.lt_floor_add_one _).le
  · have he : (m : ℝ) * (t : ℝ) = m := le_antisymm hle (le_of_not_gt hlt)
    refine ⟨m - 1, by omega, ?_, ?_⟩
    · rw [he]
      exact_mod_cast Nat.sub_le m 1
    · rw [he]
      exact_mod_cast (show m ≤ m - 1 + 1 by omega)

/-- Uniform continuity of a path gives uniform convergence of its mesh interpolants. -/
theorem tendsto_meshInterpolate (φ : C(UnitTime, E)) :
    Tendsto (fun m => meshInterpolate m φ) atTop (𝓝 φ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous φ.continuous)
      (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm₀ : 0 < m := by omega
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm₀
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast (show N ≤ m by omega)
  have hinv : (m : ℝ)⁻¹ < δ := by
    rw [inv_lt_comm₀ hm' hδ]
    exact hN.trans_le hmN
  have hbound : dist (meshInterpolate m φ) φ ≤ ε / 2 := by
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    obtain ⟨k, hk, htl, htr⟩ := exists_mesh_interval hm₀ t
    let a := (m : ℝ) * (t : ℝ) - k
    have ha : 0 ≤ a := sub_nonneg.mpr htl
    have ha' : a ≤ 1 := by dsimp [a]; linarith
    have hl : dist (meshTime m k) t ≤ (m : ℝ)⁻¹ := by
      change dist (meshTime m k : ℝ) (t : ℝ) ≤ _
      rw [coe_meshTime hk.le, Real.dist_eq, abs_of_nonpos
        (sub_nonpos.mpr ((div_le_iff₀ hm').mpr (by simpa [mul_comm] using htl)))]
      rw [← one_div]
      apply (le_div_iff₀ hm').mpr
      rw [neg_sub, sub_mul, div_mul_cancel₀ _ hm'.ne']
      linarith
    have hr : dist (meshTime m (k + 1)) t ≤ (m : ℝ)⁻¹ := by
      change dist (meshTime m (k + 1) : ℝ) (t : ℝ) ≤ _
      rw [coe_meshTime hk, Nat.cast_succ, Real.dist_eq, abs_of_nonneg
        (sub_nonneg.mpr ((le_div_iff₀ hm').mpr (by simpa [mul_comm] using htr)))]
      rw [← one_div]
      apply (le_div_iff₀ hm').mpr
      rw [sub_mul, div_mul_cancel₀ _ hm'.ne']
      linarith
    have hL := hu (hl.trans_lt hinv)
    have hR := hu (hr.trans_lt hinv)
    rw [meshInterpolate_between hk φ t htl htr, dist_eq_norm]
    change ‖φ (meshTime m k) + a • (φ (meshTime m (k + 1)) - φ (meshTime m k)) -
      φ t‖ ≤ _
    have heq : φ (meshTime m k) + a • (φ (meshTime m (k + 1)) - φ (meshTime m k)) -
        φ t = (1 - a) • (φ (meshTime m k) - φ t) + a • (φ (meshTime m (k + 1)) - φ t) := by
      simp only [sub_smul, smul_sub, one_smul]
      abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg ha, ← dist_eq_norm, ← dist_eq_norm]
    calc
      _ ≤ (1 - a) * (ε / 2) + a * (ε / 2) := by gcongr
      _ = ε / 2 := by ring
  exact hbound.trans_lt (by linarith)

end Mogulskii



