import Mogulskii.GridPolygon
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace Mogulskii

/-- Indices of the increments meeting a mesh interval, including its right boundary. -/
def meshBlock (m n k : ℕ) : Finset ℕ :=
  Finset.Ico (gridIndex n m k) (gridIndex n m (k + 1) + 1)

theorem card_meshBlock {m : ℕ} (hm : 0 < m) (n k : ℕ) :
    ((meshBlock m n k).card : ℝ) ≤ (n : ℝ) / m + 2 := by
  have hmono : gridIndex n m k ≤ gridIndex n m (k + 1) := gridIndex_mono n m (Nat.le_succ k)
  rw [meshBlock, Nat.card_Ico, Nat.cast_sub (hmono.trans (Nat.le_succ _)), Nat.cast_succ]
  obtain ⟨hl, _⟩ := gridIndex_rounding n hm k
  obtain ⟨_, hr⟩ := gridIndex_rounding n hm (k + 1)
  have heq : (n : ℝ) * ((k + 1 : ℕ) : ℝ) / m =
      (n : ℝ) * k / m + (n : ℝ) / m := by push_cast; ring
  rw [heq] at hr
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem dist_polygon_le_meshBlock (m n k : ℕ) (hm : 0 < m) (x : ℕ → E)
    {s t : UnitTime} (hs : (gridIndex n m k : ℝ) ≤ (n : ℝ) * (s : ℝ))
    (ht : (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * (k + 1) / m) (hst : s ≤ t) :
    dist (polygon n x t) (polygon n x s) ≤
      (n : ℝ)⁻¹ * ∑ i ∈ meshBlock m n k, ‖x i‖ := by
  classical
  refine (dist_polygon_le_sum n x hst).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  have hu := (gridIndex_rounding n hm (k + 1)).1
  simp only [Nat.cast_add, Nat.cast_one] at hu
  apply Finset.mem_Ico.mpr
  constructor
  · by_contra! hlt
    have hi' : (i : ℝ) + 1 ≤ gridIndex n m k := by exact_mod_cast hlt
    linarith [h.2]
  · have hi' : (i : ℝ) < (gridIndex n m (k + 1) : ℝ) + 1 := by linarith [h.1]
    exact_mod_cast hi'

private noncomputable def roundedMesh (m n k : ℕ) : UnitTime :=
  meshTime n (gridIndex n m k)

private theorem gridIndex_le {m : ℕ} (hm : 0 < m) (n : ℕ) {k : ℕ} (hk : k ≤ m) :
    gridIndex n m k ≤ n := by
  refine (gridIndex_mono n m hk).trans_eq ?_
  simp [gridIndex, Nat.mul_div_cancel _ hm]

private theorem coe_roundedMesh {m n k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    (roundedMesh m n k : ℝ) = (gridIndex n m k : ℝ) / n :=
  coe_meshTime (gridIndex_le hm n hk)

private theorem roundedPolygon_between {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hk : k < m) (x : ℕ → E) (t : UnitTime)
    (htl : (k : ℝ) ≤ (m : ℝ) * (t : ℝ))
    (htr : (m : ℝ) * (t : ℝ) ≤ (k : ℝ) + 1) :
    polygon m (fun j => ((m : ℝ) / n) • ∑ i ∈
        Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), x i) t =
      (1 - ((m : ℝ) * (t : ℝ) - k)) • polygon n x (roundedMesh m n k) +
        ((m : ℝ) * (t : ℝ) - k) • polygon n x (roundedMesh m n (k + 1)) := by
  have hsum (l : ℕ) : ∑ j ∈ Finset.range l,
      ∑ i ∈ Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), x i =
      ∑ i ∈ Finset.range (gridIndex n m l), x i := by
    induction l with
    | zero => simp [gridIndex]
    | succ l ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_add_sum_Ico _ (gridIndex_mono n m (Nat.le_succ l))]
  have hmesh (l : ℕ) (hl : l ≤ m) :
      polygon n x (roundedMesh m n l) = (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (gridIndex n m l), x i := by
    have htime : roundedMesh m n l =
        ⟨(gridIndex n m l : ℝ) / n, by
          rw [← coe_roundedMesh hm hl]
          exact (roundedMesh m n l).property⟩ := Subtype.ext (coe_roundedMesh hm hl)
    rw [htime]
    exact polygon_mesh n (gridIndex n m l) (gridIndex_le hm n hl) hn.ne' x
  have hcoef : (m : ℝ)⁻¹ * ((m : ℝ) / n) = (n : ℝ)⁻¹ := by
    have hm' : (m : ℝ) ≠ 0 := by positivity
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]
  rw [polygon_between _ _ hk _ _ htl htr, ← Finset.smul_sum, hsum,
    hmesh k hk.le, hmesh (k+1) hk, ← Finset.sum_range_add_sum_Ico _ (gridIndex_mono n m (Nat.le_succ k))]
  simp only [smul_add, ← smul_assoc, smul_eq_mul, hcoef]
  rw [show (m : ℝ)⁻¹ * (((m : ℝ) * (t : ℝ) - k) * ((m : ℝ) / n)) =
      ((m : ℝ) * (t : ℝ) - k) * (n : ℝ)⁻¹ by rw [← mul_left_comm, hcoef]]
  simp only [Nat.succ_eq_add_one]
  rw [show ((1 - ((m : ℝ) * (t : ℝ) - k)) * (n : ℝ)⁻¹) =
    (n : ℝ)⁻¹ - ((m : ℝ) * (t : ℝ) - k) * (n : ℝ)⁻¹ by ring, sub_smul]
  abel

private theorem dist_polygon_rounded_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : ℕ → E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ k < m, ∑ i ∈ meshBlock m n k, ‖x i‖ ≤ (n : ℝ) * δ) :
    dist (polygon n x) (polygon m (fun j => ((m : ℝ) / n) • ∑ i ∈
        Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), x i)) ≤ δ := by
  apply (ContinuousMap.dist_le hδ).mpr
  intro t
  obtain ⟨k, hk, htl, htr⟩ := exists_mesh_interval hm t
  have hn' : (0 : ℝ) < n := by positivity
  have hm' : (0 : ℝ) < m := by positivity
  have ht₁ : (gridIndex n m k : ℝ) ≤ (n : ℝ) * (t : ℝ) := by
    apply (gridIndex_rounding n hm k).2.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hm').mpr (by simpa [mul_comm] using htl)) hn'.le
  have ht₂ : (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * ((k : ℝ) + 1) / m := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hm').mpr (by simpa [mul_comm] using htr)) hn'.le
  have hdist (j : ℕ) (hj₁ : k ≤ j) (hj₂ : j ≤ k + 1) :
      dist (polygon n x t) (polygon n x (roundedMesh m n j)) ≤ δ := by
    have hjm : j ≤ m := hj₂.trans hk
    have hjx : (n : ℝ) * (roundedMesh m n j : ℝ) = (gridIndex n m j : ℝ) := by
      rw [coe_roundedMesh hm hjm, mul_comm, div_mul_cancel₀ _ hn'.ne']
    have hjlow : (gridIndex n m k : ℝ) ≤ (n : ℝ) * (roundedMesh m n j : ℝ) := by
      rw [hjx]
      exact_mod_cast gridIndex_mono n m hj₁
    have hjhigh : (n : ℝ) * (roundedMesh m n j : ℝ) ≤ (n : ℝ) * ((k : ℝ) + 1) / m := by
      rw [hjx]
      have hcast : (gridIndex n m j : ℝ) ≤ (gridIndex n m (k+1) : ℝ) := by
        exact_mod_cast gridIndex_mono n m hj₂
      exact hcast.trans (by simpa using (gridIndex_rounding n hm (k+1)).2)
    have hδ' : (n : ℝ)⁻¹ * ∑ i ∈ meshBlock m n k, ‖x i‖ ≤ δ := by
      calc
        _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left (hsmall k hk) (by positivity)
        _ = δ := by rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
    rcases le_total (roundedMesh m n j) t with h | h
    · exact (dist_polygon_le_meshBlock m n k hm x hjlow ht₂ h).trans hδ'
    · rw [dist_comm]
      exact (dist_polygon_le_meshBlock m n k hm x ht₁ hjhigh h).trans hδ'
  rw [roundedPolygon_between hm hn hk x t htl htr, dist_eq_norm]
  let a := (m : ℝ) * (t : ℝ) - k
  have ha : 0 ≤ a := sub_nonneg.mpr htl
  have ha' : 0 ≤ 1 - a := by dsimp [a]; linarith
  change ‖polygon n x t -
    ((1 - a) • polygon n x (roundedMesh m n k) + a • polygon n x (roundedMesh m n (k + 1)))‖ ≤ δ
  have heq : polygon n x t -
    ((1 - a) • polygon n x (roundedMesh m n k) + a • polygon n x (roundedMesh m n (k + 1))) =
      (1 - a) • (polygon n x t - polygon n x (roundedMesh m n k)) +
        a • (polygon n x t - polygon n x (roundedMesh m n (k + 1))) := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha',
    abs_of_nonneg ha, ← dist_eq_norm, ← dist_eq_norm]
  calc
    _ ≤ (1 - a) * δ + a * δ :=
      add_le_add (mul_le_mul_of_nonneg_left (hdist k le_rfl (Nat.le_succ k)) ha')
        (mul_le_mul_of_nonneg_left (hdist (k + 1) (Nat.le_succ k) le_rfl) ha)
    _ = δ := by ring

section

variable {Ω : Type*}

private theorem dist_rounded_gridPolygon_le {m n : ℕ} (hm : 0 < m)
    (hn : m * (m + 1) ≤ n) (X : ℕ → Ω → E) (ω : Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ k < m, ∑ i ∈ meshBlock m n k, ‖X i ω‖ ≤ (n : ℝ) * δ) :
    dist (polygon m (fun j => ((m : ℝ) / n) • ∑ i ∈
        Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), X i ω))
      (gridPolygon m (gridAverages X n m ω)) ≤ δ := by
  have hm' : (0 : ℝ) < m := by positivity
  have hn₀ : 0 < n := (Nat.mul_pos hm (Nat.succ_pos _)).trans_le hn
  have hn' : (0 : ℝ) < n := by positivity
  have hmn : (m : ℝ) * ((m : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) / m :=
    (le_div_iff₀ hm').mpr (by linarith only [hmn, mul_comm (m : ℝ) ((m : ℝ) + 1)])
  unfold gridPolygon
  refine (dist_polygon_le _ _ _).trans ?_
  have hterm (j : ℕ) (hj : j ∈ Finset.range m) :
      dist (((m : ℝ) / n) • ∑ i ∈
          Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), X i ω)
        (extendFin (gridAverages X n m ω) j) ≤ δ := by
    have hj' := Finset.mem_range.mp hj
    let a : Fin m := ⟨j, hj'⟩
    have hr := gridCount_rounding n hm a
    rw [mul_one_div] at hr
    have hcm : (m : ℝ) ≤ gridCount n m a := by
      linarith [neg_le_abs ((gridCount n m a : ℝ) - (n : ℝ) / m)]
    have hc : (0 : ℝ) < gridCount n m a := hm'.trans_le hcm
    rw [show extendFin (gridAverages X n m ω) j = gridAverages X n m ω a by
      simp [extendFin, hj', a]]
    rw [← gridCount_smul_gridAverages X n m ω a, dist_eq_norm, smul_smul]
    rw [show ((m : ℝ) / n * (gridCount n m a : ℝ)) • gridAverages X n m ω a -
        gridAverages X n m ω a =
        ((m : ℝ) / n * (gridCount n m a : ℝ) - 1) • gridAverages X n m ω a by
      rw [sub_smul, one_smul]]
    rw [norm_smul, Real.norm_eq_abs]
    have hcoef : (m : ℝ) / n * (gridCount n m a : ℝ) - 1 =
        ((m : ℝ) / n) * ((gridCount n m a : ℝ) - (n : ℝ) / m) := by
      field_simp [hm'.ne', hn'.ne'] <;> ring
    rw [hcoef, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) / n)]
    have hnorm : ‖gridAverages X n m ω a‖ ≤ (n : ℝ) * δ / (m : ℝ) := by
      have hsum : ‖∑ i ∈ Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), X i ω‖ ≤
          (n : ℝ) * δ := by
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun _ _ _ => norm_nonneg _)).trans (hsmall j hj'))
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        exact Finset.mem_Ico.mpr ⟨hi'.1, hi'.2.trans (Nat.lt_succ_self _)⟩
      rw [← gridCount_smul_gridAverages X n m ω a, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc] at hsum
      apply (le_div_iff₀ hm').mpr
      simpa [mul_comm] using (mul_le_mul_of_nonneg_right hcm (norm_nonneg _)).trans hsum
    calc
      _ ≤ ((m : ℝ) / n) * 1 * ((n : ℝ) * δ / (m : ℝ)) := by gcongr
      _ = δ := by field_simp
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ _j ∈ Finset.range m, δ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = δ := by simp [nsmul_eq_mul, ← mul_assoc, hm'.ne']

theorem dist_polygon_gridPolygon_le {m n : ℕ} (hm : 0 < m) (hn : m * (m + 1) ≤ n)
    (X : ℕ → Ω → E) (ω : Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ k < m, ∑ i ∈ meshBlock m n k, ‖X i ω‖ ≤ (n : ℝ) * (δ / 2)) :
    dist (polygon n (fun i => X i ω)) (gridPolygon m (gridAverages X n m ω)) ≤ δ := by
  have hn₀ : 0 < n := (Nat.mul_pos hm (Nat.succ_pos _)).trans_le hn
  refine (dist_triangle _ (polygon m (fun j => ((m : ℝ) / n) • ∑ i ∈
    Finset.Ico (gridIndex n m j) (gridIndex n m (j + 1)), X i ω)) _).trans ?_
  exact (add_le_add (dist_polygon_rounded_le hm hn₀ _ (by positivity) hsmall)
    (dist_rounded_gridPolygon_le hm hn X ω (by positivity) hsmall)).trans_eq (by ring)

end

end Mogulskii

