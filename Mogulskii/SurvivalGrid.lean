import Mogulskii.BrownianBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Set MeasureTheory
open scoped Topology NNReal

namespace Mogulskii

def intervalSurvival {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (left right : ℝ) (T : ℝ≥0) : Set Ω :=
  {ω | ∀ t ≤ T, B t ω ∈ Icc left right}

noncomputable def uniformGrid (T : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  (T / (n + 1 : ℕ)) * (k : ℝ≥0)

theorem monotone_uniformGrid (T : ℝ≥0) (n : ℕ) : Monotone (uniformGrid T n) := by
  intro a b hab
  exact mul_le_mul_right (by exact_mod_cast hab) _

@[simp] theorem uniformGrid_zero (T : ℝ≥0) (n : ℕ) : uniformGrid T n 0 = 0 := by
  simp [uniformGrid]

@[simp] theorem uniformGrid_last (T : ℝ≥0) (n : ℕ) : uniformGrid T n (n + 1) = T := by
  have h : ((↑(n + 1) : ℝ≥0)) ≠ 0 := by positivity
  exact div_mul_cancel₀ T h

theorem uniformGrid_succ (T : ℝ≥0) (n k : ℕ) :
    uniformGrid T n (k + 1) = uniformGrid T n k + T / (n + 1 : ℕ) := by
  simp [uniformGrid, mul_add]

theorem tendsto_uniformGrid_mesh (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      ((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)).const_mul (T : ℝ)

private theorem exists_uniformGrid_close {t T : ℝ≥0} (ht : t ≤ T) (hT : 0 < T) (n : ℕ) :
    ∃ k ≤ n + 1, dist (uniformGrid T n k) t ≤ (T : ℝ) / ((n : ℝ) + 1) := by
  let mesh : ℝ := (T : ℝ) / ((n : ℝ) + 1)
  have hmesh : 0 < mesh := div_pos (by exact_mod_cast hT) (by positivity)
  let k := ⌊(t : ℝ) / mesh⌋₊
  have hratio : 0 ≤ (t : ℝ) / mesh := div_nonneg t.2 hmesh.le
  have hfloor := Nat.floor_le hratio
  have hceil := Nat.lt_floor_add_one ((t : ℝ) / mesh)
  have hgrid : ((uniformGrid T n k : ℝ≥0) : ℝ) = mesh * (k : ℝ) := by
    simp [uniformGrid, mesh]
  have hkle : k ≤ n + 1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt hratio).2
    rw [div_lt_iff₀ hmesh]
    have hT' : (T : ℝ) = mesh * ((n : ℝ) + 1) := by
      dsimp [mesh]
      field_simp
    push_cast
    have ht' : (t : ℝ) ≤ (T : ℝ) := ht
    linarith [mul_pos hmesh (show (0 : ℝ) < 1 by norm_num)]
  refine ⟨k, hkle, ?_⟩
  rw [NNReal.dist_eq, hgrid, abs_of_nonpos]
  · have hh := (div_lt_iff₀ hmesh).mp hceil
    linarith
  · rw [sub_nonpos, mul_comm]
    exact (le_div_iff₀ hmesh).mp hfloor

/-- A strict violation of the closed interval is detected on all sufficiently fine grids. -/
theorem eventually_exists_uniformGrid_exit {path : ℝ≥0 → ℝ} (hpath : Continuous path)
    {left right : ℝ} {T : ℝ≥0}
    (hexit : ∃ t ≤ T, path t ∉ Icc left right) :
    ∀ᶠ n in atTop, ∃ k ≤ n + 1, path (uniformGrid T n k) ∉ Icc left right := by
  obtain ⟨t, ht, houtside⟩ := hexit
  obtain rfl | hT := eq_or_lt_of_le (show 0 ≤ T from zero_le)
  · have ht' : t = 0 := le_antisymm ht zero_le
    subst t
    exact Eventually.of_forall (fun n ↦ ⟨0, Nat.zero_le _, by simpa using houtside⟩)
  have hopen : IsOpen (path ⁻¹' (Icc left right)ᶜ) :=
    isClosed_Icc.isOpen_compl.preimage hpath
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t houtside
  filter_upwards [(tendsto_uniformGrid_mesh T).eventually (eventually_lt_nhds hε)] with n hn
  obtain ⟨k, hk, hdist⟩ := exists_uniformGrid_close ht hT n
  exact ⟨k, hk, hball (hdist.trans_lt hn)⟩

theorem measurableSet_intervalSurvival {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) (left right : ℝ) (T : ℝ≥0) :
    MeasurableSet (intervalSurvival B left right T) := by
  have heq : intervalSurvival B left right T =
      ⋂ n : ℕ, ⋂ k : ℕ, ⋂ _ : k ≤ n + 1, B (uniformGrid T n k) ⁻¹' Icc left right := by
    ext ω
    simp only [intervalSurvival, mem_setOf_eq, mem_iInter, mem_preimage]
    constructor
    · intro h n k hk
      exact h _ ((monotone_uniformGrid T n hk).trans_eq (uniformGrid_last T n))
    · intro h t ht
      by_contra hn
      obtain ⟨n, k, hk, he⟩ :=
        (eventually_exists_uniformGrid_exit (hc ω) ⟨t, ht, hn⟩).exists
      exact he (h n k hk)
  rw [heq]
  exact MeasurableSet.iInter (fun n ↦ MeasurableSet.iInter (fun k ↦
    MeasurableSet.iInter (fun _ ↦ hm _ measurableSet_Icc)))

/-- A crossing between two successive grid samples has an intermediate boundary point. -/
theorem exists_between_boundary {path : ℝ≥0 → ℝ} (hpath : Continuous path)
    {s t : ℝ≥0} (hst : s ≤ t) {left right : ℝ}
    (hs : path s ∈ Icc left right) (ht : path t ∉ Icc left right) :
    ∃ u ∈ Icc s t, path u = left ∨ path u = right := by
  by_cases h : path t < left
  · obtain ⟨u, hu, huleft⟩ :=
      intermediate_value_Icc' hst hpath.continuousOn ⟨h.le, hs.1⟩
    exact ⟨u, hu, Or.inl huleft⟩
  · have hr : right < path t := lt_of_not_ge (fun h' ↦ ht ⟨le_of_not_gt h, h'⟩)
    obtain ⟨u, hu, huright⟩ :=
      intermediate_value_Icc hst hpath.continuousOn ⟨hs.2, hr.le⟩
    exact ⟨u, hu, Or.inr huright⟩

end Mogulskii
