import Mogulskii.GridBlocks
import Mogulskii.InjectiveContraction
import Mogulskii.Polygon

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extend a finite vector of increments by zero. -/
def extendFin {m : ℕ} (x : Fin m → E) (i : ℕ) : E :=
  if hi : i < m then x ⟨i, hi⟩ else 0

@[simp] theorem extendFin_val {m : ℕ} (x : Fin m → E) (i : Fin m) :
    extendFin x i.val = x i := dif_pos i.isLt

theorem continuous_extendFin (m : ℕ) : Continuous (extendFin (E := E) (m := m)) := by
  apply continuous_pi
  intro i
  by_cases hi : i < m
  · simpa only [extendFin, dif_pos hi] using (continuous_apply (⟨i, hi⟩ : Fin m)
      : Continuous fun x : Fin m → E ↦ x ⟨i, hi⟩)
  · simpa only [extendFin, dif_neg hi] using
      (continuous_const : Continuous fun _ : Fin m → E ↦ (0 : E))

/-- Polygonal interpolation on a fixed finite grid, with the input as its slopes. -/
noncomputable def gridPolygon (m : ℕ) (x : Fin m → E) : C(UnitTime, E) :=
  polygon m (extendFin x)

theorem continuous_gridPolygon (m : ℕ) : Continuous (gridPolygon (E := E) m) :=
  (continuous_polygon m).comp (continuous_extendFin m)

theorem gridPolygon_injective (m : ℕ) : Function.Injective (gridPolygon (E := E) m) := by
  intro x y hxy
  funext i
  have hm : m ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h_mesh (k : ℕ) (hk : k ≤ m) :
      ∑ j ∈ Finset.range k, extendFin x j = ∑ j ∈ Finset.range k, extendFin y j := by
    have h := congrArg (fun φ : C(UnitTime, E) ↦ φ (meshTime m k)) hxy
    change polygon m (extendFin x) (meshTime m k) =
      polygon m (extendFin y) (meshTime m k) at h
    have heq : (meshTime m k : ℝ) = (k : ℝ) / m := coe_meshTime hk
    have hpoint : meshTime m k = ⟨(k : ℝ) / m, by rw [← heq]; exact (meshTime m k).property⟩ :=
      Subtype.ext heq
    rw [hpoint, polygon_mesh _ _ hk hm, polygon_mesh _ _ hk hm] at h
    exact (smul_right_injective E (inv_ne_zero hmR)) h
  have hs := h_mesh (i.val + 1) i.isLt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, h_mesh i.val i.isLt.le,
    extendFin_val x i, extendFin_val y i] at hs
  exact add_left_cancel hs

variable {Ω : Type*} [MeasurableSpace Ω] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(UnitTime, E)] [BorelSpace C(UnitTime, E)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure E} [IsProbabilityMeasure ν]

/-- The fixed-grid approximation to the random walk has the finite-grid rate on its
polygonal image and infinite rate elsewhere. -/
theorem hasExponentialBounds_gridPolygon {X : ℕ → Ω → E} {I : E → ℝ≥0∞}
    (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hν : ∀ i, μ.map (X i) = ν)
    (hmean : HasExponentialBounds (meanLaw ν) I) {m : ℕ} (hmpos : 0 < m) :
    HasExponentialBounds (fun n ↦ μ.map (gridPolygon m ∘ gridAverages X n m))
      (imageRate (gridPolygon m)
        (fun x ↦ ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a))) := by
  have h := (hasExponentialBounds_gridAverages hX hm hν hmean hmpos).map_injective
    (continuous_gridPolygon m) (gridPolygon_injective m)
  simpa only [Measure.map_map (continuous_gridPolygon m).measurable
    (measurable_gridAverages hm _ _)] using h

end Mogulskii

