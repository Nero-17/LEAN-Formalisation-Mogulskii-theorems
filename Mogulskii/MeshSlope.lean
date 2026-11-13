import Mogulskii.GridPolygon

open Set
open scoped BigOperators ENNReal

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vector of slopes of the secants between successive mesh points. -/
noncomputable def meshSlope (m : ℕ) (φ : C(UnitTime, E)) (a : Fin m) : E :=
  (m : ℝ) • (φ (meshTime m (a.val + 1)) - φ (meshTime m a.val))

theorem meshInterpolate_eq_gridPolygon {m : ℕ} (φ : C(UnitTime, E))
    (hφ : φ (meshTime m 0) = 0) :
    meshInterpolate m φ = gridPolygon m (meshSlope m φ) := by
  ext t
  simp only [meshInterpolate, ContinuousMap.add_apply, ContinuousMap.const_apply, hφ, zero_add,
    gridPolygon]
  change (m : ℝ)⁻¹ • (∑ i ∈ Finset.range m,
    ramp m i t • ((m : ℝ) • (φ (meshTime m (i + 1)) - φ (meshTime m i)))) =
    (m : ℝ)⁻¹ • (∑ i ∈ Finset.range m, ramp m i t • extendFin (meshSlope m φ) i)
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show extendFin (meshSlope m φ) i = meshSlope m φ ⟨i, Finset.mem_range.mp hi⟩ from
    dif_pos (Finset.mem_range.mp hi)]
  rfl

theorem imageRate_gridPolygon_meshInterpolate {m : ℕ} (φ : C(UnitTime, E))
    (hφ : φ (meshTime m 0) = 0) (I : E → ℝ≥0∞) :
    imageRate (gridPolygon m)
      (fun x => ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a))
      (meshInterpolate m φ) =
      ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (meshSlope m φ a) := by
  rw [meshInterpolate_eq_gridPolygon φ hφ, imageRate_apply (gridPolygon_injective m)]

end Mogulskii
