import Mogulskii.ActionIdentity
import Mogulskii.MeshSlope

open MeasureTheory
open scoped ENNReal BigOperators

namespace Mogulskii

theorem pathRate_gridPolygon_le {d m : ℕ} (hm : 0 < m)
    (I : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (x : Fin m → EuclideanSpace ℝ (Fin d)) :
    pathRate I (gridPolygon m x) ≤
      ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a) := by
  unfold pathRate
  refine (iInf_le _ (polygonVelocity m (extendFin x))).trans ?_
  refine (iInf_le _ (integrable_polygonVelocity m (extendFin x)).integrableOn).trans ?_
  refine (iInf_le _ (fun t => (integral_polygonVelocity hm (extendFin x) t).symm)).trans ?_
  rw [lintegral_polygonVelocity hm, ← Fin.sum_univ_eq_sum_range
    (fun i => ENNReal.ofReal (1 / (m : ℝ)) * I (extendFin x i))]
  simp

/-- The action of each equal-mesh secant approximation is bounded by the path action. -/
theorem imageRate_gridPolygon_meshInterpolate_le {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (hm : 0 < m) (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (φ : WalkPath d) :
    imageRate (gridPolygon m)
      (fun x => ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * cramerRate μ X (x a))
      (meshInterpolate m φ) ≤ pathRate (cramerRate μ X) φ := by
  refine le_trans ?_ (disjointIntervalAction_le_pathRate μ X φ)
  by_cases hφ : disjointIntervalAction (cramerRate μ X) φ = ⊤
  · rw [hφ]
    exact le_top
  have hzero : φ ⟨0, by norm_num⟩ = 0 := finite_disjointIntervalAction_start hφ
  have hstart : φ (meshTime m 0) = 0 := by simpa [meshTime] using hzero
  rw [imageRate_gridPolygon_meshInterpolate φ hstart]
  have hbound := meshAction_le_disjointIntervalAction (cramerRate μ X) φ hzero hm
  rw [lintegral_polygonVelocity hm] at hbound
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ENNReal.ofReal (1 / (m : ℝ)) * cramerRate μ X
      ((m : ℝ) • (φ (meshTime m (i + 1)) - φ (meshTime m i))))] at hbound
  exact hbound

end Mogulskii
