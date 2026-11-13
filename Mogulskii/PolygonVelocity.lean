import Mogulskii.Polygon
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Interval

namespace Mogulskii

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A step-function velocity whose primitive is the polygon. -/
noncomputable def polygonVelocity (m : ℕ) (x : ℕ → E) (s : ℝ) : E :=
  ∑ i ∈ Finset.range m,
    (Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m)).indicator (fun _ => x i) s

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem integrable_step (m i : ℕ) (x : E) :
    Integrable ((Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m)).indicator (fun _ => x)) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact integrableOn_const (by simp [Real.volume_Ioc])

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem integrable_polygonVelocity (m : ℕ) (x : ℕ → E) : Integrable (polygonVelocity m x) := by
  unfold polygonVelocity
  exact integrable_finsetSum _ fun i _ => integrable_step m i (x i)

private theorem measure_step_inter {m : ℕ} (hm : 0 < m) (i : ℕ) (t : UnitTime) :
    volume.real (Ioc (0 : ℝ) (t : ℝ) ∩ Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) =
      (m : ℝ)⁻¹ * ramp m i t := by
  have hm' : (0 : ℝ) < m := by positivity
  rw [Ioc_inter_Ioc, max_eq_right (by positivity), measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal', ← min_sub_sub_right]
  have heq : min (((m : ℝ) * (t : ℝ) - i) / m) (1 / (m : ℝ)) =
      min (1 : ℝ) ((m : ℝ) * (t : ℝ) - i) / m := by
    rw [min_comm, min_div_div_right hm'.le]
  rw [show (t : ℝ) - (i : ℝ) / m = ((m : ℝ) * (t : ℝ) - i) / m by field_simp,
    show ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m by ring, heq]
  rw [← zero_div (m : ℝ), max_comm, max_div_div_right hm'.le]
  simp [ramp, div_eq_mul_inv, mul_comm]

theorem integral_polygonVelocity {m : ℕ} (hm : 0 < m) (x : ℕ → E) (t : UnitTime) :
    (∫ s in (0 : ℝ)..(t : ℝ), polygonVelocity m x s) = polygon m x t := by
  rw [intervalIntegral.integral_of_le t.property.1]
  change (∫ s in Ioc (0 : ℝ) (t : ℝ), ∑ i ∈ Finset.range m,
    (Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m)).indicator (fun _ => x i) s) = _
  rw [integral_finsetSum _ (fun i _ => (integrable_step m i (x i)).integrableOn)]
  change _ = (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, ramp m i t • x i
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc,
    inter_comm, measure_step_inter hm, smul_smul]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem polygonVelocity_eq {m i : ℕ} (hm : 0 < m) (hi : i < m) (x : ℕ → E)
    {s : ℝ} (hs : s ∈ Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m)) :
    polygonVelocity m x s = x i := by
  classical
  unfold polygonVelocity
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hs _
  · intro j hj hji
    have hm' : (0 : ℝ) < m := by positivity
    apply indicator_of_notMem
    intro hs'
    rcases lt_or_gt_of_ne hji with h | h
    · have hh : ((j : ℝ) + 1) / m ≤ (i : ℝ) / m := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast h) hm'.le
      exact (not_lt_of_ge (hs'.2.trans hh)) hs.1
    · have hh : ((i : ℝ) + 1) / m ≤ (j : ℝ) / m := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast h) hm'.le
      exact (not_lt_of_ge (hs.2.trans hh)) hs'.1
  · exact fun h => (h (Finset.mem_range.mpr hi)).elim

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The integral action of the polygonal velocity is the mesh average of the slope costs. -/
theorem lintegral_polygonVelocity {m : ℕ} (hm : 0 < m) (x : ℕ → E) (I : E → ℝ≥0∞) :
    (∫⁻ s in Icc (0 : ℝ) 1, I (polygonVelocity m x s)) =
      ∑ i ∈ Finset.range m, ENNReal.ofReal (1 / (m : ℝ)) * I (x i) := by
  have hm' : (0 : ℝ) < m := by positivity
  have h (k : ℕ) (hk : k ≤ m) :
      (∫⁻ s in Ioc (0 : ℝ) ((k : ℝ) / m), I (polygonVelocity m x s)) =
        ∑ i ∈ Finset.range k, ENNReal.ofReal (1 / (m : ℝ)) * I (x i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hle : (k : ℝ) / m ≤ ((k : ℝ) + 1) / m :=
        div_le_div_of_nonneg_right (by linarith) hm'.le
      have hd : Disjoint (Ioc (0 : ℝ) ((k : ℝ) / m))
          (Ioc ((k : ℝ) / m) (((k : ℝ) + 1) / m)) :=
        Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂.1)
      push_cast
      rw [Finset.sum_range_succ, ← Ioc_union_Ioc_eq_Ioc (by positivity) hle,
        lintegral_union measurableSet_Ioc hd, ih (Nat.le_of_succ_le hk)]
      congr 1
      rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => I (x k))
        (fun _ ht => congrArg I (polygonVelocity_eq hm hk x ht)), setLIntegral_const,
        Real.volume_Ioc, show ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m by ring, mul_comm]
  rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  simpa only [div_self hm'.ne'] using h m le_rfl

end Mogulskii




