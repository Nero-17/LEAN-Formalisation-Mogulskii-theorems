import Mogulskii.BlockTail
import Mogulskii.GridError
import Mogulskii.PathApproximation

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace Mogulskii

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : ℕ → Ω → E}

/-- The random polygon and its block-average approximation are exponentially close as the
mesh is refined. -/
theorem eventually_measure_dist_gridPolygon_le
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hId : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hExp : ∀ t ≥ 0, ∀ i, Integrable (fun ω => Real.exp (t * ‖X i ω‖)) μ)
    {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      μ {ω | δ < dist (polygon n (fun i => X i ω))
        (gridPolygon m (gridAverages X n m ω))} ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  let blocks := fun m => if 0 < m then Finset.range m else ∅
  have hblocks : ∀ m n j, j ∈ blocks m → ((meshBlock m n j).card : ℝ) ≤
      (n : ℝ) / m + 2 := by
    intro m n j hj
    by_cases hm : 0 < m
    · exact card_meshBlock hm n j
    · simp [blocks, hm] at hj
  have hnorm : Measurable (norm : E → ℝ) := continuous_norm.measurable
  have ht :=
    eventually_measure_block_union_le (X := fun i ω => ‖X i ω‖)
      blocks meshBlock (fun i => hnorm.comp (hX i))
      (hInd.comp (fun _ => norm) (fun _ => hnorm))
      (fun i => (hId i).comp hnorm) hExp hblocks (half_pos hδ) r
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  filter_upwards [hm, eventually_ge_atTop (m * (m + 1))] with n hn hnsize
  refine (measure_mono ?_).trans hn
  intro ω hω
  by_contra hnmem
  have hsmall : ∀ k < m, ∑ i ∈ meshBlock m n k, ‖X i ω‖ ≤ (n : ℝ) * (δ / 2) := by
    intro k hk
    apply le_of_not_gt
    intro h
    apply hnmem
    exact Set.mem_iUnion₂.mpr ⟨k, by simpa [blocks, hmpos] using hk, h.le⟩
  exact (not_le_of_gt hω) (dist_polygon_gridPolygon_le hmpos hnsize X ω hδ.le hsmall)

variable [ProperSpace E] [MeasurableSpace C(UnitTime, E)] [BorelSpace C(UnitTime, E)]
  {ν : Measure E} [IsProbabilityMeasure ν]

/-- The path-space LDP follows from the sample-mean LDP and an action with the finite-grid
cost comparison and recovery inequalities. -/
theorem hasExponentialBounds_polygon_of_mean
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hν : ∀ i, μ.map (X i) = ν)
    (hExp : ∀ t ≥ 0, ∀ i, Integrable (fun ω => Real.exp (t * ‖X i ω‖)) μ)
    {I : E → ℝ≥0∞} (hmean : HasExponentialBounds (meanLaw ν) I)
    {J : C(UnitTime, E) → ℝ≥0∞} (hJ : GoodRate J)
    (hdom : ∀ m > 0, ∀ x : Fin m → E,
      J (gridPolygon m x) ≤ ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a))
    (hcost : ∀ m > 0, ∀ φ : C(UnitTime, E),
      imageRate (gridPolygon m)
        (fun x => ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a))
        (meshInterpolate m φ) ≤ J φ) :
    HasExponentialBounds (fun n => μ.map (fun ω => polygon n (fun i => X i ω))) J := by
  let K := fun m => imageRate (gridPolygon m)
    (fun x => ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a))
  refine hasExponentialBounds_of_approximation
    (X := fun n ω => polygon n (fun i => X i ω))
    (Y := fun m n ω => gridPolygon m (gridAverages X n m ω))
    (J := K) (π := meshInterpolate)
    (fun n => (continuous_polygon n).measurable.comp (measurable_pi_lambda _ hX))
    (fun m n => (continuous_gridPolygon m).measurable.comp (measurable_gridAverages hX n m))
    hJ (fun m hm => hasExponentialBounds_gridPolygon hInd hX hν hmean hm)
    ?_ tendsto_meshInterpolate hcost ?_
  · intro m hm φ
    by_cases hφ : φ ∈ range (gridPolygon m)
    · obtain ⟨x, rfl⟩ := hφ
      rw [show K m (gridPolygon m x) = ∑ a : Fin m, ENNReal.ofReal (1 / (m : ℝ)) * I (x a) by
        exact imageRate_apply (gridPolygon_injective m) _ x]
      exact hdom m hm x
    · simpa only [K, imageRate_eq_top hφ] using (show J φ ≤ ⊤ from le_top)
  · exact fun δ hδ r =>
      eventually_measure_dist_gridPolygon_le hX hInd
        (fun i => ⟨(hX i).aemeasurable, (hX 0).aemeasurable, (hν i).trans (hν 0).symm⟩)
        hExp hδ r

end Mogulskii

