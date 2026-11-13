import Mogulskii.BalancedBlocks
import Mogulskii.SingleBlockBounds
import Mogulskii.MovingTube
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology

namespace Mogulskii.SmallDeviation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A constant exponential estimate on each block becomes the exponential
estimate with the sum of the block exponents. -/
theorem prod_const_exp_blocks (m : ℕ) (r T : ℝ) :
    (∏ _j ∈ Finset.range m, ENNReal.ofReal (Real.exp (-r * T))) =
      ENNReal.ofReal (Real.exp (-r * ((m : ℝ) * T))) := by
  rw [Finset.prod_const, Finset.card_range, ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← Real.exp_nat_mul]
  rw [show (m : ℝ) * (-r * T) = -r * ((m : ℝ) * T) by ring]

/-- Concatenate lower estimates with a fixed terminal window at every block boundary. -/
theorem measure_balanced_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (N m : ℕ) (hm : 0 < m) (x l u lo hi : ℝ) (p : ℝ≥0∞)
    (h : ∀ L : ℕ, (L = N / m ∨ L = N / m + 1) →
      ∀ y : ℝ, (y = x ∨ y ∈ Icc lo hi) →
        p ≤ μ (endpointTube X L y (fun _ => l) (fun _ => u) (Icc lo hi))) :
    p ^ m ≤ μ (endpointTube X N x (fun _ => l) (fun _ => u) (Icc lo hi)) := by
  let time := balancedCut N m
  let endpoint (j : ℕ) := if j = 0 then {x} else Icc lo hi
  have he (j : ℕ) : MeasurableSet (endpoint j) := by
    unfold endpoint
    split
    · exact measurableSet_singleton _
    · exact measurableSet_Icc
  have hx : x ∈ endpoint 0 := by simp [endpoint]
  have hprob (j : ℕ) (hj : j < m) (y : ℝ) (hy : y ∈ endpoint j) :
      p ≤ μ (endpointTube X (time (j + 1) - time j) y
        (fun _ => l) (fun _ => u) (endpoint (j + 1))) ∧
      μ (endpointTube X (time (j + 1) - time j) y
        (fun _ => l) (fun _ => u) (endpoint (j + 1))) ≤ 1 := by
    rw [show endpoint (j + 1) = Icc lo hi by simp [endpoint]]
    refine ⟨h _ ?_ y ?_, prob_le_one⟩
    · change balancedCut N m (j + 1) - balancedCut N m j = _ ∨ _
      rw [balancedCut_succ]
      split <;> simp
    · by_cases hj' : j = 0
      · exact Or.inl (by simpa [endpoint, hj'] using hy)
      · exact Or.inr (by simpa [endpoint, hj'] using hy)
  have hbound := (measure_partitionTube_bounds hX hind hid x (balancedCut_mono N m)
    (balancedCut_zero N m) (fun _ _ => l) (fun _ _ => u) he hx (fun _ => p) (fun _ => 1) m
    (fun j hj y hy => hprob j hj y hy)).1
  rw [Finset.prod_const, Finset.card_range] at hbound
  refine hbound.trans (measure_mono fun ω hω => ?_)
  have ht : balancedCut N m m = N := balancedCut_end N m hm
  have hEnd := mem_endpoint_of_mem_partitionTube (balancedCut_mono N m)
    (balancedCut_zero N m) hω
  have hTube := partitionTube_subset_tubeEvent (balancedCut_mono N m) (balancedCut_zero N m)
    hm (f := fun _ => l) (g := fun _ => u) (fun _ _ _ _ => ⟨le_rfl, le_rfl⟩) hω
  have hEnd' : x + walk X N ω ∈ Icc lo hi := by
    simpa only [ht, endpoint, Nat.ne_of_gt hm, if_false] using hEnd
  exact ⟨by simpa only [ht] using hTube, hEnd'⟩

/-- Concatenate upper estimates that hold for every starting position. -/
theorem measure_balanced_upper {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (N m : ℕ) (hm : 0 < m) (x l u : ℝ) (q : ℝ≥0∞)
    (h : ∀ L : ℕ, (L = N / m ∨ L = N / m + 1) →
      ∀ y : ℝ, μ (tubeEvent X L y (fun _ => l) (fun _ => u)) ≤ q) :
    μ (tubeEvent X N x (fun _ => l) (fun _ => u)) ≤ q ^ m := by
  let time := balancedCut N m
  let endpoint (_j : ℕ) := (univ : Set ℝ)
  have hprob (j : ℕ) (hj : j < m) (y : ℝ) (_hy : y ∈ endpoint j) :
      (0 : ℝ≥0∞) ≤ μ (endpointTube X (time (j + 1) - time j) y
        (fun _ => l) (fun _ => u) (endpoint (j + 1))) ∧
      μ (endpointTube X (time (j + 1) - time j) y
        (fun _ => l) (fun _ => u) (endpoint (j + 1))) ≤ q := by
    refine ⟨zero_le, ?_⟩
    apply (measure_mono (show endpointTube X _ y _ _ _ ⊆ tubeEvent X _ y _ _ from
      inter_subset_left)).trans
    apply h
    change balancedCut N m (j + 1) - balancedCut N m j = _ ∨ _
    rw [balancedCut_succ]
    split <;> simp
  have hbound := (measure_partitionTube_bounds hX hind hid x (balancedCut_mono N m)
    (balancedCut_zero N m) (fun _ _ => l) (fun _ _ => u)
    (show ∀ j, MeasurableSet (endpoint j) from fun _ => MeasurableSet.univ)
    (mem_univ x) (fun _ => 0) (fun _ => q) m hprob).2
  rw [Finset.prod_const, Finset.card_range] at hbound
  apply le_trans (measure_mono ?_) hbound
  have ht : balancedCut N m m = N := balancedCut_end N m hm
  simpa only [ht] using
    (tubeEvent_subset_partitionTube (X := X) (x := x) (count := m)
      (lower := fun _ _ => l) (upper := fun _ _ => u) (f := fun _ => l) (g := fun _ => u)
      (balancedCut_mono N m) (fun _ _ _ _ => ⟨le_rfl, le_rfl⟩))

/-- A positive limiting proportion of the walk contains a divergent number
of steps on the scale of one diffusive block. -/
theorem tendsto_length_div_diffusive {a : ℕ → ℝ} {length : ℕ → ℕ} {δ : ℝ}
    (ha : ∀ n, 0 < a n) (hδ : 0 < δ)
    (hscale : Tendsto (fun n : ℕ => a n ^ 2 / (n : ℝ)) atTop (𝓝 0))
    (hlen : Tendsto (fun n : ℕ => (length n : ℝ) / n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => (length n : ℝ) / a n ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro r
  let bound := max r 1
  have hbound : 0 < bound := zero_lt_one.trans_le (le_max_right _ _)
  filter_upwards [(tendsto_order.1 hlen).1 (δ / 2) (by linarith),
    (tendsto_order.1 hscale).2 (δ / (2 * bound)) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hsn hn'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hapos : 0 < a n ^ 2 := pow_pos (ha n) 2
  have hstep : bound * (a n ^ 2 / n) < δ / 2 := by
    have hb := (lt_div_iff₀ (show 0 < 2 * bound by positivity)).mp hsn
    rw [show a n ^ 2 / (n : ℝ) * (2 * bound) = 2 * (bound * (a n ^ 2 / n)) by ring] at hb
    linarith
  apply (le_max_left r 1).trans
  apply (le_div_iff₀ hapos).2
  have hi := (div_lt_div_iff_of_pos_right hnpos).mp
    (show (bound * a n ^ 2) / (n : ℝ) < (length n : ℝ) / n by
      rw [mul_div_assoc]
      exact hstep.trans hn)
  exact hi.le

/-- Convergence of the scaled block count converts a fixed error in the
single-block exponent into any prescribed error in the rectangle exponent. -/
theorem eventually_repeated_exponent {a : ℕ → ℝ} {length : ℕ → ℕ}
    {δ T rate η ε : ℝ} (ha : ∀ n, 0 < a n) (hT : 0 < T)
    (hquot : Tendsto (fun n => (length n : ℝ) / a n ^ 2) atTop atTop)
    (hlen : Tendsto (fun n => (length n : ℝ) / (n : ℝ)) atTop (𝓝 δ))
    (hupper : (rate + η) * δ < δ * rate + ε)
    (hlower : δ * rate - ε < (rate - η) * δ) :
    let count := fun n => ⌊((length n : ℝ) / a n ^ 2) / T⌋₊
    ∀ᶠ n : ℕ in atTop,
      (rate + η) * ((count n : ℝ) * T) ≤ (δ * rate + ε) * ((n : ℝ) / a n ^ 2) ∧
      (δ * rate - ε) * ((n : ℝ) / a n ^ 2) ≤ (rate - η) * ((count n : ℝ) * T) := by
  let count := fun n => ⌊((length n : ℝ) / a n ^ 2) / T⌋₊
  have hcount : Tendsto (fun n => (count n : ℝ) * T * (a n ^ 2 / (n : ℝ)))
      atTop (𝓝 δ) := tendsto_balanced_count_mul hT hquot hlen
  have hlo := (tendsto_order.1 ((tendsto_const_nhds (x := rate - η)).mul hcount)).1 _ hlower
  have hhi := (tendsto_order.1 ((tendsto_const_nhds (x := rate + η)).mul hcount)).2 _ hupper
  filter_upwards [hlo, hhi, eventually_ge_atTop (1 : ℕ)] with n hln hhn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hspeed : 0 < (n : ℝ) / a n ^ 2 := div_pos hn' (pow_pos (ha n) 2)
  have hcancel : a n ^ 2 / (n : ℝ) * ((n : ℝ) / a n ^ 2) = 1 := by
    field_simp [hn'.ne', (ha n).ne']
  have hln' := mul_le_mul_of_nonneg_right hln.le hspeed.le
  have hhn' := mul_le_mul_of_nonneg_right hhn.le hspeed.le
  simpa only [mul_assoc, hcancel, mul_one] using And.intro hhn' hln'

theorem rectangularBounds_of_singleBlockBounds
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (haInf : Tendsto (fun n => a n ^ 2) atTop atTop)
    (haZero : Tendsto (fun n : ℕ => a n ^ 2 / (n : ℝ)) atTop (𝓝 0))
    (C : ℝ) (hLower : SingleBlockLower μ X a C) (hUpper : SingleBlockUpper μ X a C) :
    RectangularLower μ X a C ∧ RectangularUpper μ X a C := by
  constructor
  · intro length δ l u startLo startHi endLo endHi hδ hsl hss hsu hel hee heu hlen ε hε
    let η := ε / (2 * δ)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηδ : η * δ = ε / 2 := by
      dsimp [η]
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hδ.ne']
    have hquot := tendsto_length_div_diffusive ha hδ haZero hlen
    obtain ⟨T, hT, hTLower⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (hLower l u (min startLo endLo) (max startHi endHi) endLo endHi
        (lt_min hsl hel)
        ((min_le_left _ _).trans (hss.trans (le_max_left _ _)))
        (max_lt hsu heu) hel hee heu η hη)).exists
    let count := fun n => ⌊((length n : ℝ) / a n ^ 2) / T⌋₊
    obtain ⟨hcount, hlen₀, hlen₁⟩ := tendsto_balanced_at_diffusive_scale haInf hT hquot
    let rate := C / (u - l) ^ 2
    have hbounds := eventually_repeated_exponent ha hT hquot hlen (rate := rate) (η := η) (ε := ε)
      (by rw [add_mul, hηδ]; linarith) (by rw [sub_mul, hηδ]; linarith)
    filter_upwards [hcount, hTLower (fun n => length n / count n) hlen₀,
      hTLower (fun n => length n / count n + 1) hlen₁, hbounds] with n hn hc₀ hc₁ hb
    intro x hx
    have hp := measure_balanced_lower hX hind hid (length n) (count n) hn x (a n * l) (a n * u)
      (a n * endLo) (a n * endHi) (ENNReal.ofReal (Real.exp (-(rate + η) * T))) (by
        intro L hL y hy
        have hy' : y ∈ Icc (a n * min startLo endLo) (a n * max startHi endHi) := by
          rcases hy with rfl | hy
          · exact ⟨(mul_le_mul_of_nonneg_left (min_le_left _ _) (ha n).le).trans hx.1,
              hx.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (ha n).le)⟩
          · exact ⟨(mul_le_mul_of_nonneg_left (min_le_right _ _) (ha n).le).trans hy.1,
              hy.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (ha n).le)⟩
        rcases hL with rfl | rfl
        · exact hc₀ y hy'
        · exact hc₁ y hy')
    rw [← Finset.card_range (count n), ← Finset.prod_const, prod_const_exp_blocks] at hp
    exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      simpa only [neg_mul] using neg_le_neg hb.1))).trans hp
  · intro length δ l u hδ hlu hlen ε hε
    let η := ε / (2 * δ)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηδ : η * δ = ε / 2 := by
      dsimp [η]
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hδ.ne']
    have hquot := tendsto_length_div_diffusive ha hδ haZero hlen
    obtain ⟨T, hT, hTUpper⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (hUpper l u hlu η hη)).exists
    let count := fun n => ⌊((length n : ℝ) / a n ^ 2) / T⌋₊
    obtain ⟨hcount, hlen₀, hlen₁⟩ := tendsto_balanced_at_diffusive_scale haInf hT hquot
    let rate := C / (u - l) ^ 2
    have hbounds := eventually_repeated_exponent ha hT hquot hlen (rate := rate) (η := η) (ε := ε)
      (by rw [add_mul, hηδ]; linarith) (by rw [sub_mul, hηδ]; linarith)
    filter_upwards [hcount, hTUpper (fun n => length n / count n) hlen₀,
      hTUpper (fun n => length n / count n + 1) hlen₁, hbounds] with n hn hc₀ hc₁ hb
    intro x
    have hq := measure_balanced_upper hX hind hid (length n) (count n) hn x (a n * l) (a n * u)
      (ENNReal.ofReal (Real.exp (-(rate - η) * T))) (by
        intro L hL y
        rcases hL with rfl | rfl
        · exact hc₀ y
        · exact hc₁ y)
    rw [← Finset.card_range (count n), ← Finset.prod_const, prod_const_exp_blocks] at hq
    exact hq.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      simpa only [neg_mul] using neg_le_neg hb.2)))

end Mogulskii.SmallDeviation
