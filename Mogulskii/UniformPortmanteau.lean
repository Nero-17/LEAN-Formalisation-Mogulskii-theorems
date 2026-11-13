import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Mogulskii.SmallDeviation

section UniformPortmanteau

variable {E Ω Ω' : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [SeminormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {X : ℕ → Ω → E} {B : Ω' → E}

private theorem shifted_subsequence
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    {u : ℕ → ℕ} (hu : StrictMono u)
    {x : ℕ → E} {a : E} (hx : Tendsto x atTop (𝓝 a)) :
    TendstoInDistribution (fun n ω => X (u n) ω + x n) atTop
      (fun ω => B ω + a) (fun _ => P) Q := by
  have hsub : TendstoInDistribution (fun n => X (u n)) atTop B (fun _ => P) Q :=
    ⟨fun n => h.forall_aemeasurable (u n), h.aemeasurable_limit,
      h.tendsto.comp hu.tendsto_atTop⟩
  have hshift : TendstoInMeasure P (fun n (_ : Ω) => x n) atTop (fun _ => a) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hx))
  exact hsub.add_of_tendstoInMeasure_const hshift (fun _ => aemeasurable_const)

/-- A strict bound on the limiting closed-set probabilities, uniformly for the shifts in a
compact set, becomes an eventual uniform bound on the approximating probabilities. -/
theorem eventually_shift_closed_lt
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    {K F : Set E} (hK : IsCompact K) (hF : IsClosed F) {b : ℝ≥0∞}
    (hb : ∀ x ∈ K, Q {ω | B ω + x ∈ F} < b) :
    ∀ᶠ n in atTop, ∀ x ∈ K, P {ω | X n ω + x ∈ F} < b := by
  classical
  by_contra! hbad
  obtain ⟨u, hu, hbad⟩ := extraction_of_frequently_atTop hbad
  choose x hx hbad using hbad
  obtain ⟨a, ha, v, hv, hconv⟩ := hK.tendsto_subseq hx
  have hs := shifted_subsequence h (hu.comp hv) hconv
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hs.tendsto hF
  change (atTop : Filter ℕ).limsup
      (fun n => (P.map (fun ω => X (u (v n)) ω + x (v n))) F) ≤
    (Q.map (fun ω => B ω + a)) F at hlim
  have hmap : (fun n => (P.map (fun ω => X (u (v n)) ω + x (v n))) F) =
      (fun n => P {ω | X (u (v n)) ω + x (v n) ∈ F}) :=
    funext fun n => Measure.map_apply_of_aemeasurable (hs.forall_aemeasurable n) hF.measurableSet
  rw [hmap, Measure.map_apply_of_aemeasurable hs.aemeasurable_limit hF.measurableSet] at hlim
  have hev := eventually_lt_of_limsup_lt (hlim.trans_lt (hb a ha))
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (hbad (v n))) hn

/-- A strict lower bound on limiting open-set probabilities becomes eventual and uniform on
every compact set of shifts on which the strict lower bound holds. -/
theorem eventually_lt_shift_open
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    {K G : Set E} (hK : IsCompact K) (hG : IsOpen G) {b : ℝ≥0∞}
    (hb : ∀ x ∈ K, b < Q {ω | B ω + x ∈ G}) :
    ∀ᶠ n in atTop, ∀ x ∈ K, b < P {ω | X n ω + x ∈ G} := by
  classical
  by_contra! hbad
  obtain ⟨u, hu, hbad⟩ := extraction_of_frequently_atTop hbad
  choose x hx hbad using hbad
  obtain ⟨a, ha, v, hv, hconv⟩ := hK.tendsto_subseq hx
  have hs := shifted_subsequence h (hu.comp hv) hconv
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hs.tendsto hG
  change (Q.map (fun ω => B ω + a)) G ≤
      (atTop : Filter ℕ).liminf (fun n => (P.map (fun ω => X (u (v n)) ω + x (v n))) G)
      at hlim
  have hmap : (fun n => (P.map (fun ω => X (u (v n)) ω + x (v n))) G) =
      (fun n => P {ω | X (u (v n)) ω + x (v n) ∈ G}) :=
    funext fun n => Measure.map_apply_of_aemeasurable (hs.forall_aemeasurable n) hG.measurableSet
  rw [hmap, Measure.map_apply_of_aemeasurable hs.aemeasurable_limit hG.measurableSet] at hlim
  have hev := eventually_lt_of_lt_liminf ((hb a ha).trans_le hlim)
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (hbad (v n))) hn

end UniformPortmanteau

end Mogulskii.SmallDeviation


namespace Mogulskii.SmallDeviation

/-- Continuous paths confined to a fixed interval, with a separate endpoint constraint. -/
def tube {T : Type*} [TopologicalSpace T] (finish : T) (I J : Set ℝ) :
    Set C(T, ℝ) := {f | Set.range f ⊆ I ∧ f finish ∈ J}

theorem isOpen_tube {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (finish : T) {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J) :
    IsOpen (tube finish I J) :=
  (ContinuousMap.isOpen_setOf_range_subset hI).inter
    (hJ.preimage (continuous_eval_const finish))

theorem isClosed_tube {T : Type*} [TopologicalSpace T]
    (finish : T) {I J : Set ℝ} (hI : IsClosed I) (hJ : IsClosed J) :
    IsClosed (tube finish I J) := by
  have h : IsClosed {f : C(T, ℝ) | Set.range f ⊆ I} := by
    simpa only [Set.mapsTo_univ_iff_range_subset] using
      (ContinuousMap.isClosed_setOf_mapsTo hI (Set.univ : Set T))
  exact h.inter (hJ.preimage (continuous_eval_const finish))

end Mogulskii.SmallDeviation



namespace Mogulskii.SmallDeviation

/-- Real starting positions in a compact set give a compact set of constant paths. -/
theorem isCompact_constant_paths {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {K : Set ℝ} (hK : IsCompact K) :
    IsCompact ((ContinuousMap.const T : ℝ → C(T, ℝ)) '' K) :=
  hK.image ContinuousMap.continuous_const'

end Mogulskii.SmallDeviation



namespace Mogulskii.SmallDeviation

/-- Rescaling the time length of a polygonal block changes the spatial normalization by a
deterministic factor. This version of Slutsky's theorem includes a subsequence of block lengths. -/
theorem tendstoInDistribution_smul_subseq
    {E Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {B : Ω' → E}
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {c : ℕ → ℝ} {a : ℝ} (hc : Tendsto c atTop (𝓝 a)) :
    TendstoInDistribution (fun n ω => c n • X (m n) ω) atTop
      (fun ω => a • B ω) (fun _ => P) Q := by
  have hsub : TendstoInDistribution (fun n => X (m n)) atTop B (fun _ => P) Q :=
    ⟨fun n => h.forall_aemeasurable (m n), h.aemeasurable_limit, h.tendsto.comp hm⟩
  have hscale : TendstoInMeasure P (fun n (_ : Ω) => c n) atTop (fun _ => a) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hc))
  exact hsub.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : E × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst) hscale (fun _ => aemeasurable_const)

end Mogulskii.SmallDeviation


namespace Mogulskii.SmallDeviation

/-- The number of steps in a fixed diffusive time block tends to infinity. -/
theorem tendsto_diffusive_block_size_of_tendsto
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {times : ℕ → ℝ} {time : ℝ} (htimes : Tendsto times atTop (𝓝 time)) (htime : 0 < time) :
    Tendsto (fun n => ⌊times n * scale n ^ 2⌋₊) atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  have hhalf : 0 < time / 2 := by positivity
  filter_upwards [(tendsto_atTop.1 hscale) (max 1 ((N : ℝ) / (time / 2))),
    (tendsto_order.1 htimes).1 (time / 2) (by linarith)] with n hn htn
  have h₁ : 1 ≤ scale n := (le_max_left _ _).trans hn
  have h₂ : (N : ℝ) / (time / 2) ≤ scale n := (le_max_right _ _).trans hn
  have h₃ : (N : ℝ) ≤ times n * scale n ^ 2 := calc
    (N : ℝ) ≤ scale n * (time / 2) := (div_le_iff₀ hhalf).1 h₂
    _ = (time / 2) * scale n := mul_comm _ _
    _ ≤ (time / 2) * scale n ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hhalf.le
      simpa only [one_mul, pow_two] using
        (mul_le_mul_of_nonneg_right h₁ (zero_le_one.trans h₁))
    _ ≤ times n * scale n ^ 2 := mul_le_mul_of_nonneg_right htn.le (sq_nonneg _)
  by_cases hN : N = 0
  · simp [hN]
  · exact (Nat.le_floor_iff' hN).2 h₃

/-- The number of steps in a fixed diffusive time block tends to infinity. -/
theorem tendsto_diffusive_block_size {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {time : ℝ} (htime : 0 < time) :
    Tendsto (fun n => ⌊time * scale n ^ 2⌋₊) atTop atTop :=
  tendsto_diffusive_block_size_of_tendsto hscale tendsto_const_nhds htime

/-- The square root of the integer block length, divided by the spatial scale, converges
to the square root of the block's limiting diffusive time. -/
theorem tendsto_diffusive_block_normalization_of_tendsto
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {times : ℕ → ℝ} {time : ℝ} (htimes : Tendsto times atTop (𝓝 time)) (htime : 0 < time) :
    Tendsto (fun n => Real.sqrt (⌊times n * scale n ^ 2⌋₊ : ℝ) / scale n) atTop
      (𝓝 (Real.sqrt time)) := by
  have hpos : ∀ᶠ n in atTop, 0 < scale n :=
    ((tendsto_atTop.1 hscale) 1).mono fun _ hn => zero_lt_one.trans_le hn
  have htimepos : ∀ᶠ n in atTop, 0 < times n := (tendsto_order.1 htimes).1 0 htime
  have hinv : Tendsto (fun n => (scale n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hscale
  have hsq : Tendsto (fun n => (scale n ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hinv.pow 2
  have hlow : Tendsto (fun n => times n - (scale n ^ 2)⁻¹) atTop (𝓝 time) := by
    simpa using htimes.sub hsq
  have hratio : Tendsto (fun n => (⌊times n * scale n ^ 2⌋₊ : ℝ) / scale n ^ 2) atTop
      (𝓝 time) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow htimes ?_ ?_
    · filter_upwards [hpos] with n hn
      rw [le_div_iff₀ (pow_pos hn _), sub_mul, inv_mul_cancel₀ (pow_ne_zero _ hn.ne')]
      have := Nat.lt_floor_add_one (times n * scale n ^ 2)
      linarith
    · filter_upwards [hpos, htimepos] with n hn htn
      rw [div_le_iff₀ (pow_pos hn _)]
      exact Nat.floor_le (mul_nonneg htn.le (sq_nonneg _))
  apply ((Real.continuous_sqrt.tendsto time).comp hratio).congr'
  filter_upwards [hpos] with n hn
  change Real.sqrt ((⌊times n * scale n ^ 2⌋₊ : ℝ) / scale n ^ 2) =
    Real.sqrt (⌊times n * scale n ^ 2⌋₊ : ℝ) / scale n
  rw [Real.sqrt_div (Nat.cast_nonneg _) _, Real.sqrt_sq_eq_abs, abs_of_pos hn]

/-- The square root of a fixed diffusive block length divided by the spatial scale. -/
theorem tendsto_diffusive_block_normalization
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {time : ℝ} (htime : 0 < time) :
    Tendsto (fun n => Real.sqrt (⌊time * scale n ^ 2⌋₊ : ℝ) / scale n) atTop
      (𝓝 (Real.sqrt time)) :=
  tendsto_diffusive_block_normalization_of_tendsto hscale tendsto_const_nhds htime

end Mogulskii.SmallDeviation


namespace Mogulskii.SmallDeviation

section PathTransfer

variable {T Ω Ω' : Type*} [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [SecondCountableTopology C(T, ℝ)] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {X : ℕ → Ω → C(T, ℝ)} {B : Ω' → C(T, ℝ)}

/-- A compact set of real starts admits uniform upper bounds for closed tubes. -/
theorem eventually_closed_tube_lt
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    (finish : T) {K I J : Set ℝ}
    (hK : IsCompact K) (hI : IsClosed I) (hJ : IsClosed J) {b : ℝ≥0∞}
    (hb : ∀ x ∈ K, Q {ω | (∀ t, B ω t + x ∈ I) ∧ B ω finish + x ∈ J} < b) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      P {ω | (∀ t, X n ω t + x ∈ I) ∧ X n ω finish + x ∈ J} < b := by
  have he := eventually_shift_closed_lt h (isCompact_constant_paths (T := T) hK)
    (isClosed_tube finish hI hJ) (b := b) (by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [tube, Set.mem_setOf_eq, Set.range_subset_iff, ContinuousMap.add_apply,
        ContinuousMap.const_apply] using hb x hx)
  filter_upwards [he] with n hn x hx
  simpa only [tube, Set.mem_setOf_eq, Set.range_subset_iff, ContinuousMap.add_apply,
    ContinuousMap.const_apply] using hn (ContinuousMap.const T x) ⟨x, hx, rfl⟩

/-- A compact set of real starts admits uniform lower bounds for open tubes. -/
theorem eventually_lt_open_tube
    (h : TendstoInDistribution X atTop B (fun _ => P) Q)
    (finish : T) {K I J : Set ℝ}
    (hK : IsCompact K) (hI : IsOpen I) (hJ : IsOpen J) {b : ℝ≥0∞}
    (hb : ∀ x ∈ K, b < Q {ω | (∀ t, B ω t + x ∈ I) ∧ B ω finish + x ∈ J}) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      b < P {ω | (∀ t, X n ω t + x ∈ I) ∧ X n ω finish + x ∈ J} := by
  have he := eventually_lt_shift_open h (isCompact_constant_paths (T := T) hK)
    (isOpen_tube finish hI hJ) (b := b) (by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [tube, Set.mem_setOf_eq, Set.range_subset_iff, ContinuousMap.add_apply,
        ContinuousMap.const_apply] using hb x hx)
  filter_upwards [he] with n hn x hx
  simpa only [tube, Set.mem_setOf_eq, Set.range_subset_iff, ContinuousMap.add_apply,
    ContinuousMap.const_apply] using hn (ContinuousMap.const T x) ⟨x, hx, rfl⟩

end PathTransfer

end Mogulskii.SmallDeviation

namespace Mogulskii.SmallDeviation

/-- The vertex times for an (m)-step polygonal path on the unit interval. -/
noncomputable def gridTime (m : ℕ) (k : Fin (m + 1)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(k.val : ℝ) / (m : ℝ), div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), by
    by_cases hm : m = 0
    · simp [hm]
    · have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
      exact (div_le_iff₀ hm').2 (by
        simpa only [one_mul, Nat.cast_le] using Nat.le_of_lt_succ k.isLt)⟩

/-- The unit interval's right endpoint is the final vertex of every nonempty grid. -/
theorem gridTime_last {m : ℕ} (hm : m ≠ 0) :
    gridTime m (Fin.last m) = (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) := by
  apply Subtype.ext
  change (m : ℝ) / (m : ℝ) = 1
  exact div_self (Nat.cast_ne_zero.mpr hm)

private theorem convexComb_mem_Icc {a b x y θ : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - θ) * x + θ * y ∈ Set.Icc a b := by
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  constructor
  · calc
      a = (1 - θ) * a + θ * a := by ring
      _ ≤ (1 - θ) * x + θ * y :=
        add_le_add (mul_le_mul_of_nonneg_left hx.1 hθ') (mul_le_mul_of_nonneg_left hy.1 hθ.1)
  · calc
      (1 - θ) * x + θ * y ≤ (1 - θ) * b + θ * b :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 hθ') (mul_le_mul_of_nonneg_left hy.2 hθ.1)
      _ = b := by ring

private theorem convexComb_mem_Ioo {a b x y θ : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - θ) * x + θ * y ∈ Set.Ioo a b := by
  by_cases h : θ = 0
  · simpa [h] using hx
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h)
  constructor
  · calc
      a = (1 - θ) * a + θ * a := by ring
      _ < (1 - θ) * x + θ * y :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.1.le hθ')
          (mul_lt_mul_of_pos_left hy.1 hθpos)
  · calc
      (1 - θ) * x + θ * y < (1 - θ) * b + θ * b :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.2.le hθ')
          (mul_lt_mul_of_pos_left hy.2 hθpos)
      _ = b := by ring

/-- Fixed closed-interval confinement of a polygonal path is equivalent to confinement
at its vertices. A constant shift may be added before testing confinement. -/
theorem polygonal_mem_Icc_iff_grid
    {m : ℕ} {f : Set.Icc (0 : ℝ) 1 → ℝ}
    (h : ∀ t, ∃ i j : Fin (m + 1), ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      f t = (1 - θ) * f (gridTime m i) + θ * f (gridTime m j))
    (x a b : ℝ) :
    (∀ t, f t + x ∈ Set.Icc a b) ↔ ∀ k, f (gridTime m k) + x ∈ Set.Icc a b := by
  constructor
  · intro hall k
    exact hall (gridTime m k)
  · intro hgrid t
    obtain ⟨i, j, θ, hθ, ht⟩ := h t
    rw [ht, show (1 - θ) * f (gridTime m i) + θ * f (gridTime m j) + x =
      (1 - θ) * (f (gridTime m i) + x) + θ * (f (gridTime m j) + x) by ring]
    exact convexComb_mem_Icc (hgrid i) (hgrid j) hθ

/-- Fixed open-interval confinement of a polygonal path is equivalent to confinement
at its vertices. -/
theorem polygonal_mem_Ioo_iff_grid
    {m : ℕ} {f : Set.Icc (0 : ℝ) 1 → ℝ}
    (h : ∀ t, ∃ i j : Fin (m + 1), ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      f t = (1 - θ) * f (gridTime m i) + θ * f (gridTime m j))
    (x a b : ℝ) :
    (∀ t, f t + x ∈ Set.Ioo a b) ↔ ∀ k, f (gridTime m k) + x ∈ Set.Ioo a b := by
  constructor
  · intro hall k
    exact hall (gridTime m k)
  · intro hgrid t
    obtain ⟨i, j, θ, hθ, ht⟩ := h t
    rw [ht, show (1 - θ) * f (gridTime m i) + θ * f (gridTime m j) + x =
      (1 - θ) * (f (gridTime m i) + x) + θ * (f (gridTime m j) + x) by ring]
    exact convexComb_mem_Ioo (hgrid i) (hgrid j) hθ

end Mogulskii.SmallDeviation


