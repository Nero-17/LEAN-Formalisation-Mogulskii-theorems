import Mogulskii.UniformPortmanteau
import MathlibExt.Probability.PolygonalProcess
import Mathlib.Tactic.FieldSimp

open Filter MeasureTheory Set Topology
open scoped ENNReal
open MathlibExt.Probability.DonskerWanted

namespace Mogulskii.SmallDeviation

local notation "UnitInterval" => Set.Icc (0 : ℝ) 1
/-- The right endpoint of the time interval used for a normalized block. -/
def unitRightEndpoint : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

/-- The path normalized by the prescribed spatial scale. -/
noncomputable def scaledBlockPath {Ω : Type*} (m : ℕ) (scale : ℝ)
    (X : ℕ → Ω → ℝ) (ω : Ω) : C(UnitInterval, ℝ) :=
  (Real.sqrt (m : ℝ) / scale) • donskerProcess m X ω

theorem scaledBlockPath_apply_grid {Ω : Type*} {m : ℕ} (hm : m ≠ 0) (scale : ℝ)
    (X : ℕ → Ω → ℝ) (ω : Ω) (k : Fin (m + 1)) :
    scaledBlockPath m scale X ω (gridTime m k) =
      (∑ i ∈ Finset.range k.val, X i ω) / scale := by
  have hcast : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hgrid : (m : ℝ) * (gridTime m k).val = (k.val : ℝ) := by
    change (m : ℝ) * ((k.val : ℝ) / m) = (k.val : ℝ)
    field_simp
  have hterm : (if k.val < m then X k.val ω * ((k.val : ℝ) - k.val) else 0) = 0 := by
    split <;> simp
  simp only [scaledBlockPath, ContinuousMap.smul_apply, smul_eq_mul]
  rw [donskerProcess_apply_eq _ _ _ _ hm, hgrid, Nat.floor_natCast, hterm, add_zero]
  by_cases hs : scale = 0
  · simp [hs]
  · field_simp [Real.sqrt_ne_zero'.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))]

private theorem scaledBlockPath_convex {Ω : Type*} {m : ℕ} (hm : m ≠ 0) (scale : ℝ)
    (X : ℕ → Ω → ℝ) (ω : Ω) (t : UnitInterval) :
    ∃ i j : Fin (m + 1), ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      scaledBlockPath m scale X ω t =
        (1 - θ) * scaledBlockPath m scale X ω (gridTime m i) +
          θ * scaledBlockPath m scale X ω (gridTime m j) := by
  let k := ⌊(m : ℝ) * t.val⌋₊
  let θ := (m : ℝ) * t.val - k
  have hnonneg : 0 ≤ (m : ℝ) * t.val := mul_nonneg (Nat.cast_nonneg _) t.2.1
  have hk : k ≤ m := Nat.floor_le_of_le (by
    simpa using mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg m))
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Nat.zero_le_self_sub_floor hnonneg, (Nat.self_sub_floor_lt_one _).le⟩
  have hvalue :
      scaledBlockPath m scale X ω t =
        ((∑ i ∈ Finset.range k, X i ω) + if k < m then X k ω * θ else 0) / scale := by
    simp only [scaledBlockPath, ContinuousMap.smul_apply, smul_eq_mul]
    rw [donskerProcess_apply_eq _ _ _ _ hm]
    change Real.sqrt (m : ℝ) / scale *
      (((∑ i ∈ Finset.range k, X i ω) + if k < m then X k ω * θ else 0) /
        Real.sqrt (m : ℝ)) = _
    by_cases hs : scale = 0
    · simp [hs]
    · field_simp [Real.sqrt_ne_zero'.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))]
  by_cases hkm : k < m
  · refine ⟨⟨k, by omega⟩, ⟨k + 1, by omega⟩, θ, hθ, ?_⟩
    rw [hvalue, if_pos hkm, scaledBlockPath_apply_grid hm, scaledBlockPath_apply_grid hm]
    simp only [Finset.sum_range_succ]
    ring
  · refine ⟨⟨k, by omega⟩, ⟨k, by omega⟩, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp [hvalue, hkm, scaledBlockPath_apply_grid hm]

private theorem endpoint_eq_scaled_sum {Ω : Type*} {m : ℕ} (hm : m ≠ 0) (scale : ℝ)
    (X : ℕ → Ω → ℝ) (ω : Ω) :
    scaledBlockPath m scale X ω unitRightEndpoint = (∑ i ∈ Finset.range m, X i ω) / scale := by
  have hlast : gridTime m (Fin.last m) = unitRightEndpoint := gridTime_last hm
  rw [← hlast, scaledBlockPath_apply_grid hm]
  rfl

private theorem scaledBlockPath_mem_closed {Ω : Type*} {m : ℕ} (hm : m ≠ 0) {scale : ℝ}
    (hs : 0 < scale) (X : ℕ → Ω → ℝ) (ω : Ω) (x a b : ℝ) :
    (∀ t, scaledBlockPath m scale X ω t + x ∈ Set.Icc a b) ↔
      ∀ k ≤ m, scale * x + ∑ i ∈ Finset.range k, X i ω ∈
        Set.Icc (scale * a) (scale * b) := by
  rw [polygonal_mem_Icc_iff_grid (scaledBlockPath_convex hm scale X ω) x a b]
  simp only [scaledBlockPath_apply_grid hm]
  have hiff (k : ℕ) :
      (∑ i ∈ Finset.range k, X i ω) / scale + x ∈ Set.Icc a b ↔
        scale * x + ∑ i ∈ Finset.range k, X i ω ∈ Set.Icc (scale * a) (scale * b) := by
    rw [add_comm (_ / scale) x, add_div_eq_mul_add_div _ _ hs.ne', mul_comm x scale]
    simp only [Set.mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs]
    rw [mul_comm a scale, mul_comm b scale]
  exact ⟨fun h k hk => (hiff k).1 (h ⟨k, Nat.lt_succ_of_le hk⟩),
    fun h k => (hiff k.val).2 (h k.val (Nat.le_of_lt_succ k.isLt))⟩

private theorem scaledBlockPath_mem_open {Ω : Type*} {m : ℕ} (hm : m ≠ 0) {scale : ℝ}
    (hs : 0 < scale) (X : ℕ → Ω → ℝ) (ω : Ω) (x a b : ℝ) :
    (∀ t, scaledBlockPath m scale X ω t + x ∈ Set.Ioo a b) ↔
      ∀ k ≤ m, scale * x + ∑ i ∈ Finset.range k, X i ω ∈
        Set.Ioo (scale * a) (scale * b) := by
  rw [polygonal_mem_Ioo_iff_grid (scaledBlockPath_convex hm scale X ω) x a b]
  simp only [scaledBlockPath_apply_grid hm]
  have hiff (k : ℕ) :
      (∑ i ∈ Finset.range k, X i ω) / scale + x ∈ Set.Ioo a b ↔
        scale * x + ∑ i ∈ Finset.range k, X i ω ∈ Set.Ioo (scale * a) (scale * b) := by
    rw [add_comm (_ / scale) x, add_div_eq_mul_add_div _ _ hs.ne', mul_comm x scale]
    simp only [Set.mem_Ioo, lt_div_iff₀ hs, div_lt_iff₀ hs]
    rw [mul_comm a scale, mul_comm b scale]
  exact ⟨fun h k hk => (hiff k).1 (h ⟨k, Nat.lt_succ_of_le hk⟩),
    fun h k => (hiff k.val).2 (h k.val (Nat.le_of_lt_succ k.isLt))⟩

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [SecondCountableTopology C(UnitInterval, ℝ)] [MeasurableSpace C(UnitInterval, ℝ)]
  [BorelSpace C(UnitInterval, ℝ)] {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {X : ℕ → Ω → ℝ} {B : Ω' → C(UnitInterval, ℝ)}
  {scale times : ℕ → ℝ} {time : ℝ} {K : Set ℝ}

/-- Portmanteau transfers a strict closed-tube bound to the walk uniformly on compact starts. -/
theorem eventually_walk_closed_lt_of_donsker
    (h : TendstoInDistribution (fun m => donskerProcess m X) atTop B (fun _ => P) Q)
    (hscale : Tendsto scale atTop atTop) (htimes : Tendsto times atTop (𝓝 time))
    (htime : 0 < time) (hK : IsCompact K) (a b : ℝ) {upper : ℝ≥0∞}
    (hu : ∀ x ∈ K, Q {ω | ∀ t, Real.sqrt time * B ω t + x ∈ Set.Icc a b} < upper) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      P {ω | ∀ k ≤ ⌊times n * scale n ^ 2⌋₊,
        scale n * x + ∑ i ∈ Finset.range k, X i ω ∈
          Set.Icc (scale n * a) (scale n * b)} < upper := by
  have hm := tendsto_diffusive_block_size_of_tendsto hscale htimes htime
  have hconv := tendstoInDistribution_smul_subseq h hm
    (tendsto_diffusive_block_normalization_of_tendsto hscale htimes htime)
  have hbound := eventually_closed_tube_lt hconv unitRightEndpoint hK isClosed_Icc
    (isClosed_univ : IsClosed (Set.univ : Set ℝ)) (b := upper) (by
      simpa [ContinuousMap.smul_apply] using hu)
  filter_upwards [hbound, (tendsto_atTop.1 hscale) 1, (tendsto_atTop.1 hm) 1] with n hn hs hm x hx
  have heq :
      {ω | ∀ k ≤ ⌊times n * scale n ^ 2⌋₊,
        scale n * x + ∑ i ∈ Finset.range k, X i ω ∈
          Set.Icc (scale n * a) (scale n * b)} =
      {ω | ∀ t, scaledBlockPath ⌊times n * scale n ^ 2⌋₊ (scale n) X ω t + x ∈ Set.Icc a b} := by
    ext ω
    exact (scaledBlockPath_mem_closed (by omega) (zero_lt_one.trans_le hs) X ω x a b).symm
  rw [heq]
  simpa [scaledBlockPath] using hn x hx

/-- Portmanteau transfers strict lower bounds for open tubes with an endpoint window to the
discrete walk. The conclusion is stated with closed constraints for block concatenation. -/
theorem eventually_lt_walk_closed_of_donsker
    (h : TendstoInDistribution (fun m => donskerProcess m X) atTop B (fun _ => P) Q)
    (hscale : Tendsto scale atTop atTop) (htimes : Tendsto times atTop (𝓝 time))
    (htime : 0 < time) (hK : IsCompact K) (a b c d : ℝ) {lower : ℝ≥0∞}
    (hl : ∀ x ∈ K, lower < Q {ω | (∀ t, Real.sqrt time * B ω t + x ∈ Set.Ioo a b) ∧
      Real.sqrt time * B ω unitRightEndpoint + x ∈ Set.Ioo c d}) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      lower < P {ω |
        (∀ k ≤ ⌊times n * scale n ^ 2⌋₊,
          scale n * x + ∑ i ∈ Finset.range k, X i ω ∈
            Set.Icc (scale n * a) (scale n * b)) ∧
        scale n * x + ∑ i ∈ Finset.range ⌊times n * scale n ^ 2⌋₊, X i ω ∈
          Set.Icc (scale n * c) (scale n * d)} := by
  have hm := tendsto_diffusive_block_size_of_tendsto hscale htimes htime
  have hconv := tendstoInDistribution_smul_subseq h hm
    (tendsto_diffusive_block_normalization_of_tendsto hscale htimes htime)
  have hbound := eventually_lt_open_tube hconv unitRightEndpoint hK
    isOpen_Ioo isOpen_Ioo (b := lower) (by
      simpa [ContinuousMap.smul_apply] using hl)
  filter_upwards [hbound, (tendsto_atTop.1 hscale) 1, (tendsto_atTop.1 hm) 1] with n hn hs hm x hx
  have hpos := zero_lt_one.trans_le hs
  let m := ⌊times n * scale n ^ 2⌋₊
  have hm' : m ≠ 0 := by
    dsimp [m]
    omega
  apply (hn x hx).trans_le
  apply measure_mono
  intro ω hω
  change (∀ t, scaledBlockPath m (scale n) X ω t + x ∈ Set.Ioo a b) ∧
    scaledBlockPath m (scale n) X ω unitRightEndpoint + x ∈ Set.Ioo c d at hω
  refine ⟨fun k hk => Set.Ioo_subset_Icc_self
    ((scaledBlockPath_mem_open hm' hpos X ω x a b).1 hω.1 k hk), ?_⟩
  have hlast := hω.2
  rw [endpoint_eq_scaled_sum hm', add_comm (_ / scale n) x,
    add_div_eq_mul_add_div _ _ hpos.ne', mul_comm x (scale n)] at hlast
  simp only [Set.mem_Ioo, lt_div_iff₀ hpos, div_lt_iff₀ hpos] at hlast
  rw [mul_comm c (scale n), mul_comm d (scale n)] at hlast
  exact ⟨hlast.1.le, hlast.2.le⟩

end Transfer

end Mogulskii.SmallDeviation
