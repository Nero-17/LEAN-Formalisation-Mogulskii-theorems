import Mogulskii.PackedWalk
import Mogulskii.IndependentStep
import Mathlib.Data.ENNReal.BigOperators

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Mogulskii.SmallDeviation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A block with time-dependent constraints and a separate constraint on its last position. -/
def endpointTube (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (lower upper : ℕ → ℝ)
    (endpoint : Set ℝ) : Set Ω :=
  tubeEvent X n x lower upper ∩ (fun ω => x + walk X n ω) ⁻¹' endpoint

theorem measurableSet_endpointTube {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (n : ℕ) (x : ℝ) (lower upper : ℕ → ℝ) {endpoint : Set ℝ}
    (hend : MeasurableSet endpoint) :
    MeasurableSet (endpointTube X n x lower upper endpoint) :=
  (measurableSet_tubeEvent hX n x lower upper).inter
    ((measurable_const.add (measurable_walk hX n)) hend)

/-- The endpoint-constrained block depends only on the finite vector of its increments. -/
theorem measure_endpointTube_shift {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (m n : ℕ) (x : ℝ)
    (lower upper : ℕ → ℝ) {endpoint : Set ℝ} (hend : MeasurableSet endpoint) :
    μ (endpointTube (fun i => X (m + i)) n x lower upper endpoint) =
      μ (endpointTube X n x lower upper endpoint) := by
  let A : Set (Fin n → ℝ) := {v | () ∈ endpointTube (blockExtension v) n x lower upper endpoint}
  have hA : MeasurableSet A := by
    change MeasurableSet ({v | ∀ k ≤ n, x + walk (blockExtension v) k () ∈
      Icc (lower k) (upper k)} ∩ {v | x + walk (blockExtension v) n () ∈ endpoint})
    apply MeasurableSet.inter
    · have heq : {v : Fin n → ℝ | ∀ k ≤ n, x + walk (blockExtension v) k () ∈
          Icc (lower k) (upper k)} =
          ⋂ k : ℕ, ⋂ _ : k ≤ n, (fun v : Fin n → ℝ => x + walk (blockExtension v) k ()) ⁻¹'
            Icc (lower k) (upper k) := by ext v; simp
      rw [heq]
      exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        (measurable_const.add (measurable_walk_blockExtension n k)) measurableSet_Icc
    · exact (measurable_const.add (measurable_walk_blockExtension n n)) hend
  have preimage_eq (j : ℕ) :
      blockVector X j n ⁻¹' A = endpointTube (fun i => X (j + i)) n x lower upper endpoint := by
    ext ω
    simp only [A, Set.mem_preimage, Set.mem_setOf_eq, endpointTube, Set.mem_inter_iff, tubeEvent]
    refine and_congr ?_ ?_
    · apply forall_congr'
      intro k
      apply forall_congr'
      intro hk
      rw [walk_blockExtension_blockVector X j n k ω hk]
    · rw [walk_blockExtension_blockVector X j n n ω le_rfl]
  have h := congrArg (fun ν : Measure (Fin n → ℝ) => ν A)
    (map_blockVector_shift hX hind hid m n)
  rw [Measure.map_apply (measurable_blockVector hX m n) hA,
    Measure.map_apply (measurable_blockVector hX 0 n) hA, preimage_eq, preimage_eq] at h
  simpa using h

/-- Discrete positions must satisfy each block's tube and each partition endpoint constraint. -/
def partitionTube (X : ℕ → Ω → ℝ) (x : ℝ) (time : ℕ → ℕ)
    (lower upper : ℕ → ℕ → ℝ) (endpoint : ℕ → Set ℝ) (count : ℕ) : Set Ω :=
  {ω | x ∈ endpoint 0 ∧ ∀ j < count,
    ω ∈ endpointTube (fun i => X (time j + i)) (time (j + 1) - time j)
      (x + walk X (time j) ω) (lower j) (upper j) (endpoint (j + 1))}

theorem mem_partitionTube_succ {X : ℕ → Ω → ℝ} {x : ℝ} {time : ℕ → ℕ}
    {lower upper : ℕ → ℕ → ℝ} {endpoint : ℕ → Set ℝ} {count : ℕ} {ω : Ω} :
    ω ∈ partitionTube X x time lower upper endpoint (count + 1) ↔
      ω ∈ partitionTube X x time lower upper endpoint count ∧
      ω ∈ endpointTube (fun i => X (time count + i)) (time (count + 1) - time count)
        (x + walk X (time count) ω) (lower count) (upper count) (endpoint (count + 1)) := by
  constructor
  · intro h
    exact ⟨⟨h.1, fun j hj => h.2 j (Nat.lt_succ_of_lt hj)⟩, h.2 count (Nat.lt_succ_self _)⟩
  · rintro ⟨h, hlast⟩
    refine ⟨h.1, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact h.2 j hlt
    · exact hlast

theorem mem_endpoint_of_mem_partitionTube {X : ℕ → Ω → ℝ} {x : ℝ} {time : ℕ → ℕ}
    {lower upper : ℕ → ℕ → ℝ} {endpoint : ℕ → Set ℝ} {count : ℕ}
    (ht : Monotone time) (h0 : time 0 = 0) {ω : Ω}
    (hω : ω ∈ partitionTube X x time lower upper endpoint count) :
    x + walk X (time count) ω ∈ endpoint count := by
  cases count with
  | zero => simpa [h0, walk] using hω.1
  | succ count =>
    have h := (mem_partitionTube_succ.mp hω).2.2
    change x + walk X (time count) ω +
      walk (fun i => X (time count + i)) (time (count + 1) - time count) ω ∈
        endpoint (count + 1) at h
    rw [add_assoc, ← walk_add, Nat.add_sub_of_le (ht (Nat.le_succ _))] at h
    exact h

theorem mem_partitionTube_iff_absolute {X : ℕ → Ω → ℝ} {x : ℝ} {time : ℕ → ℕ}
    {lower upper : ℕ → ℕ → ℝ} {endpoint : ℕ → Set ℝ} {count : ℕ}
    (ht : Monotone time) {ω : Ω} :
    ω ∈ partitionTube X x time lower upper endpoint count ↔
      x ∈ endpoint 0 ∧ ∀ j < count,
        (∀ k ≤ time (j + 1) - time j,
          x + walk X (time j + k) ω ∈ Icc (lower j k) (upper j k)) ∧
        x + walk X (time (j + 1)) ω ∈ endpoint (j + 1) := by
  unfold partitionTube
  simp only [mem_setOf_eq, endpointTube, mem_inter_iff, mem_preimage, tubeEvent]
  refine and_congr Iff.rfl ?_
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have hjtime : time j + (time (j + 1) - time j) = time (j + 1) :=
    Nat.add_sub_of_le (ht (Nat.le_succ _))
  simp_rw [add_assoc, ← walk_add, hjtime]

theorem measurableSet_partitionHistory (x : ℝ) (time : ℕ → ℕ)
    (lower upper : ℕ → ℕ → ℝ) {endpoint : ℕ → Set ℝ}
    (he : ∀ j, MeasurableSet (endpoint j)) (count : ℕ) :
    MeasurableSet {v : Fin (time count) → ℝ |
      () ∈ partitionTube (blockExtension v) x time lower upper endpoint count} := by
  have hmain (j : ℕ) :
      MeasurableSet {v : Fin (time count) → ℝ |
        () ∈ endpointTube (fun i => blockExtension v (time j + i)) (time (j + 1) - time j)
          (x + walk (blockExtension v) (time j) ()) (lower j) (upper j) (endpoint (j + 1))} := by
    have hwalk (k : ℕ) :
        Measurable (fun v : Fin (time count) → ℝ =>
          x + walk (blockExtension v) (time j) () +
          walk (fun i => blockExtension v (time j + i)) k ()) := by
      have h : Measurable (fun v : Fin (time count) → ℝ =>
          x + walk (blockExtension v) (time j + k) ()) :=
        measurable_const.add (measurable_walk_blockExtension (time count) (time j + k))
      simpa only [add_assoc, ← walk_add] using h
    change MeasurableSet ({v : Fin (time count) → ℝ |
      ∀ k ≤ time (j + 1) - time j, x + walk (blockExtension v) (time j) () +
        walk (fun i => blockExtension v (time j + i)) k () ∈ Icc (lower j k) (upper j k)} ∩
        (fun v : Fin (time count) → ℝ => x + walk (blockExtension v) (time j) () +
          walk (fun i => blockExtension v (time j + i)) (time (j + 1) - time j) ()) ⁻¹'
            endpoint (j + 1))
    refine MeasurableSet.inter ?_ (hwalk _ (he _))
    rw [show {v : Fin (time count) → ℝ | ∀ k ≤ time (j + 1) - time j,
      x + walk (blockExtension v) (time j) () +
        walk (fun i => blockExtension v (time j + i)) k () ∈ Icc (lower j k) (upper j k)} =
      ⋂ k : ℕ, ⋂ _ : k ≤ time (j + 1) - time j,
        (fun v : Fin (time count) → ℝ => x + walk (blockExtension v) (time j) () +
          walk (fun i => blockExtension v (time j + i)) k ()) ⁻¹'
          Icc (lower j k) (upper j k) by ext v; simp]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hwalk k measurableSet_Icc
  rw [show {v : Fin (time count) → ℝ |
    () ∈ partitionTube (blockExtension v) x time lower upper endpoint count} =
    {v | x ∈ endpoint 0} ∩ ⋂ j : ℕ, ⋂ _ : j < count, {v |
      () ∈ endpointTube (fun i => blockExtension v (time j + i)) (time (j + 1) - time j)
        (x + walk (blockExtension v) (time j) ()) (lower j) (upper j) (endpoint (j + 1))} by
      ext v; simp [partitionTube]]
  exact (MeasurableSet.const _).inter <| MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => hmain j

theorem partitionHistory_preimage (X : ℕ → Ω → ℝ) (x : ℝ) {time : ℕ → ℕ}
    (ht : Monotone time) (lower upper : ℕ → ℕ → ℝ) (endpoint : ℕ → Set ℝ) (count : ℕ) :
    blockVector X 0 (time count) ⁻¹' {v |
      () ∈ partitionTube (blockExtension v) x time lower upper endpoint count} =
      partitionTube X x time lower upper endpoint count := by
  ext ω
  simp only [mem_preimage, mem_setOf_eq]
  rw [mem_partitionTube_iff_absolute ht, mem_partitionTube_iff_absolute ht]
  refine and_congr Iff.rfl ?_
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have hjn : time (j + 1) ≤ time count := ht (Nat.succ_le_of_lt hj)
  have hjtime : time j + (time (j + 1) - time j) = time (j + 1) :=
    Nat.add_sub_of_le (ht (Nat.le_succ _))
  refine and_congr ?_ ?_
  · apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    have hkbound : time j + k ≤ time count := by
      exact (Nat.add_le_add_left hk _).trans (hjtime.le.trans hjn)
    rw [walk_blockExtension_blockVector X 0 (time count) (time j + k) ω hkbound]
    simp
  · rw [walk_blockExtension_blockVector X 0 (time count) (time (j + 1)) ω hjn]
    simp

private def jointEndpointTube {m n : ℕ} (x : ℝ) (lower upper : ℕ → ℝ)
    (endpoint : Set ℝ) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {v | () ∈ endpointTube (blockExtension v.2) n (x + walk (blockExtension v.1) m ())
    lower upper endpoint}

private theorem measurableSet_jointEndpointTube {m n : ℕ} (x : ℝ)
    (lower upper : ℕ → ℝ) {endpoint : Set ℝ} (he : MeasurableSet endpoint) :
    MeasurableSet (jointEndpointTube (m := m) (n := n) x lower upper endpoint) := by
  have hwalk (k : ℕ) :
      Measurable (fun v : (Fin m → ℝ) × (Fin n → ℝ) =>
        x + walk (blockExtension v.1) m () + walk (blockExtension v.2) k ()) :=
    (measurable_const.add ((measurable_walk_blockExtension m m).comp measurable_fst)).add
      ((measurable_walk_blockExtension n k).comp measurable_snd)
  change MeasurableSet ({v : (Fin m → ℝ) × (Fin n → ℝ) | ∀ k ≤ n,
      x + walk (blockExtension v.1) m () + walk (blockExtension v.2) k () ∈
        Icc (lower k) (upper k)} ∩
    (fun v : (Fin m → ℝ) × (Fin n → ℝ) =>
      x + walk (blockExtension v.1) m () + walk (blockExtension v.2) n ()) ⁻¹' endpoint)
  refine MeasurableSet.inter ?_ (hwalk n he)
  rw [show {v : (Fin m → ℝ) × (Fin n → ℝ) | ∀ k ≤ n,
    x + walk (blockExtension v.1) m () + walk (blockExtension v.2) k () ∈
      Icc (lower k) (upper k)} =
    ⋂ k : ℕ, ⋂ _ : k ≤ n,
      (fun v : (Fin m → ℝ) × (Fin n → ℝ) =>
        x + walk (blockExtension v.1) m () + walk (blockExtension v.2) k ()) ⁻¹'
        Icc (lower k) (upper k) by ext v; simp]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hwalk k measurableSet_Icc

private theorem mem_jointEndpointTube_iff {X : ℕ → Ω → ℝ} {m n : ℕ}
    (x : ℝ) (lower upper : ℕ → ℝ) (endpoint : Set ℝ) (v : Fin m → ℝ) (ω : Ω) :
    (v, blockVector X m n ω) ∈ jointEndpointTube x lower upper endpoint ↔
      ω ∈ endpointTube (fun i => X (m + i)) n (x + walk (blockExtension v) m ())
        lower upper endpoint := by
  simp only [jointEndpointTube, mem_setOf_eq, endpointTube, mem_inter_iff, tubeEvent, mem_preimage]
  refine and_congr ?_ ?_
  · apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    rw [walk_blockExtension_blockVector X m n k ω hk]
  · rw [walk_blockExtension_blockVector X m n n ω le_rfl]

/-- The conditional probability of the next partition block is computed from fresh increments. -/
theorem measure_partitionTube_succ {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (x : ℝ) {time : ℕ → ℕ} (ht : Monotone time) (lower upper : ℕ → ℕ → ℝ)
    {endpoint : ℕ → Set ℝ} (he : ∀ j, MeasurableSet (endpoint j)) (count : ℕ) :
    μ (partitionTube X x time lower upper endpoint (count + 1)) =
      ∫⁻ v in {v | () ∈ partitionTube (blockExtension v) x time lower upper endpoint count},
        μ (endpointTube X (time (count + 1) - time count)
          (x + walk (blockExtension v) (time count) ()) (lower count) (upper count)
          (endpoint (count + 1))) ∂(μ.map (blockVector X 0 (time count))) := by
  let length := time (count + 1) - time count
  let past : Set (Fin (time count) → ℝ) :=
    {v | () ∈ partitionTube (blockExtension v) x time lower upper endpoint count}
  let survive : Set ((Fin (time count) → ℝ) × (Fin length → ℝ)) :=
    jointEndpointTube x (lower count) (upper count) (endpoint (count + 1))
  have hpast : MeasurableSet past := measurableSet_partitionHistory x time lower upper he count
  have hsurvive : MeasurableSet survive := measurableSet_jointEndpointTube _ _ _ (he _)
  have hstep := measure_independent_step
    (measurable_blockVector hX 0 (time count))
    (measurable_blockVector hX (time count) length) (indepFun_blockVector hX hind _ _)
    hpast hsurvive
  have hevent : {ω | blockVector X 0 (time count) ω ∈ past ∧
      (blockVector X 0 (time count) ω, blockVector X (time count) length ω) ∈ survive} =
      partitionTube X x time lower upper endpoint (count + 1) := by
    ext ω
    simp only [mem_setOf_eq, survive, mem_jointEndpointTube_iff, mem_partitionTube_succ]
    rw [walk_blockExtension_blockVector X 0 (time count) (time count) ω le_rfl]
    simp only [Nat.zero_add]
    change (ω ∈ blockVector X 0 (time count) ⁻¹' past ∧ _) ↔ _
    rw [partitionHistory_preimage X x ht lower upper endpoint count]
  rw [hevent] at hstep
  rw [hstep]
  apply lintegral_congr
  intro v
  have hslice : MeasurableSet (Prod.mk v ⁻¹' survive) :=
    ((measurable_const (a := v)).prodMk (measurable_id (α := Fin length → ℝ))) hsurvive
  rw [Measure.map_apply (measurable_blockVector hX (time count) length) hslice]
  rw [show blockVector X (time count) length ⁻¹' (Prod.mk v ⁻¹' survive) =
      endpointTube (fun i => X (time count + i)) length
        (x + walk (blockExtension v) (time count) ()) (lower count) (upper count)
        (endpoint (count + 1)) by
      ext ω
      exact mem_jointEndpointTube_iff (X := X) x (lower count) (upper count)
        (endpoint (count + 1)) v ω]
  exact measure_endpointTube_shift hX hind hid (time count) length
    (x + walk (blockExtension v) (time count) ()) (lower count) (upper count) (he (count + 1))

/-- Finite products bound the measure of a partition tube under uniform local block bounds. -/
theorem measure_partitionTube_bounds {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (x : ℝ) {time : ℕ → ℕ} (ht : Monotone time) (h0 : time 0 = 0)
    (lower upper : ℕ → ℕ → ℝ) {endpoint : ℕ → Set ℝ}
    (he : ∀ j, MeasurableSet (endpoint j)) (hx : x ∈ endpoint 0)
    (p q : ℕ → ℝ≥0∞) (count : ℕ)
    (hprob : ∀ j < count, ∀ y ∈ endpoint j,
      p j ≤ μ (endpointTube X (time (j + 1) - time j) y (lower j) (upper j) (endpoint (j + 1))) ∧
      μ (endpointTube X (time (j + 1) - time j) y (lower j) (upper j) (endpoint (j + 1))) ≤ q j) :
    (∏ j ∈ Finset.range count, p j) ≤ μ (partitionTube X x time lower upper endpoint count) ∧
      μ (partitionTube X x time lower upper endpoint count) ≤ ∏ j ∈ Finset.range count, q j := by
  induction count with
  | zero =>
    have hzero : partitionTube X x time lower upper endpoint 0 = univ := by
      ext ω
      simp [partitionTube, hx]
    simp [hzero]
  | succ count ih =>
    have hinduction := ih fun j hj => hprob j (Nat.lt_succ_of_lt hj)
    let past : Set (Fin (time count) → ℝ) :=
      {v | () ∈ partitionTube (blockExtension v) x time lower upper endpoint count}
    let ν := μ.map (blockVector X 0 (time count))
    have hpast : MeasurableSet past := measurableSet_partitionHistory x time lower upper he count
    have heval : ν past = μ (partitionTube X x time lower upper endpoint count) := by
      change (μ.map (blockVector X 0 (time count))) past = _
      rw [Measure.map_apply (measurable_blockVector hX 0 (time count)) hpast,
        partitionHistory_preimage X x ht lower upper endpoint count]
    have hlast : ∀ v ∈ past, x + walk (blockExtension v) (time count) () ∈ endpoint count :=
      fun v hv => mem_endpoint_of_mem_partitionTube ht h0 hv
    rw [measure_partitionTube_succ hX hind hid x ht lower upper he count]
    change (∏ j ∈ Finset.range (count + 1), p j) ≤
      (∫⁻ v in past, _ ∂ν) ∧ (∫⁻ v in past, _ ∂ν) ≤ ∏ j ∈ Finset.range (count + 1), q j
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    constructor
    · calc
        _ ≤ p count * ν past := by
          rw [mul_comm (p count), heval]
          exact mul_le_mul_left hinduction.1 _
        _ = ∫⁻ _ in past, p count ∂ν := (setLIntegral_const past (p count)).symm
        _ ≤ _ := lintegral_mono_ae <| (ae_restrict_iff' hpast).2 <|
          Filter.Eventually.of_forall fun v hv => (hprob count (Nat.lt_succ_self _) _ (hlast v hv)).1
    · calc
        _ ≤ ∫⁻ _ in past, q count ∂ν := lintegral_mono_ae <| (ae_restrict_iff' hpast).2 <|
          Filter.Eventually.of_forall fun v hv => (hprob count (Nat.lt_succ_self _) _ (hlast v hv)).2
        _ = q count * ν past := setLIntegral_const past (q count)
        _ ≤ _ := by
          rw [mul_comm (q count), heval]
          exact mul_le_mul_left hinduction.2 _

theorem exists_partition_block {time : ℕ → ℕ} (h0 : time 0 = 0) {count k : ℕ}
    (hcount : 0 < count) (hk : k ≤ time count) :
    ∃ j < count, time j ≤ k ∧ k ≤ time (j + 1) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases h : time count ≤ k
    · exact ⟨count, Nat.lt_succ_self count, h, hk⟩
    · have hc : 0 < count := by
        by_contra! hc
        have he : count = 0 := by omega
        rw [he, h0] at h
        omega
      obtain ⟨j, hj, hleft, hright⟩ := ih hc (Nat.le_of_lt (Nat.lt_of_not_ge h))
      exact ⟨j, Nat.lt_succ_of_lt hj, hleft, hright⟩

/-- A piecewise tube whose local windows lie inside the moving tube is an inner event. -/
theorem partitionTube_subset_tubeEvent {X : ℕ → Ω → ℝ} {x : ℝ} {time : ℕ → ℕ}
    (ht : Monotone time) (h0 : time 0 = 0) {count : ℕ} (hc : 0 < count)
    {lower upper : ℕ → ℕ → ℝ} {endpoint : ℕ → Set ℝ} {f g : ℕ → ℝ}
    (hbound : ∀ j < count, ∀ k ≤ time (j + 1) - time j,
      f (time j + k) ≤ lower j k ∧ upper j k ≤ g (time j + k)) :
    partitionTube X x time lower upper endpoint count ⊆ tubeEvent X (time count) x f g := by
  intro ω hω k hk
  obtain ⟨j, hj, hjk, hkj⟩ := exists_partition_block h0 hc hk
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have hl : l ≤ time (j + 1) - time j := by omega
  have hw := ((mem_partitionTube_iff_absolute ht).mp hω).2 j hj |>.1 l hl
  exact ⟨(hbound j hj l hl).1.trans hw.1, hw.2.trans (hbound j hj l hl).2⟩

/-- A piecewise tube whose windows contain the moving tube and whose endpoints are
unrestricted is an outer event. -/
theorem tubeEvent_subset_partitionTube {X : ℕ → Ω → ℝ} {x : ℝ} {time : ℕ → ℕ}
    (ht : Monotone time) {count : ℕ} {lower upper : ℕ → ℕ → ℝ} {f g : ℕ → ℝ}
    (hbound : ∀ j < count, ∀ k ≤ time (j + 1) - time j,
      lower j k ≤ f (time j + k) ∧ g (time j + k) ≤ upper j k) :
    tubeEvent X (time count) x f g ⊆ partitionTube X x time lower upper (fun _ => univ) count := by
  intro ω hω
  refine (mem_partitionTube_iff_absolute ht).mpr ⟨mem_univ _, fun j hj => ⟨?_, mem_univ _⟩⟩
  intro k hk
  have hjt : time j ≤ time (j + 1) := ht (Nat.le_succ j)
  have hct : time (j + 1) ≤ time count := ht (Nat.succ_le_of_lt hj)
  have hw := hω (time j + k) (by omega)
  exact ⟨(hbound j hj k hk).1.trans hw.1, hw.2.trans (hbound j hj k hk).2⟩

end Mogulskii.SmallDeviation










