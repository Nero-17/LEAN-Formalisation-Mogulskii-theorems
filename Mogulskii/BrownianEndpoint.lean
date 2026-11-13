import Mogulskii.BrownianTerminal
import Mogulskii.IndependentStep

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Mogulskii

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}

/-- Survival in an interior interval up to time T, followed by a unit transition in
the wider interval to a prescribed interior endpoint window. -/
theorem uniform_closed_survival_with_endpoint_lower
    {left right innerLeft innerRight lower upper finishLower finishUpper : ℝ}
    (hinnerLeft : left < innerLeft) (hinnerRight : innerRight < right)
    (hleft : innerLeft < lower) (hle : lower ≤ upper) (hright : upper < innerRight)
    (hfinishLeft : left < finishLower) (hfinishWidth : finishLower < finishUpper)
    (hfinishRight : finishUpper < right) :
    ∃ c > 0, ∀ (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω), IsBrownianReal B P →
      (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) →
      ∀ x ∈ Icc lower upper, ∀ T : ℝ≥0,
        c * Real.exp (-intervalEigenvalue 1 innerLeft innerRight * (T : ℝ)) ≤
          P.real (intervalSurvival (fun t ω ↦ x + B t ω) left right (T + 1) ∩
            {ω | x + B (T + 1) ω ∈ Icc finishLower finishUpper}) := by
  have hinner := (hleft.trans_le hle).trans hright
  obtain ⟨c₁, hc₁, h₁⟩ := uniform_closed_survival_lower (Ω := Ω) hleft hle hright
  obtain ⟨c₂, hc₂, h₂⟩ := uniform_brownian_terminal_transition (Ω := Ω)
    hinnerLeft hinner.le hinnerRight hfinishLeft hfinishWidth hfinishRight
  refine ⟨c₂ * c₁, mul_pos hc₂ hc₁, fun B P hB hm hc x hx T ↦ ?_⟩
  haveI : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let history := fun ω (t : Iic T) ↦ B t ω
  let increment := fun ω t ↦ B (T + t) ω - B T ω
  let past : Set (Iic T → ℝ) := ⋂ n : ℕ, ⋂ k : ℕ, ⋂ hk : k ≤ n + 1,
    {f | x + f ⟨uniformGrid T n k,
      (monotone_uniformGrid T n hk).trans_eq (uniformGrid_last T n)⟩ ∈ Icc innerLeft innerRight}
  let survive : Set ((Iic T → ℝ) × (ℝ≥0 → ℝ)) :=
    (⋂ n : ℕ, ⋂ k : ℕ, ⋂ _ : k ≤ n + 1,
      {z | x + z.1 ⟨T, self_mem_Iic⟩ + z.2 (uniformGrid 1 n k) ∈ Icc left right}) ∩
      {z | x + z.1 ⟨T, self_mem_Iic⟩ + z.2 1 ∈ Icc finishLower finishUpper}
  have hhistory : Measurable history := measurable_pi_lambda _ (fun t ↦ hm t.1)
  have hmincrement (t : ℝ≥0) : Measurable (fun ω ↦ increment ω t) :=
    (hm (T + t)).sub (hm T)
  have hincrement : Measurable increment := measurable_pi_lambda _ hmincrement
  have hcinc (ω : Ω) : Continuous (increment ω) :=
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hpast : MeasurableSet past := by
    apply MeasurableSet.iInter (fun n ↦ MeasurableSet.iInter (fun k ↦ MeasurableSet.iInter (fun hk ↦ ?_)))
    exact (measurable_const.add (measurable_pi_apply _)) measurableSet_Icc
  have hposition (t : ℝ≥0) :
      Measurable (fun z : (Iic T → ℝ) × (ℝ≥0 → ℝ) ↦
        x + z.1 ⟨T, self_mem_Iic⟩ + z.2 t) :=
    (measurable_const.add
      ((measurable_pi_apply (⟨T, self_mem_Iic⟩ : Iic T)).comp measurable_fst)).add
      ((measurable_pi_apply t).comp measurable_snd)
  have hsurvive : MeasurableSet survive := by
    exact (MeasurableSet.iInter (fun n ↦ MeasurableSet.iInter (fun k ↦
      MeasurableSet.iInter (fun _ ↦ hposition (uniformGrid 1 n k) measurableSet_Icc)))).inter
        (hposition 1 measurableSet_Icc)
  have hpast' : history ⁻¹' past = intervalSurvival (fun t ω ↦ x + B t ω) innerLeft innerRight T := by
    ext ω
    simp only [history, past, mem_preimage, mem_iInter, mem_setOf_eq, intervalSurvival]
    constructor
    · intro hg t ht
      by_contra hn
      obtain ⟨n, k, hk, he⟩ := (eventually_exists_uniformGrid_exit
        (continuous_const.add (hc ω)) ⟨t, ht, hn⟩).exists
      exact he (hg n k hk)
    · intro hs n k hk
      exact hs _ ((monotone_uniformGrid T n hk).trans_eq (uniformGrid_last T n))
  have hsection (f : Iic T → ℝ) :
      increment ⁻¹' (Prod.mk f ⁻¹' survive) =
        intervalSurvival (fun t ω ↦ x + f ⟨T, self_mem_Iic⟩ + increment ω t) left right 1 ∩
          {ω | x + f ⟨T, self_mem_Iic⟩ + increment ω 1 ∈ Icc finishLower finishUpper} := by
    ext ω
    simp only [mem_preimage, survive, mem_inter_iff, mem_iInter, mem_setOf_eq,
      intervalSurvival]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro hg t ht
      by_contra hn
      obtain ⟨n, k, hk, he⟩ := (eventually_exists_uniformGrid_exit
        (continuous_const.add (hcinc ω)) ⟨t, ht, hn⟩).exists
      exact he (hg n k hk)
    · intro hs n k hk
      exact hs _ ((monotone_uniformGrid 1 n hk).trans_eq (uniformGrid_last 1 n))
  have hstep (f : Iic T → ℝ) (hf : f ∈ past) :
      ENNReal.ofReal c₂ ≤ (P.map increment) (Prod.mk f ⁻¹' survive) := by
    have hy : x + f ⟨T, self_mem_Iic⟩ ∈ Icc innerLeft innerRight := by
      have hg := (show ∀ n k (hk : k ≤ n + 1),
        x + f ⟨uniformGrid T n k,
          (monotone_uniformGrid T n hk).trans_eq (uniformGrid_last T n)⟩ ∈ Icc innerLeft innerRight by
          simpa [past] using hf) 0 1 (by norm_num)
      have hlast : (⟨uniformGrid T 0 1,
          (monotone_uniformGrid T 0 (show 1 ≤ 0 + 1 by norm_num)).trans_eq
            (uniformGrid_last T 0)⟩ : Iic T) = ⟨T, self_mem_Iic⟩ :=
        Subtype.ext (uniformGrid_last T 0)
      rwa [hlast] at hg
    rw [Measure.map_apply hincrement (measurable_prodMk_left hsurvive), hsection]
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    exact h₂ (hB.shift T) hmincrement hcinc _ hy
  have hlower := Mogulskii.SmallDeviation.mul_measure_le_independent_step hhistory hincrement
    (hB.toIsPreBrownianReal.indepFun_shift T).symm hpast hsurvive hstep
  rw [hpast'] at hlower
  have hcontain : {ω | history ω ∈ past ∧ (history ω, increment ω) ∈ survive} ⊆
      intervalSurvival (fun t ω ↦ x + B t ω) left right (T + 1) ∩
        {ω | x + B (T + 1) ω ∈ Icc finishLower finishUpper} := by
    rintro ω ⟨hp, hs⟩
    have hbefore : ω ∈ history ⁻¹' past := hp
    rw [hpast'] at hbefore
    have hafter : ω ∈ increment ⁻¹' (Prod.mk (history ω) ⁻¹' survive) := hs
    rw [hsection] at hafter
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · by_cases htime : t ≤ T
      · exact ⟨hinnerLeft.le.trans (hbefore t htime).1,
          (hbefore t htime).2.trans hinnerRight.le⟩
      · have hsub : t - T ≤ 1 := tsub_le_iff_left.mpr ht
        have h := hafter.1 (t - T) hsub
        have htime' : T + (t - T) = t := add_tsub_cancel_of_le (le_of_not_ge htime)
        change x + B T ω + (B (T + (t - T)) ω - B T ω) ∈ Icc left right at h
        rwa [htime', show x + B T ω + (B t ω - B T ω) = x + B t ω by ring] at h
    · have h := hafter.2
      change x + B T ω + (B (T + 1) ω - B T ω) ∈ Icc finishLower finishUpper at h
      rwa [show x + B T ω + (B (T + 1) ω - B T ω) = x + B (T + 1) ω by ring] at h
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) (hlower.trans (measure_mono hcontain))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂.le] at hreal
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (h₁ B P hB hm hc x hx T) hc₂.le).trans hreal

end Mogulskii
