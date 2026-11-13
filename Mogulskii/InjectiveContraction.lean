import Mogulskii.ExponentialBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Map

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Mogulskii

/-- The rate transported by an injective map, with infinite rate outside its image. -/
noncomputable def imageRate {X Y : Type*} (f : X → Y) (I : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ⨅ x : {x // f x = y}, I x

theorem imageRate_apply {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    (I : X → ℝ≥0∞) (x : X) : imageRate f I (f x) = I x := by
  apply le_antisymm
  · exact iInf_le (fun y : {y // f y = f x} ↦ I y) ⟨x, rfl⟩
  · exact le_iInf fun y ↦ (congrArg I (hf y.property)).ge

theorem imageRate_eq_top {X Y : Type*} {f : X → Y} {I : X → ℝ≥0∞} {y : Y}
    (hy : y ∉ range f) : imageRate f I y = ⊤ := by
  apply top_unique
  exact le_iInf fun x ↦ (hy ⟨x, x.property⟩).elim

theorem imageRate_sublevel {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    (I : X → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    {y | imageRate f I y ≤ c} = f '' {x | I x ≤ c} := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ range f := by
      by_contra hn
      have : imageRate f I y = ⊤ := imageRate_eq_top hn
      exact hc (top_unique (this ▸ hy))
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, by simpa only [mem_setOf_eq, imageRate_apply hf] using hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_setOf_eq, imageRate_apply hf] using hx

theorem HasExponentialBounds.map_injective {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : ℕ → Measure X} {I : X → ℝ≥0∞} (hP : HasExponentialBounds P I)
    {f : X → Y} (hc : Continuous f) (hi : Function.Injective f) :
    HasExponentialBounds (fun n ↦ (P n).map f) (imageRate f I) := by
  have hm : Measurable f := hc.measurable
  have hK (c : ℝ≥0∞) (hfin : c ≠ ⊤) : IsCompact {y | imageRate f I y ≤ c} := by
    rw [imageRate_sublevel hi I hfin]
    exact (hP.isGood.isCompact_sublevel c hfin).image hc
  refine ⟨⟨lowerSemicontinuous_iff_isClosed_preimage.2 fun c ↦ ?_, hK⟩, ?_, ?_⟩
  · by_cases h : c = ⊤
    · simp [h]
    · exact (hK c h).isClosed
  · intro F hF r hr
    have hrate : (⨅ y ∈ F, imageRate f I y) ≤ (⨅ x ∈ f ⁻¹' F, I x) := by
      refine le_iInf₂ fun x hx ↦ ?_
      rw [← imageRate_apply hi I x]
      exact iInf₂_le (f x) hx
    obtain ⟨C, hC, hev⟩ := hP.upper (hF.preimage hc)
      (hr.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.2 hrate))
    exact ⟨C, hC, hev.mono fun n hn ↦ by rw [Measure.map_apply hm hF.measurableSet]; exact hn⟩
  · intro y U hU r hr
    have hy : y ∈ range f := by
      by_contra hn
      rw [imageRate_eq_top hn] at hr
      exact not_lt_of_ge le_top hr
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨V, hVU, hV, hx⟩ := mem_nhds_iff.1 hU
    have hv : f ⁻¹' V ∈ 𝓝 x := (hV.preimage hc).mem_nhds hx
    rw [imageRate_apply hi] at hr
    obtain ⟨C, hC, hev⟩ := hP.lower hv hr
    refine ⟨C, hC, hev.mono fun n hn ↦ hn.trans ?_⟩
    rw [← Measure.map_apply hm hV.measurableSet]
    exact measure_mono hVU

end Mogulskii

