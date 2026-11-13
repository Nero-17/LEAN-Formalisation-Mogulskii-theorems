import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Mogulskii

/-- Coordinate arrays obtained from disjoint finite blocks of independent variables have a
product law. An injective index map on the dependent sum encodes disjointness of the blocks. -/
theorem map_blocks_eq_pi {Ω ι κ E : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace E]
    {block : ι → Type*} [∀ a, Fintype (block a)] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν] {X : κ → Ω → E}
    (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hν : ∀ i, μ.map (X i) = ν)
    (index : (Σ a, block a) → κ) (hindex : Function.Injective index) :
    μ.map (fun ω a j ↦ X (index ⟨a,j⟩) ω) =
      Measure.pi fun a : ι ↦ Measure.pi fun _ : block a ↦ ν := by
  classical
  let Y : Ω → (Σ a, block a) → E := fun ω p ↦ X (index p) ω
  have hY : Measurable Y := measurable_pi_lambda _ (fun p ↦ hm (index p))
  have hYlaw : μ.map Y = Measure.pi fun _ : (Σ a, block a) ↦ ν := by
    rw [(hX.precomp hindex).map_fun_eq_pi_map (fun p ↦ (hm (index p)).aemeasurable)]
    simp only [hν]
  have hc : Measurable (Sigma.curry (γ := fun (a : ι) (_ : block a) ↦ E)) :=
    measurable_sigmaCurry
  change μ.map (Sigma.curry (γ := fun (a : ι) (_ : block a) ↦ E) ∘ Y) = _
  rw [← Measure.map_map hc hY, hYlaw]
  refine (Measure.pi_eq fun sets hsets ↦ ?_).symm
  rw [Measure.map_apply hc (MeasurableSet.univ_pi hsets)]
  -- To regroup the flat product by rows, first identify the flat measure as the pushforward of
  -- the nested product. Uniqueness on rectangles reduces this to multiplication of the factors.
  have hflat : Measure.pi (fun _ : (Σ a, block a) ↦ ν) =
      (Measure.pi fun a : ι ↦ Measure.pi fun _ : block a ↦ ν).map Sigma.uncurry := by
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.map_apply measurable_sigmaUncurry (MeasurableSet.univ_pi hs)]
    have hpre : Sigma.uncurry ⁻¹' Set.univ.pi s =
        Set.univ.pi fun a : ι ↦ Set.univ.pi fun j : block a ↦ s ⟨a,j⟩ := by
      ext x
      simp [Sigma.forall, Sigma.uncurry]
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun p : Σ a, block a ↦ ν (s p))).symm
  rw [hflat, Measure.map_apply measurable_sigmaUncurry ((MeasurableSet.univ_pi hsets).preimage hc)]
  have hpre : Sigma.uncurry ⁻¹' (Sigma.curry ⁻¹' Set.univ.pi sets) = Set.univ.pi sets := by
    ext x
    rfl
  rw [hpre, Measure.pi_pi]

/-- Applying a measurable statistic to each disjoint block preserves the product-law
description. For sample means, use `stat a x = (∑ j, x j) / Fintype.card (block a)`. -/
theorem map_block_statistics_eq_pi {Ω ι κ E F : Type*}
    [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    {block : ι → Type*} [∀ a, Fintype (block a)] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν] {X : κ → Ω → E}
    (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hν : ∀ i, μ.map (X i) = ν)
    (index : (Σ a, block a) → κ) (hindex : Function.Injective index)
    (stat : (a : ι) → (block a → E) → F) (hstat : ∀ a, Measurable (stat a)) :
    μ.map (fun ω a ↦ stat a (fun j ↦ X (index ⟨a,j⟩) ω)) =
      Measure.pi fun a : ι ↦ (Measure.pi fun _ : block a ↦ ν).map (stat a) := by
  let row : Ω → ((a : ι) → block a → E) := fun ω a j ↦ X (index ⟨a,j⟩) ω
  let transform : ((a : ι) → block a → E) → (ι → F) := fun z a ↦ stat a (z a)
  have hrow : Measurable row := measurable_pi_lambda _ fun a ↦
    measurable_pi_lambda _ fun j ↦ hm (index ⟨a,j⟩)
  have htransform : Measurable transform := measurable_pi_lambda _ fun a ↦
    (hstat a).comp (measurable_pi_apply a)
  change μ.map (transform ∘ row) = _
  rw [← Measure.map_map htransform hrow, map_blocks_eq_pi hX hm hν index hindex]
  letI (a : ι) : IsProbabilityMeasure ((Measure.pi fun _ : block a ↦ ν).map (stat a)) :=
    Measure.isProbabilityMeasure_map (hstat a).aemeasurable
  exact Measure.pi_map_pi (fun a ↦ (hstat a).aemeasurable)

end Mogulskii

