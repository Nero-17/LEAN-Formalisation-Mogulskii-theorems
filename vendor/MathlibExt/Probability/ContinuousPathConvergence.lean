/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousMapBorel
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Weak convergence of continuous-path laws

For a fixed positive horizon, tightness of probability laws on
`C(Set.Icc 0 T, ℝ)` and weak convergence of every finite evaluation
pushforward imply weak convergence of the path laws in the uniform topology.

The proof is the compactness and finite-dimensional identification argument
used in Donsker's theorem: Prokhorov compactness gives a convergent further
subsequence, while projective-limit uniqueness identifies its limit. This
module uses the corresponding public Mathlib APIs directly.
`MathlibExt.Probability.Donsker` imports this module, implements its `T = 1`
extensionality theorem as a wrapper around the generalized result, and proves
Donsker convergence through the criterion below, so the argument lives here
only.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace MathlibExt.Probability.ContinuousPathConvergence

noncomputable section

/-- Pushforward along a measurable map, with the map supplied explicitly. -/
abbrev mapProbability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (f : α → β) (hf : Measurable f) : ProbabilityMeasure β :=
  μ.map hf.aemeasurable

theorem continuousPath_finsetEval_continuous (T : ℝ) (I : Finset (Set.Icc (0 : ℝ) T)) :
    Continuous (fun f : C(Set.Icc (0 : ℝ) T, ℝ) => I.restrict fun t => f t) :=
  continuous_pi fun t => continuous_eval_const (t : Set.Icc (0 : ℝ) T)

abbrev mapFinsetEval (T : ℝ) (I : Finset (Set.Icc (0 : ℝ) T))
    (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ)) : ProbabilityMeasure (I → ℝ) :=
  mapProbability μ _ (continuousPath_finsetEval_continuous T I).measurable

private theorem probabilityMeasure_pi_ext_of_finset_eval
    {ι : Type*} (μ ν : ProbabilityMeasure (ι → ℝ))
    (h : ∀ I : Finset ι,
      mapProbability μ I.restrict (Finset.measurable_restrict I) =
        mapProbability ν I.restrict (Finset.measurable_restrict I)) :
    μ = ν := by
  let P := fun I : Finset ι =>
    ((mapProbability μ I.restrict (Finset.measurable_restrict I) :
      ProbabilityMeasure (I → ℝ)) : Measure (I → ℝ))
  let _ (I : Finset ι) : IsProbabilityMeasure (P I) := by
    exact (μ : Measure (ι → ℝ)).isProbabilityMeasure_map
      (Finset.measurable_restrict I).aemeasurable
  have hμ : IsProjectiveLimit (μ : Measure (ι → ℝ)) P := by
    intro I
    rfl
  have hν : IsProjectiveLimit (ν : Measure (ι → ℝ)) P := by
    intro I
    exact congrArg ProbabilityMeasure.toMeasure (h I).symm
  exact ProbabilityMeasure.toMeasure_injective (hμ.unique hν)

/-- Probability measures on continuous real paths over `[0, T]` are
determined by all of their finite evaluation pushforwards. The empty `Finset`
is included, and repeated coordinates are identified by `Finset`. -/
theorem continuousPath_measure_ext_of_finset_eval (T : ℝ)
    (μ ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (h : ∀ I : Finset (Set.Icc (0 : ℝ) T), mapFinsetEval T I μ = mapFinsetEval T I ν) :
    μ = ν := by
  obtain ⟨s, hs_countable, hs_dense⟩ :=
    TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  let _ : Countable s := hs_countable
  let e := fun f : C(Set.Icc (0 : ℝ) T, ℝ) => fun t : s => f t
  have he : Continuous e :=
    continuous_pi fun t => continuous_eval_const (t : Set.Icc (0 : ℝ) T)
  have he_injective : Function.Injective e := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    apply hs_dense.denseRange_val.equalizer f.continuous g.continuous
    simpa only [e, Function.comp_def] using hfg
  have he_embedding : MeasurableEmbedding e :=
    he.measurableEmbedding he_injective
  have hmap : mapProbability μ e he.measurable = mapProbability ν e he.measurable := by
    apply probabilityMeasure_pi_ext_of_finset_eval
    intro J
    let I := J.image fun t : s => (t : Set.Icc (0 : ℝ) T)
    have hdj (j : J) : (j : Set.Icc (0 : ℝ) T) ∈ I :=
      Finset.mem_image.2 ⟨j, j.2, rfl⟩
    let eI := fun f : C(Set.Icc (0 : ℝ) T, ℝ) =>
      I.restrict (fun t => f t)
    let eJ := fun f : C(Set.Icc (0 : ℝ) T, ℝ) =>
      J.restrict (fun j => f (j : Set.Icc (0 : ℝ) T))
    let r := fun x : I → ℝ => fun j : J =>
      x ⟨(j : Set.Icc (0 : ℝ) T), hdj j⟩
    have heI : Measurable eI :=
      measurable_pi_iff.2 fun t => ContinuousMap.measurable_eval
        (t : Set.Icc (0 : ℝ) T)
    have hr : Measurable r :=
      measurable_pi_iff.2 fun j =>
        measurable_pi_apply
          (⟨(j : Set.Icc (0 : ℝ) T), hdj j⟩ : I)
    have hcomp : r ∘ eI = eJ := by
      funext f j
      rfl
    have hrestrict : J.restrict ∘ e = eJ := by
      funext f j
      rfl
    have heJ : Measurable eJ := hrestrict ▸ (Finset.measurable_restrict J).comp he.measurable
    have hμdense : mapProbability (mapProbability μ e he.measurable) J.restrict
        (Finset.measurable_restrict J) = mapProbability μ eJ heJ := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [mapProbability, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (Finset.measurable_restrict J) he.measurable,
        hrestrict]
    have hνdense : mapProbability (mapProbability ν e he.measurable) J.restrict
        (Finset.measurable_restrict J) = mapProbability ν eJ heJ := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [mapProbability, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (Finset.measurable_restrict J) he.measurable,
        hrestrict]
    have hμcomp : mapProbability (mapProbability μ eI heI) r hr = mapProbability μ eJ heJ := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [mapProbability, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map hr heI, hcomp]
    have hνcomp : mapProbability (mapProbability ν eI heI) r hr = mapProbability ν eJ heJ := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [mapProbability, ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map hr heI, hcomp]
    calc
      _ = mapProbability μ eJ heJ := hμdense
      _ = mapProbability (mapProbability μ eI heI) r hr := hμcomp.symm
      _ = mapProbability (mapProbability ν eI heI) r hr :=
        congrArg (fun ρ => mapProbability ρ r hr) (h I)
      _ = mapProbability ν eJ heJ := hνcomp
      _ = _ := hνdense.symm
  apply ProbabilityMeasure.toMeasure_injective
  apply he_embedding.map_injective
  simpa only [mapProbability, ProbabilityMeasure.toMeasure_map] using
    congrArg ProbabilityMeasure.toMeasure hmap

/-- Let `T > 0`. A tight sequence of probability laws on
`C(Set.Icc 0 T, ℝ)` converges weakly to `μ` in the uniform topology if every
finite evaluation pushforward converges weakly to the corresponding
pushforward of `μ`.

This is a condition-to-convergence criterion, not a process convergence
theorem: applications must separately prove tightness and all finite-dimensional
convergences for their constructed laws. -/
theorem tendsto_continuousPath_of_tight_of_finset_eval (T : ℝ) (_hT : 0 < T)
    (μs : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ)) :
        Measure C(Set.Icc (0 : ℝ) T, ℝ)) | ν ∈ Set.range μs})
    (hfdd : ∀ I : Finset (Set.Icc (0 : ℝ) T),
      Tendsto (fun n => mapFinsetEval T I (μs n)) atTop (𝓝 (mapFinsetEval T I μ))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hcompact : IsCompact (closure (Set.range μs)) :=
    isCompact_closure_of_isTightMeasureSet htight
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hmem : ∀ n, μs (ns n) ∈ closure (Set.range μs) := fun n =>
    subset_closure (Set.mem_range_self (ns n))
  obtain ⟨ν, -, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hnsφ : Tendsto (fun n => ns (φ n)) atTop atTop :=
    hns.comp hφ.tendsto_atTop
  have hν : ν = μ := by
    apply continuousPath_measure_ext_of_finset_eval T
    intro I
    let e := fun f : C(Set.Icc (0 : ℝ) T, ℝ) =>
      I.restrict (fun t => f t)
    have he : Continuous e :=
      continuous_pi fun t => continuous_eval_const
        (t : Set.Icc (0 : ℝ) T)
    have hcluster : Tendsto
        (fun n => mapFinsetEval T I (μs (ns (φ n)))) atTop (𝓝 (mapFinsetEval T I ν)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n => μs (ns (φ n))) ν hconv he
    have hlimit : Tendsto
        (fun n => mapFinsetEval T I (μs (ns (φ n)))) atTop (𝓝 (mapFinsetEval T I μ)) := by
      simpa only [e, Function.comp_def] using (hfdd I).comp hnsφ
    exact tendsto_nhds_unique hcluster hlimit
  simpa only [Function.comp_def, hν] using hconv

end

end MathlibExt.Probability.ContinuousPathConvergence

