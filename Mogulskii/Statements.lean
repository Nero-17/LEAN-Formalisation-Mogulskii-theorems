import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Topology Interval

namespace Mogulskii

universe u

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev WalkPath (d : ℕ) := C(UnitInterval, EuclideanSpace ℝ (Fin d))

local instance statementsEuclideanMeasurableSpace {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance statementsWalkPathMeasurableSpace {d : ℕ} : MeasurableSpace (WalkPath d) := borel _

/-- Partial sums of increments indexed from zero. -/
def partialSum {Ω E : Type*} [AddCommMonoid E] (X : ℕ → Ω → E)
    (k : ℕ) (ω : Ω) : E :=
  ∑ j ∈ Finset.range k, X j ω

/-- The polygonal interpolation before restriction to the unit interval. -/
noncomputable def interpolate {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) (t : ℝ) : E :=
  (n : ℝ)⁻¹ •
    (partialSum X ⌊(n : ℝ) * t⌋₊ ω +
      ((n : ℝ) * t - (⌊(n : ℝ) * t⌋₊ : ℝ)) • X ⌊(n : ℝ) * t⌋₊ ω)

/-- An LDP at speed `n`, expressed by eventual exponential comparisons.
The real comparison parameter also describes an infinite infimum of the rate. -/
def HasSpeedNLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (laws : ℕ → Measure E) (rate : E → ℝ≥0∞) : Prop :=
  (∀ F : Set E, IsClosed F → ∀ r : ℝ, (r : EReal) <
      ⨅ x ∈ F, (rate x : EReal) →
    ∀ᶠ n : ℕ in atTop, laws n F ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r))) ∧
  (∀ U : Set E, IsOpen U → ∀ r : ℝ, (⨅ x ∈ U, (rate x : EReal)) <
      (r : EReal) →
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) ≤ laws n U)

noncomputable def cramerRate {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ θ : EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal (inner ℝ θ v - Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ))

theorem lowerSemicontinuous_cramerRate {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) :
    LowerSemicontinuous (cramerRate μ X) := by
  unfold cramerRate
  refine lowerSemicontinuous_iSup fun θ => ?_
  apply Continuous.lowerSemicontinuous
  exact ENNReal.continuous_ofReal.comp
    ((continuous_const.inner continuous_id).sub continuous_const)

/-- A bound on the log moment generating function on a sphere gives a linear
lower bound on the rate with slope equal to the radius. -/
theorem ofReal_norm_sub_le_cramerRate {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (h : ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = R →
      Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ) ≤ M) :
    ENNReal.ofReal (R * ‖v‖ - M) ≤ cramerRate μ X v := by
  by_cases hv : v = 0
  · rw [hv, norm_zero, mul_zero, zero_sub, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hM)]
    exact zero_le
  let θ := (R / ‖v‖) • v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hθ : ‖θ‖ = R := by
    dsimp [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR (norm_nonneg _))]
    exact div_mul_cancel₀ R hn
  have hi : inner ℝ θ v = R * ‖v‖ := by
    dsimp [θ]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  calc
    ENNReal.ofReal (R * ‖v‖ - M) ≤
      ENNReal.ofReal (inner ℝ θ v - Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ)) := by
      rw [hi]
      exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (h θ hθ) _)
    _ ≤ cramerRate μ X v := le_iSup (fun η : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (inner ℝ η v - Real.log (∫ ω, Real.exp (inner ℝ η (X ω)) ∂μ))) θ

/-- An affine minorant of the Cramér rate can be integrated over any finite interval. -/
theorem affineIntegral_le_cramerAction {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) {v : ℝ → EuclideanSpace ℝ (Fin d)}
    {s t : ℝ} (hv : IntegrableOn v (Ioc s t)) :
    ENNReal.ofReal (∫ x in Ioc s t,
      (inner ℝ θ (v x) - Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ))) ≤
      ∫⁻ x in Ioc s t, cramerRate μ X (v x) := by
  let f := fun x => inner ℝ θ (v x) - Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ)
  change ENNReal.ofReal (∫ x, f x ∂(volume.restrict (Ioc s t))) ≤ _
  have hi : Integrable f (volume.restrict (Ioc s t)) := by
    exact (Integrable.const_inner θ hv).sub (integrable_const _)
  calc
    ENNReal.ofReal (∫ x, f x ∂(volume.restrict (Ioc s t))) ≤
        ENNReal.ofReal (∫ x, max (f x) 0 ∂(volume.restrict (Ioc s t))) :=
      ENNReal.ofReal_le_ofReal (integral_mono hi (hi.sup (integrable_const 0))
        fun x => le_max_left _ _)
    _ = ∫⁻ x in Ioc s t, ENNReal.ofReal (max (f x) 0) :=
      ofReal_integral_eq_lintegral_ofReal (hi.sup (integrable_const 0))
        (Filter.Eventually.of_forall fun x => le_max_right _ _)
    _ ≤ ∫⁻ x in Ioc s t, cramerRate μ X (v x) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (max (f x) 0) ≤ cramerRate μ X (v x)
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
      exact le_iSup (fun η : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (inner ℝ η (v x) -
          Real.log (∫ ω, Real.exp (inner ℝ η (X ω)) ∂μ))) θ

/-- Jensen's inequality for the possibly infinite Cramér rate. -/
theorem cramerRate_integral_le {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {d : ℕ} (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (ν : Measure A) [IsProbabilityMeasure ν]
    {v : A → EuclideanSpace ℝ (Fin d)} (hv : Integrable v ν) :
    cramerRate μ X (∫ x, v x ∂ν) ≤ ∫⁻ x, cramerRate μ X (v x) ∂ν := by
  unfold cramerRate
  refine iSup_le fun θ => ?_
  let c := Real.log (∫ ω, Real.exp (inner ℝ θ (X ω)) ∂μ)
  let f := fun x => inner ℝ θ (v x) - c
  have hi : Integrable f ν := (Integrable.const_inner θ hv).sub (integrable_const c)
  have heq : (∫ x, f x ∂ν) = inner ℝ θ (∫ x, v x ∂ν) - c := by
    change (∫ x, inner ℝ θ (v x) - c ∂ν) = _
    rw [integral_sub (Integrable.const_inner θ hv) (integrable_const c), integral_inner hv]
    simp
  change ENNReal.ofReal (inner ℝ θ (∫ x, v x ∂ν) - c) ≤ _
  rw [← heq]
  have hm : Integrable (fun x => max (f x) 0) ν := hi.sup (integrable_const 0)
  calc
    ENNReal.ofReal (∫ x, f x ∂ν) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂ν) :=
      ENNReal.ofReal_le_ofReal (integral_mono hi hm fun x => le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂ν :=
      ofReal_integral_eq_lintegral_ofReal hm
        (Filter.Eventually.of_forall fun x => le_max_right _ _)
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (max (f x) 0) ≤ _
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
      exact le_iSup (fun η : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (inner ℝ η (v x) -
          Real.log (∫ ω, Real.exp (inner ℝ η (X ω)) ∂μ))) θ

/-- On a finite interval the action of the secant is at most the integral action. -/
theorem cramerRate_secant_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    {v : ℝ → EuclideanSpace ℝ (Fin d)} {s t : ℝ} (hst : s < t)
    (hv : IntegrableOn v (Ioc s t)) :
    ENNReal.ofReal (t - s) * cramerRate μ X ((t - s)⁻¹ • ∫ x in Ioc s t, v x) ≤
      ∫⁻ x in Ioc s t, cramerRate μ X (v x) := by
  have hpos : 0 < t - s := sub_pos.mpr hst
  let c := ENNReal.ofReal (t - s)
  have h0 : c ≠ 0 := by simp [c, hpos.not_ge]
  have ht : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvMass : (volume.restrict (Ioc s t)) univ = c := by
    simp [c, Real.volume_Ioc]
  let ν := c⁻¹ • volume.restrict (Ioc s t)
  haveI : IsProbabilityMeasure ν := ⟨by
    change c⁻¹ * (volume.restrict (Ioc s t)) univ = 1
    rw [hvMass, ENNReal.inv_mul_cancel h0 ht]⟩
  have hν : Integrable v ν :=
    (integrable_smul_measure (by simp [ht]) (by simp [h0])).2 hv
  have hJ := cramerRate_integral_le μ X ν hν
  have hmean : (∫ x, v x ∂ν) = (t - s)⁻¹ • ∫ x in Ioc s t, v x := by
    rw [show ν = c⁻¹ • volume.restrict (Ioc s t) from rfl, integral_smul_measure]
    simp [c, hpos.le]
  rw [hmean, show ν = c⁻¹ • volume.restrict (Ioc s t) from rfl, lintegral_smul_measure] at hJ
  calc
    _ ≤ c * (c⁻¹ * ∫⁻ x in Ioc s t, cramerRate μ X (v x)) :=
      mul_le_mul_right hJ c
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- The rate via integrable velocities. The infimum of the empty set is infinity.
An integrable velocity giving the path as its primitive is unique almost everywhere. -/
noncomputable def pathRate {d : ℕ} (rate : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (φ : WalkPath d) : ℝ≥0∞ :=
  ⨅ (v : ℝ → EuclideanSpace ℝ (Fin d))
      (_ : IntegrableOn v (Icc 0 1))
      (_ : ∀ t : UnitInterval, φ t = ∫ s in (0 : ℝ)..(t : ℝ), v s),
    ∫⁻ s in Icc 0 1, rate (v s)

theorem cramerRate_pathSecant_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d)) (φ : WalkPath d)
    {s t : UnitInterval} (hst : (s : ℝ) < (t : ℝ)) :
    ENNReal.ofReal ((t : ℝ) - s) *
      cramerRate μ X (((t : ℝ) - s)⁻¹ • (φ t - φ s)) ≤ pathRate (cramerRate μ X) φ := by
  unfold pathRate
  refine le_iInf fun v => le_iInf fun hv => le_iInf fun hφ => ?_
  have hs : IntegrableOn v (Ioc (0 : ℝ) (s : ℝ)) :=
    hv.mono_set fun x hx => ⟨hx.1.le, hx.2.trans s.property.2⟩
  have hst' : IntegrableOn v (Ioc (s : ℝ) (t : ℝ)) :=
    hv.mono_set fun x hx => ⟨s.property.1.trans hx.1.le, hx.2.trans t.property.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le s.property.1).2 hs)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).2 hst')
  have hd : φ t - φ s = ∫ x in Ioc (s : ℝ) (t : ℝ), v x := by
    rw [hφ t, hφ s, ← hadd, add_sub_cancel_left, intervalIntegral.integral_of_le hst.le]
  rw [hd]
  exact (cramerRate_secant_le μ X hst hst').trans
    (lintegral_mono_set fun x hx => ⟨s.property.1.trans hx.1.le, hx.2.trans t.property.2⟩)

/-- Summing secant costs on consecutive intervals is bounded by the action on their union. -/
theorem sum_cramerRate_secants_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    {v : ℝ → EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (hv : IntegrableOn v (Ioc a b))
    (p : ℕ → ℝ) (n : ℕ) (hp : StrictMono p) (ha : a ≤ p 0) (hb : p n ≤ b) :
    ∑ k ∈ Finset.range n, ENNReal.ofReal (p (k + 1) - p k) *
      cramerRate μ X ((p (k + 1) - p k)⁻¹ • ∫ x in Ioc (p k) (p (k + 1)), v x) ≤
    ∫⁻ x in Ioc (p 0) (p n), cramerRate μ X (v x) := by
  induction n with
  | zero => simpa using (show (0 : ℝ≥0∞) ≤ ∫⁻ x in Ioc (p 0) (p 0),
      cramerRate μ X (v x) from zero_le)
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep : p n < p (n + 1) := hp (Nat.lt_succ_self n)
      have hinc : p 0 ≤ p n := hp.monotone (Nat.zero_le n)
      have hsub : Ioc (p n) (p (n + 1)) ⊆ Ioc a b :=
        fun x hx => ⟨(ha.trans hinc).trans_lt hx.1, hx.2.trans hb⟩
      have hsec := cramerRate_secant_le μ X hstep (hv.mono_set hsub)
      have hdisj : Disjoint (Ioc (p 0) (p n)) (Ioc (p n) (p (n + 1))) := by
        refine Set.disjoint_left.mpr fun x hx hy => ?_
        exact (not_lt_of_ge hx.2) hy.1
      calc
        _ ≤ (∫⁻ x in Ioc (p 0) (p n), cramerRate μ X (v x)) +
            ∫⁻ x in Ioc (p n) (p (n + 1)), cramerRate μ X (v x) :=
          add_le_add (ih (hstep.le.trans hb)) hsec
        _ = _ := by
          rw [← lintegral_union measurableSet_Ioc hdisj, Ioc_union_Ioc_eq_Ioc hinc hstep.le]

/-- The full target for the path large-deviation theorem in finite dimension. -/
def PathLargeDeviationStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
    (∀ k, Measurable (X k)) → iIndepFun X μ →
    (∀ k, IdentDistrib (X k) (X 0) μ μ) →
    (∀ θ : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp (inner ℝ θ (X 0 ω))) μ) →
    ∃ paths : ℕ → Ω → WalkPath d,
      (∀ n, Measurable (paths n)) ∧
      (∀ n ω (t : UnitInterval), paths n ω t = interpolate X n ω t) ∧
      HasSpeedNLDP (fun n => μ.map (paths n)) (pathRate (cramerRate μ (X 0))) ∧
      LowerSemicontinuous (pathRate (cramerRate μ (X 0))) ∧
      (∀ r : ℝ≥0, IsCompact {φ | pathRate (cramerRate μ (X 0)) φ ≤ (r : ℝ≥0∞)})

def tubeEvent {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f g : ℝ → ℝ)
    (n : ℕ) : Set Ω :=
  {ω | ∀ k ≤ n, a n * f ((k : ℝ) / n) ≤ partialSum X k ω ∧
    partialSum X k ω ≤ a n * g ((k : ℝ) / n)}

theorem measurable_partialSum {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable (X k)) (k : ℕ) : Measurable (partialSum X k) := by
  induction k with
  | zero =>
      have h : partialSum X 0 = (fun _ : Ω => (0 : ℝ)) := by
        funext ω
        simp [partialSum]
      rw [h]
      exact measurable_const
  | succ k hk =>
      have h : partialSum X (k + 1) = fun ω => partialSum X k ω + X k ω := by
        funext ω
        simp only [partialSum, Finset.sum_range_succ]
      rw [h]
      exact hk.add (hX k)

theorem measurableSet_tubeEvent {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable (X k)) (a : ℕ → ℝ) (f g : ℝ → ℝ) (n : ℕ) :
    MeasurableSet (tubeEvent X a f g n) := by
  have h (k : ℕ) :
      MeasurableSet {ω | a n * f ((k : ℝ) / n) ≤ partialSum X k ω ∧
        partialSum X k ω ≤ a n * g ((k : ℝ) / n)} :=
    (measurableSet_le measurable_const (measurable_partialSum hX k)).inter
      (measurableSet_le (measurable_partialSum hX k) measurable_const)
  have hEq : tubeEvent X a f g n =
      ⋂ k : Fin (n + 1), {ω | a n * f ((k.val : ℝ) / n) ≤ partialSum X k.val ω ∧
        partialSum X k.val ω ≤ a n * g ((k.val : ℝ) / n)} := by
    ext ω
    simp only [tubeEvent, mem_setOf_eq, mem_iInter]
    exact ⟨fun hω k => hω k.val (Nat.le_of_lt_succ k.isLt),
      fun hω k hk => hω ⟨k, Nat.lt_succ_of_le hk⟩⟩
  rw [hEq]
  exact MeasurableSet.iInter fun k => h k.val

/-- The full moving-tube small-deviation target. The two exponential bounds
express the logarithmic limit without assigning a real logarithm to zero. -/
def SmallDeviationStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (f g : ℝ → ℝ),
    (∀ k, Measurable (X k)) → iIndepFun X μ →
    (∀ k, IdentDistrib (X k) (X 0) μ μ) →
    MemLp (X 0) 2 μ → (∫ ω, X 0 ω ∂μ) = 0 →
    0 < ProbabilityTheory.variance (X 0) μ →
    (∀ n, 0 < a n) → Tendsto a atTop atTop →
    Tendsto (fun n : ℕ => a n / Real.sqrt n) atTop (𝓝 0) →
    ContinuousOn f (Icc 0 1) → ContinuousOn g (Icc 0 1) →
    (∀ t ∈ Icc (0 : ℝ) 1, f t < g t) → f 0 < 0 → 0 < g 0 →
    let rate := Real.pi ^ 2 * ProbabilityTheory.variance (X 0) μ / 2 *
      ∫ t in (0 : ℝ)..1, (g t - f t)⁻¹ ^ 2
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(rate + ε) * ((n : ℝ) / a n ^ 2))) ≤
        μ (tubeEvent X a f g n) ∧
      μ (tubeEvent X a f g n) ≤
        ENNReal.ofReal (Real.exp (-(rate - ε) * ((n : ℝ) / a n ^ 2)))

end Mogulskii
