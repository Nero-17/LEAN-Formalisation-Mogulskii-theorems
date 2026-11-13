import Mogulskii.ActionIdentity
import Mogulskii.Cramer
import Mogulskii.EuclideanNormMGF
import Mogulskii.PathLDP
import Mogulskii.PolygonAction
import Mathlib.Analysis.InnerProductSpace.Dual

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace Mogulskii

local instance pathTheoremEuclideanMeasurableSpace {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance pathTheoremEuclideanBorelSpace {d : ℕ} :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
local instance pathTheoremWalkPathMeasurableSpace {d : ℕ} : MeasurableSpace (WalkPath d) :=
  borel _
local instance pathTheoremWalkPathBorelSpace {d : ℕ} : BorelSpace (WalkPath d) := ⟨rfl⟩

theorem cramerRateLaw_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)} (hX : Measurable X) :
    cramerRateLaw (μ.map X) = cramerRate μ X := by
  funext v
  have hcgf (θ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
      cgf θ (μ.map X) 1 = Real.log (∫ ω, Real.exp (θ (X ω)) ∂μ) := by
    unfold cgf mgf
    simp only [one_mul]
    congr 1
    exact integral_map hX.aemeasurable (f := fun y => Real.exp (θ y))
      ((Real.continuous_exp.comp θ.continuous).measurable.aestronglyMeasurable)
  unfold cramerRateLaw cramerRate
  simp_rw [hcgf]
  apply le_antisymm
  · refine iSup_le fun θ => ?_
    exact le_iSup_of_le ((InnerProductSpace.toDual ℝ _).symm θ) (by
      simp only [InnerProductSpace.toDual_symm_apply, le_refl])
  · refine iSup_le fun θ => ?_
    exact le_iSup_of_le (InnerProductSpace.toDual ℝ _ θ) (by
      simp only [InnerProductSpace.toDual_apply_apply, le_refl])

private theorem polygon_eq_interpolate {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) (t : UnitTime) :
    polygon n (fun i => X i ω) t = interpolate X n ω t := by
  by_cases hn : n = 0
  · simp [hn, polygon, interpolate]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnonneg : 0 ≤ (n : ℝ) * (t : ℝ) := mul_nonneg hn'.le t.property.1
  have hle : (n : ℝ) * (t : ℝ) ≤ n := mul_le_of_le_one_right hn'.le t.property.2
  by_cases hlt : (n : ℝ) * (t : ℝ) < n
  · exact polygon_between _ _ ((Nat.floor_lt hnonneg).mpr hlt) _ _
      (Nat.floor_le hnonneg) (Nat.lt_floor_add_one _).le
  · have hnt : (n : ℝ) * (t : ℝ) = n := le_antisymm hle (le_of_not_gt hlt)
    have ht : (t : ℝ) = (n : ℝ) / n := by
      apply (eq_div_iff hn'.ne').mpr
      simpa only [mul_comm] using hnt
    have he : t = ⟨(n : ℝ) / n, by simp [hn'.ne']⟩ := Subtype.ext ht
    rw [he, polygon_mesh _ _ le_rfl hn]
    simp [interpolate, partialSum, hn'.ne', Nat.floor_natCast]

private theorem coe_iInf_rate {E : Type*} (I : E → ℝ≥0∞) (A : Set E) :
    ((⨅ x ∈ A, I x : ℝ≥0∞) : EReal) = ⨅ x ∈ A, (I x : EReal) := by
  apply le_antisymm
  · exact le_iInf₂ fun x hx => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iInf₂_le x hx)
  · have hnonneg : (0 : EReal) ≤ ⨅ x ∈ A, (I x : EReal) :=
      le_iInf₂ fun x _ => EReal.coe_ennreal_nonneg (I x)
    rw [← EReal.coe_toENNReal hnonneg, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun x hx => ?_
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal (iInf₂_le x hx :
        (⨅ y ∈ A, (I y : EReal)) ≤ (I x : EReal))

private theorem eventually_exp_neg_mul_le {q : ℝ} (hq : 0 < q) {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n : ℝ) * q)) ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hpos : 0 < c.toReal := ENNReal.toReal_pos hc htop
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log c.toReal / q)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound := (div_lt_iff₀ hq).mp (hN.trans_le (by exact_mod_cast hn : (N : ℝ) ≤ n))
  have hexp := Real.exp_le_exp.mpr (show -(n : ℝ) * q ≤ Real.log c.toReal by linarith)
  rw [Real.exp_log hpos] at hexp
  exact (ENNReal.ofReal_le_ofReal hexp).trans_eq (ENNReal.ofReal_toReal htop)

private theorem exp_neg_mul_add (n : ℕ) (r q : ℝ) :
    ENNReal.ofReal (Real.exp (-(n : ℝ) * (r + q))) =
      ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) * q)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, mul_add]

/-- A strict slack in each exponent absorbs the positive finite prefactors. -/
theorem HasExponentialBounds.hasSpeedNLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {P : ℕ → Measure E} {I : E → ℝ≥0∞} (h : HasExponentialBounds P I) :
    HasSpeedNLDP P I := by
  constructor
  · intro F hF r hr
    rw [← coe_iInf_rate] at hr
    obtain ⟨s, hrs, hs⟩ := EReal.exists_between_coe_real hr
    have hgap : 0 < s - r := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hrs)
    obtain ⟨c, hc, hupper⟩ := h.upper hF hs
    simp only [← neg_mul] at hupper
    by_cases hc0 : c = 0
    · filter_upwards [hupper] with n hn
      rw [hc0, zero_mul] at hn
      exact hn.trans zero_le
    filter_upwards [hupper, eventually_exp_neg_mul_le hgap (ENNReal.inv_ne_zero.mpr hc)]
      with n hn hsmall
    refine hn.trans ?_
    rw [show s = r + (s - r) by ring, exp_neg_mul_add, mul_left_comm c]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * r)) * (c * c⁻¹) :=
        mul_le_mul_right (mul_le_mul_right hsmall _) _
      _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hc, mul_one]
  · intro U hU r hr
    have hx : ∃ x ∈ U, (I x : EReal) < (r : EReal) := by
      by_contra hnone
      exact (not_le_of_gt hr) (le_iInf₂ fun x hxU => le_of_not_gt fun hx => hnone ⟨x, hxU, hx⟩)
    obtain ⟨x, hxU, hx⟩ := hx
    obtain ⟨s, hxs, hsr⟩ := EReal.exists_between_coe_real hx
    have hgap : 0 < r - s := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hsr)
    obtain ⟨c, hc, hlower⟩ := h.lower (hU.mem_nhds hxU) hxs
    simp only [← neg_mul] at hlower
    filter_upwards [hlower, eventually_exp_neg_mul_le hgap hc] with n hn hsmall
    refine le_trans ?_ hn
    calc
      _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * s)) *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (r - s))) := by
        rw [← exp_neg_mul_add, show s + (r - s) = r by ring]
      _ ≤ _ := (mul_le_mul_right hsmall _).trans_eq (mul_comm _ _)

/-- Mogulskii's theorem for i.i.d. increments with every directional exponential moment. -/
theorem pathLargeDeviation : PathLargeDeviationStatement := by
  intro Ω _ μ _ d X hX hInd hId hMom
  let ν := μ.map (X 0)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hmeas (q : ℝ) : Measurable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (q * ‖y‖)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
  have hExp (q : ℝ) (hq : 0 ≤ q) (i : ℕ) :
      Integrable (fun ω => Real.exp (q * ‖X i ω‖)) μ :=
    ((hId i).comp (hmeas q)).integrable_iff.mpr
      (integrable_exp_mul_norm_of_inner (hX 0) hMom hq)
  have hExpLaw (q : ℝ) (hq : 0 ≤ q) :
      Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (q * ‖y‖)) ν :=
    (integrable_map_measure (hmeas q).aestronglyMeasurable (hX 0).aemeasurable).mpr
      (hExp q hq 0)
  have hrate : cramerRateLaw ν = cramerRate μ (X 0) := cramerRateLaw_map_eq (hX 0)
  have hmean := hasExponentialBounds_meanLaw (ν := ν) hExpLaw
  rw [hrate] at hmean
  have hgood : GoodRate (pathRate (cramerRate μ (X 0))) := by
    apply goodRate_cramerPathRate
    intro q hq
    refine ⟨max 0 (cgf (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) ν q), le_max_left _ _, fun v => ?_⟩
    rw [← hrate]
    exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left (le_max_right _ _) _)).trans
      (cramerRate_ge hq.le (hExpLaw q hq.le) v)
  have hldp := hasExponentialBounds_polygon_of_mean (ν := ν) hX hInd (fun i => (hId i).map_eq)
    hExp hmean hgood (fun m hm => pathRate_gridPolygon_le hm _)
    (fun m hm => imageRate_gridPolygon_meshInterpolate_le hm μ (X 0))
  refine ⟨(fun n ω => polygon n (fun i => X i ω)), ?_, polygon_eq_interpolate X,
    hldp.hasSpeedNLDP, hgood.lowerSemicontinuous, fun r => hgood.isCompact_sublevel r ENNReal.coe_ne_top⟩
  exact fun n => (continuous_polygon n).measurable.comp (measurable_pi_lambda _ hX)

end Mogulskii
