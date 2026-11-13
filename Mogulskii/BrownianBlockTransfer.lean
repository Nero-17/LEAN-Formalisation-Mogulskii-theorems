import Mogulskii.BlockTransfer
import Mogulskii.SingleBlockBounds
import Mogulskii.BrownianEndpoint
import MathlibExt.Probability.ContinuousMapBorel
import MathlibExt.Probability.Donsker
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology
open MathlibExt.Probability.DonskerWanted

namespace Mogulskii.SmallDeviation

local notation "UnitInterval" => Set.Icc (0 : ℝ) 1

private theorem iccToNNReal_right : iccToNNReal unitRightEndpoint = 1 := by
  exact NNReal.eq rfl

private theorem forall_time_mul_iff {T : ℝ≥0} (hT : T ≠ 0) {p : ℝ≥0 → Prop} :
    (∀ t : UnitInterval, p (T * iccToNNReal t)) ↔ ∀ s ≤ T, p s := by
  have hTreal : (0 : ℝ) < T := NNReal.coe_pos.2 (pos_iff_ne_zero.mpr hT)
  constructor
  · intro h s hs
    let t : UnitInterval :=
      ⟨(s : ℝ) / (T : ℝ), div_nonneg (NNReal.coe_nonneg s) hTreal.le,
        (div_le_one hTreal).2 (by exact_mod_cast hs)⟩
    have ht : T * iccToNNReal t = s := by
      apply NNReal.eq
      change (T : ℝ) * ((s : ℝ) / (T : ℝ)) = (s : ℝ)
      rw [mul_comm, div_mul_cancel₀ _ hTreal.ne']
    simpa only [ht] using h t
  · intro h t
    apply h
    have ht : iccToNNReal t ≤ 1 := NNReal.coe_le_one.mp (show (t : ℝ) ≤ 1 from t.2.2)
    simpa using (mul_le_mul_of_nonneg_left ht (show 0 ≤ T from zero_le))

private theorem brownian_rescale_apply {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T : ℝ≥0} (hT : T ≠ 0) (t : UnitInterval) (ω : Ω) :
    (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * (T * iccToNNReal t)) ω =
      Real.sqrt (T : ℝ) * B (iccToNNReal t) ω := by
  rw [NNReal.coe_inv, Real.sqrt_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ hT, one_mul]

private theorem brownian_path_closed_eq {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {Y : Ω → C(UnitInterval, ℝ)}
    (hY : ∀ᵐ ω ∂Q, ∀ t, Y ω t = B (iccToNNReal t) ω)
    {T : ℝ≥0} (hT : T ≠ 0) (x l u : ℝ) :
    Q {ω | ∀ t, Real.sqrt (T : ℝ) * Y ω t + x ∈ Icc l u} =
      Q (intervalSurvival
        (fun s ω => x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * s) ω) l u T) := by
  apply measure_congr
  filter_upwards [hY] with ω hω
  change (∀ t, Real.sqrt (T : ℝ) * Y ω t + x ∈ Icc l u) =
    (∀ s ≤ T, x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * s) ω ∈ Icc l u)
  simp only [hω]
  rw [← forall_time_mul_iff hT]
  simp only [brownian_rescale_apply B hT]
  simp_rw [add_comm x]

private theorem brownian_path_endpoint_lower {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {Y : Ω → C(UnitInterval, ℝ)}
    (hY : ∀ᵐ ω ∂Q, ∀ t, Y ω t = B (iccToNNReal t) ω)
    {T : ℝ≥0} (hT : T ≠ 0) {x l u c d L U C D : ℝ}
    (hL : l < L) (hU : U < u) (hC : c < C) (hD : D < d) :
    Q (intervalSurvival
        (fun s ω => x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * s) ω) L U T ∩
        {ω | x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * T) ω ∈ Icc C D}) ≤
      Q {ω | (∀ t, Real.sqrt (T : ℝ) * Y ω t + x ∈ Ioo l u) ∧
        Real.sqrt (T : ℝ) * Y ω unitRightEndpoint + x ∈ Ioo c d} := by
  apply measure_mono_ae
  filter_upwards [hY] with ω hω h
  change (∀ s ≤ T, x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * s) ω ∈ Icc L U) ∧
    x + (Real.sqrt ((T⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (T⁻¹ * T) ω ∈ Icc C D at h
  have hsurv (t : UnitInterval) : x + Real.sqrt (T : ℝ) * Y ω t ∈ Icc L U := by
    rw [hω, ← brownian_rescale_apply B hT]
    apply h.1
    have ht : iccToNNReal t ≤ 1 := NNReal.coe_le_one.mp (show (t : ℝ) ≤ 1 from t.2.2)
    simpa using (mul_le_mul_of_nonneg_left ht (show 0 ≤ T from zero_le))
  have hend : x + Real.sqrt (T : ℝ) * Y ω unitRightEndpoint ∈ Icc C D := by
    rw [hω, ← brownian_rescale_apply B hT, iccToNNReal_right, mul_one]
    exact h.2
  exact ⟨fun t => by simpa only [add_comm x] using
      (show x + Real.sqrt (T : ℝ) * Y ω t ∈ Ioo l u from
        ⟨hL.trans_le (hsurv t).1, (hsurv t).2.trans_lt hU⟩),
    by simpa only [add_comm x] using
      (show x + Real.sqrt (T : ℝ) * Y ω unitRightEndpoint ∈ Ioo c d from
        ⟨hC.trans_le hend.1, hend.2.trans_lt hD⟩)⟩

private theorem uniform_upper_exponent_of_prefactor {c r r' : ℝ}
    (hc : 0 < c) (h : r' < r) :
    ∀ᶠ T : ℝ in atTop, c * Real.exp (-r * T) < Real.exp (-r' * T) := by
  have hlim : Tendsto (fun T : ℝ => (r - r') * T) atTop atTop :=
    tendsto_id.const_mul_atTop (sub_pos.mpr h)
  filter_upwards [hlim.eventually (eventually_gt_atTop (Real.log c))] with T hT
  have h := (Real.log_lt_iff_lt_exp hc).mp hT
  have h' := mul_lt_mul_of_pos_right h (Real.exp_pos (-r * T))
  rw [← Real.exp_add] at h'
  rwa [show (r - r') * T + -r * T = -r' * T by ring] at h'

private theorem uniform_lower_exponent_of_prefactor {c r r' : ℝ}
    (hc : 0 < c) (h : r < r') :
    ∀ᶠ T : ℝ in atTop, Real.exp (-r' * T) < c * Real.exp (-r * T) := by
  filter_upwards [uniform_upper_exponent_of_prefactor (inv_pos.mpr hc) h] with T hT
  have h' := mul_lt_mul_of_pos_left hT hc
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h'
  exact h'

private theorem intervalEigenvalue_widen {l u η : ℝ} (hlu : l < u) (hη : 0 < η) :
    ∃ d > 0, intervalEigenvalue 1 l u - η < intervalEigenvalue 1 (l - d) (u + d) := by
  have hcont : ContinuousAt (fun d : ℝ => intervalEigenvalue 1 (l - d) (u + d)) 0 := by
    unfold intervalEigenvalue
    apply ContinuousAt.div
    · exact continuousAt_const
    · fun_prop
    · simp [sub_ne_zero.mpr hlu.ne']
  have hnear : ∀ᶠ d : ℝ in 𝓝 0,
      intervalEigenvalue 1 l u - η < intervalEigenvalue 1 (l - d) (u + d) := by
    have hzero : intervalEigenvalue 1 l u - η < intervalEigenvalue 1 (l - 0) (u + 0) := by
      simpa using sub_lt_self (intervalEigenvalue 1 l u) hη
    exact hcont.eventually_mem (Ioi_mem_nhds hzero)
  obtain ⟨d, hd, hrate⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ioi (0 : ℝ)] 0)).exists
  exact ⟨d, hrate, hd⟩

private theorem intervalEigenvalue_shrink {l u startLo startHi endLo endHi η : ℝ}
    (hleft : l < startLo) (hle : startLo ≤ startHi) (hright : startHi < u)
    (hendLeft : l < endLo) (hendRight : endHi < u) (hη : 0 < η) :
    ∃ d > 0, l + 2 * d < startLo ∧ startHi < u - 2 * d ∧
      l + d < endLo ∧ endHi < u - d ∧
      intervalEigenvalue 1 (l + 2 * d) (u - 2 * d) < intervalEigenvalue 1 l u + η := by
  have hlu := (hleft.trans_le hle).trans hright
  have hcont : ContinuousAt (fun d : ℝ => intervalEigenvalue 1 (l + 2 * d) (u - 2 * d)) 0 := by
    unfold intervalEigenvalue
    apply ContinuousAt.div
    · exact continuousAt_const
    · fun_prop
    · simp [sub_ne_zero.mpr hlu.ne']
  have hnear : ∀ᶠ d : ℝ in 𝓝 0,
      intervalEigenvalue 1 (l + 2 * d) (u - 2 * d) < intervalEigenvalue 1 l u + η := by
    have hzero : intervalEigenvalue 1 (l + 2 * 0) (u - 2 * 0) < intervalEigenvalue 1 l u + η := by
      simpa using lt_add_of_pos_right (intervalEigenvalue 1 l u) hη
    exact hcont.eventually_mem (Iio_mem_nhds hzero)
  have hnear' : ∀ᶠ d : ℝ in 𝓝 0, l + 2 * d < startLo ∧ startHi < u - 2 * d ∧
      l + d < endLo ∧ endHi < u - d := by
    have h1 : ContinuousAt (fun d : ℝ => l + 2 * d) 0 := by fun_prop
    have h2 : ContinuousAt (fun d : ℝ => u - 2 * d) 0 := by fun_prop
    have h3 : ContinuousAt (fun d : ℝ => l + d) 0 := by fun_prop
    have h4 : ContinuousAt (fun d : ℝ => u - d) 0 := by fun_prop
    exact (h1.eventually_mem (Iio_mem_nhds (by simpa using hleft))).and
      ((h2.eventually_mem (Ioi_mem_nhds (by simpa using hright))).and
        ((h3.eventually_mem (Iio_mem_nhds (by simpa using hendLeft))).and
          (h4.eventually_mem (Ioi_mem_nhds (by simpa using hendRight)))))
  obtain ⟨d, hd, hr⟩ := (((hnear'.and hnear).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ioi (0 : ℝ)] 0)).exists
  exact ⟨d, hr, hd.1.1, hd.1.2.1, hd.1.2.2.1, hd.1.2.2.2, hd.2⟩

private theorem intervalEigenvalue_one (l u : ℝ) :
    intervalEigenvalue 1 l u = (Real.pi ^ 2 / 2) / (u - l) ^ 2 := by
  unfold intervalEigenvalue
  rw [mul_one, div_div]

section VarianceOne

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [SecondCountableTopology C(UnitInterval, ℝ)] [MeasurableSpace C(UnitInterval, ℝ)]
    [BorelSpace C(UnitInterval, ℝ)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {B : ℝ≥0 → Ω' → ℝ} {Y : Ω' → C(UnitInterval, ℝ)}
    {a : ℕ → ℝ}

theorem singleBlockUpper_of_donsker (ha : ∀ n, 0 < a n) (haTop : Tendsto a atTop atTop)
    (hD : TendstoInDistribution (fun m => donskerProcess m X) atTop Y (fun _ => μ) Q)
    (hY : ∀ᵐ ω ∂Q, ∀ t, Y ω t = B (iccToNNReal t) ω)
    (hB : IsBrownianReal B Q) (hmB : ∀ t, Measurable (B t)) (hcB : ∀ ω, Continuous (B · ω)) :
    SingleBlockUpper μ X a (Real.pi ^ 2 / 2) := by
  intro l u hlu η hη
  obtain ⟨d, hd, hrate⟩ := intervalEigenvalue_widen hlu hη
  have hleft : l - d < l := sub_lt_self _ hd
  have hright : u < u + d := lt_add_of_pos_right _ hd
  obtain ⟨c, hc, hBound⟩ := uniform_closed_survival_upper (Ω := Ω') hleft hlu.le hright
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    uniform_upper_exponent_of_prefactor hc hrate] with T hT hExp length hlength
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  have hTnn : Tnn ≠ 0 := (NNReal.coe_pos.mp (show 0 < (Tnn : ℝ) from hT)).ne'
  have hBT := hB.smul (c := Tnn⁻¹) (inv_ne_zero hTnn)
  have hmBT (t : ℝ≥0) : Measurable (fun ω => (Real.sqrt ((Tnn⁻¹ : ℝ≥0) : ℝ))⁻¹ *
      B (Tnn⁻¹ * t) ω) := measurable_const.mul (hmB _)
  have hcBT (ω : Ω') : Continuous (fun t => (Real.sqrt ((Tnn⁻¹ : ℝ≥0) : ℝ))⁻¹ *
      B (Tnn⁻¹ * t) ω) := by
    exact continuous_const.mul ((hcB ω).comp (continuous_const.mul continuous_id))
  have hU : ∀ x ∈ Icc l u, Q {ω | ∀ t, Real.sqrt T * Y ω t + x ∈ Icc l u} <
      ENNReal.ofReal (Real.exp (-((Real.pi ^ 2 / 2) / (u - l) ^ 2 - η) * T)) := by
    intro x _
    change Q {ω | ∀ t, Real.sqrt (Tnn : ℝ) * Y ω t + x ∈ Icc l u} < _
    rw [brownian_path_closed_eq hY hTnn]
    apply (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2
    refine (hBound _ Q hBT hmBT hcBT x Tnn).trans_lt ?_
    change c * Real.exp (-intervalEigenvalue 1 (l - d) (u + d) * T) < _
    simpa only [intervalEigenvalue_one l u] using hExp
  let times : ℕ → ℝ := fun n => (length n : ℝ) / a n ^ 2
  have hWalk := eventually_walk_closed_lt_of_donsker hD haTop (times := times) hlength hT
    (isCompact_Icc (a := l) (b := u)) l u hU
  filter_upwards [hWalk] with n hn y
  have hlen : ⌊times n * a n ^ 2⌋₊ = length n := by
    simp [times, div_mul_cancel₀ _ (pow_ne_zero 2 (ha n).ne')]
  let x := y / a n
  have hx : a n * x = y := by
    dsimp [x]
    rw [mul_comm, div_mul_cancel₀ _ (ha n).ne']
  by_cases hxy : x ∈ Icc l u
  · have h := hn x hxy
    rw [hlen, hx] at h
    exact h.le
  · have he : tubeEvent X (length n) y (fun _ => a n * l) (fun _ => a n * u) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hw := hω 0 (Nat.zero_le _)
      have hy : y ∈ Icc (a n * l) (a n * u) := by simpa [walk] using hw
      exact hxy ⟨(le_div_iff₀ (ha n)).2 (by simpa [mul_comm] using hy.1),
        (div_le_iff₀ (ha n)).2 (by simpa [mul_comm] using hy.2)⟩
    rw [he, measure_empty]
    exact zero_le

theorem singleBlockLower_of_donsker (ha : ∀ n, 0 < a n) (haTop : Tendsto a atTop atTop)
    (hD : TendstoInDistribution (fun m => donskerProcess m X) atTop Y (fun _ => μ) Q)
    (hY : ∀ᵐ ω ∂Q, ∀ t, Y ω t = B (iccToNNReal t) ω)
    (hB : IsBrownianReal B Q) (hmB : ∀ t, Measurable (B t)) (hcB : ∀ ω, Continuous (B · ω)) :
    SingleBlockLower μ X a (Real.pi ^ 2 / 2) := by
  intro l u startLo startHi endLo endHi hleft hstart hright hendleft hend hendright η hη
  obtain ⟨d, hd, hLeft, hRight, hEndLeft, hEndRight, hRate⟩ :=
    intervalEigenvalue_shrink hleft hstart hright hendleft hendright hη
  let endpointLo := (2 * endLo + endHi) / 3
  let endpointHi := (endLo + 2 * endHi) / 3
  have hll : l + d < l + 2 * d := by linarith
  have hrr : u - 2 * d < u - d := by linarith
  have hel : l + d < endpointLo := by dsimp [endpointLo]; linarith
  have hew : endpointLo < endpointHi := by dsimp [endpointLo, endpointHi]; linarith
  have her : endpointHi < u - d := by dsimp [endpointHi]; linarith
  obtain ⟨c, hc, hBound⟩ := uniform_closed_survival_with_endpoint_lower (Ω := Ω')
    hll hrr hLeft hstart hRight hel hew her
  have hEig : 0 ≤ intervalEigenvalue 1 (l + 2 * d) (u - 2 * d) := by
    unfold intervalEigenvalue
    positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    uniform_lower_exponent_of_prefactor hc hRate] with T hT hExp length hlength
  have hTpos : 0 < T := zero_lt_one.trans hT
  let Tnn : ℝ≥0 := ⟨T, hTpos.le⟩
  have hTnn : Tnn ≠ 0 := (NNReal.coe_pos.mp (show 0 < (Tnn : ℝ) from hTpos)).ne'
  have hT1 : (1 : ℝ≥0) ≤ Tnn := NNReal.one_le_coe.mp (show 1 ≤ (Tnn : ℝ) from hT.le)
  have hTsum : Tnn - 1 + 1 = Tnn := tsub_add_cancel_of_le hT1
  let BT : ℝ≥0 → Ω' → ℝ :=
    fun t ω => (Real.sqrt ((Tnn⁻¹ : ℝ≥0) : ℝ))⁻¹ * B (Tnn⁻¹ * t) ω
  have hBT : IsBrownianReal BT Q := hB.smul (c := Tnn⁻¹) (inv_ne_zero hTnn)
  have hmBT (t : ℝ≥0) : Measurable (BT t) := measurable_const.mul (hmB _)
  have hcBT (ω : Ω') : Continuous (BT · ω) := by
    exact continuous_const.mul ((hcB ω).comp (continuous_const.mul continuous_id))
  have hL : ∀ x ∈ Icc startLo startHi,
      ENNReal.ofReal (Real.exp (-((Real.pi ^ 2 / 2) / (u - l) ^ 2 + η) * T)) <
      Q {ω | (∀ t, Real.sqrt T * Y ω t + x ∈ Ioo l u) ∧
        Real.sqrt T * Y ω unitRightEndpoint + x ∈ Ioo endLo endHi} := by
    intro x hx
    have hBound' := hBound BT Q hBT hmBT hcBT x hx (Tnn - 1)
    rw [hTsum] at hBound'
    have hExp' : Real.exp (-((Real.pi ^ 2 / 2) / (u - l) ^ 2 + η) * T) <
        c * Real.exp (-intervalEigenvalue 1 (l + 2 * d) (u - 2 * d) * ((Tnn - 1 : ℝ≥0) : ℝ)) := by
      have hTle : ((Tnn - 1 : ℝ≥0) : ℝ) ≤ T :=
        NNReal.coe_le_coe.mpr tsub_le_self
      have hExpLe := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hTle (neg_nonpos.mpr hEig))
      exact (by simpa only [intervalEigenvalue_one l u] using hExp :
        Real.exp (-((Real.pi ^ 2 / 2) / (u - l) ^ 2 + η) * T) <
          c * Real.exp (-intervalEigenvalue 1 (l + 2 * d) (u - 2 * d) * T)).trans_le
        (mul_le_mul_of_nonneg_left hExpLe hc.le)
    have hMeasure := (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le (measure_ne_top _ _)).2
      (hExp'.trans_le hBound')
    have hOpen := brownian_path_endpoint_lower hY hTnn (x := x) (lt_add_of_pos_right l hd)
      (sub_lt_self u hd) (show endLo < endpointLo by dsimp [endpointLo]; linarith)
      (show endpointHi < endHi by dsimp [endpointHi]; linarith)
    exact hMeasure.trans_le hOpen
  let times : ℕ → ℝ := fun n => (length n : ℝ) / a n ^ 2
  have hWalk := eventually_lt_walk_closed_of_donsker hD haTop (times := times) hlength hTpos
    (isCompact_Icc (a := startLo) (b := startHi)) l u endLo endHi hL
  filter_upwards [hWalk] with n hn y hy
  have hlen : ⌊times n * a n ^ 2⌋₊ = length n := by
    simp [times, div_mul_cancel₀ _ (pow_ne_zero 2 (ha n).ne')]
  let x := y / a n
  have hx : a n * x = y := by
    dsimp [x]
    rw [mul_comm, div_mul_cancel₀ _ (ha n).ne']
  have hxy : x ∈ Icc startLo startHi :=
    ⟨(le_div_iff₀ (ha n)).2 (by simpa [mul_comm] using hy.1),
      (div_le_iff₀ (ha n)).2 (by simpa [mul_comm] using hy.2)⟩
  have h := hn x hxy
  rw [hlen, hx] at h
  exact h.le

end VarianceOne

end Mogulskii.SmallDeviation


