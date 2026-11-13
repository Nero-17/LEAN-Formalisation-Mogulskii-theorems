import Mogulskii.SurvivalGrid
import Mathlib.Probability.Process.HittingTime

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace Mogulskii

variable {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ}

noncomputable def brownianSine (frequency shift : ℝ) (t : ℝ≥0) (value : ℝ) : ℝ :=
  Real.exp (frequency ^ 2 / 2 * (t : ℝ)) * Real.sin (frequency * (shift + value))

noncomputable def gridSine (B : ℝ≥0 → Ω → ℝ)
    (left right x : ℝ) (T : ℝ≥0) (n : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ brownianSine (Real.pi / (right - left)) (x - left)
    (uniformGrid T n k) (B (uniformGrid T n k) ω)

noncomputable def gridExit (B : ℝ≥0 → Ω → ℝ)
    (left right x : ℝ) (T : ℝ≥0) (n : ℕ) : Ω → ℕ :=
  hittingBtwn (fun k ω ↦ x + B (uniformGrid T n k) ω) (Icc left right)ᶜ 0 (n + 1)

theorem brownianSine_eq (left right x z : ℝ) (t : ℝ≥0) :
    brownianSine (Real.pi / (right - left)) (x - left) t z =
      Real.exp (intervalEigenvalue 1 left right * (t : ℝ)) *
        intervalSine left right (x + z) := by
  unfold brownianSine intervalEigenvalue intervalSine
  have hfrequency : (Real.pi / (right - left)) ^ 2 / 2 =
      Real.pi ^ 2 * 1 / (2 * (right - left) ^ 2) := by
    simp only [div_pow, div_div, mul_one, mul_comm (2 : ℝ)]
  have hposition : Real.pi / (right - left) * (x - left + z) =
      Real.pi * (x + z - left) / (right - left) := by ring
  rw [hfrequency, hposition]

theorem norm_brownianSine_le (left right x z : ℝ) {t T : ℝ≥0} (ht : t ≤ T) :
    ‖brownianSine (Real.pi / (right - left)) (x - left) t z‖ ≤
      Real.exp (intervalEigenvalue 1 left right * (T : ℝ)) := by
  rw [brownianSine_eq, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs]
  calc
    _ ≤ Real.exp (intervalEigenvalue 1 left right * (t : ℝ)) :=
      mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by
      unfold intervalEigenvalue
      positivity))

theorem gridSine_tendsto (left right x : ℝ) (hlr : left < right) (T : ℝ≥0)
    {ω : Ω} (hpath : Continuous (B · ω)) (hzero : B 0 ω = 0) (hx : x ∈ Icc left right) :
    Tendsto (fun n ↦ gridSine B left right x T n (gridExit B left right x T n ω) ω) atTop
      (𝓝 ((intervalSurvival (fun t ω ↦ x + B t ω) left right T).indicator
        (fun ω ↦ brownianSine (Real.pi / (right - left)) (x - left) T (B T ω)) ω)) := by
  let path := fun t ↦ x + B t ω
  have hc : Continuous path := continuous_const.add hpath
  have hcontinuous : Continuous (fun t : ℝ≥0 ↦
      Real.exp (intervalEigenvalue 1 left right * (t : ℝ)) * intervalSine left right (path t)) := by
    unfold intervalSine
    fun_prop
  have hstop (n : ℕ) : gridExit B left right x T n ω ≤ n + 1 := hittingBtwn_le ω
  have ht_stop (n : ℕ) : uniformGrid T n (gridExit B left right x T n ω) ≤ T :=
    (monotone_uniformGrid T n (hstop n)).trans_eq (uniformGrid_last T n)
  by_cases hstay : ω ∈ intervalSurvival (fun t ω ↦ x + B t ω) left right T
  · rw [indicator_of_mem hstay]
    have heq (n : ℕ) : gridExit B left right x T n ω = n + 1 := by
      refine (hittingBtwn_eq_end_iff).2 ?_
      rintro ⟨k, hk, hkout⟩
      exact (hkout (hstay _ ((monotone_uniformGrid T n hk.2).trans_eq
        (uniformGrid_last T n)))).elim
    simpa [gridSine, heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ brownianSine (Real.pi / (right - left))
        (x - left) T (B T ω)) atTop _)
  · rw [indicator_of_notMem hstay]
    have hevent : ∃ t ≤ T, path t ∉ Icc left right := by
      have hnot : ¬ ∀ t : ℝ≥0, t ≤ T → path t ∈ Icc left right := hstay
      obtain ⟨t, ht, houtside⟩ := not_forall₂.mp hnot
      exact ⟨t, ht, houtside⟩
    have hexit := eventually_exists_uniformGrid_exit hc hevent
    have hUC := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).uniformContinuousOn_of_continuous
      hcontinuous.continuousOn
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨δ, hδ, hUCδ⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
    filter_upwards [hexit, (tendsto_uniformGrid_mesh T).eventually (eventually_lt_nhds hδ)] with n hn hmesh
    let k := gridExit B left right x T n ω
    have hkout : path (uniformGrid T n k) ∉ Icc left right := by
      obtain ⟨j, hj, hjout⟩ := hn
      exact hittingBtwn_mem_set
        (u := fun k ω ↦ x + B (uniformGrid T n k) ω) (s := (Icc left right)ᶜ)
        (n := 0) (m := n + 1) (ω := ω) ⟨j, ⟨Nat.zero_le _, hj⟩, hjout⟩
    have hkpos : 0 < k := by
      by_contra! hk
      have h : k = 0 := le_antisymm hk (Nat.zero_le _)
      apply hkout
      simpa [h, path, hzero] using hx
    have hkin : path (uniformGrid T n (k - 1)) ∈ Icc left right := by
      have hlt : k - 1 < k := Nat.sub_lt hkpos Nat.one_pos
      exact not_not.mp (notMem_of_lt_hittingBtwn hlt (Nat.zero_le _))
    have hmono := monotone_uniformGrid T n (Nat.sub_le k 1)
    obtain ⟨u, hu, huboundary⟩ := exists_between_boundary hc hmono hkin hkout
    have hdist : dist (uniformGrid T n k) u ≤ (T : ℝ) / ((n : ℝ) + 1) := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤
        (uniformGrid T n k : ℝ) from hu.2))]
      have hstep : uniformGrid T n k =
          uniformGrid T n (k - 1) + T / (n + 1 : ℕ) := by
        rw [← uniformGrid_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hkpos.ne')]
      have hre (v w : ℝ≥0) (h : v ≤ w) : (v : ℝ) ≤ (w : ℝ) := h
      simp only [hstep, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast]
      push_cast
      linarith [hre _ _ hu.1]
    have hval : Real.exp (intervalEigenvalue 1 left right * (u : ℝ)) *
        intervalSine left right (path u) = 0 := by
      rcases huboundary with hl | hr
      · simp [hl]
      · simp [hr, intervalSine_right hlr.ne]
    have hcompare := hUCδ (uniformGrid T n k) ⟨zero_le, ht_stop n⟩
      u ⟨zero_le, hu.2.trans (ht_stop n)⟩ (hdist.trans_lt hmesh)
    rw [hval] at hcompare
    simpa only [gridSine, brownianSine_eq, k, path] using hcompare

end Mogulskii
