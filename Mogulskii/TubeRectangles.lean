import Mogulskii.PartitionRates
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped BigOperators

namespace Mogulskii.SmallDeviation

/-- Data for approximating a moving tube by constant windows on an equal mesh.
The bounds hold within twice the mesh size of the left endpoint, allowing rounding of
time endpoints to discrete times. -/
structure TubeRectangles (f g : ℝ → ℝ) (ε : ℝ) where
  count : ℕ
  count_pos : 0 < count
  innerLower : ℕ → ℝ
  innerUpper : ℕ → ℝ
  outerLower : ℕ → ℝ
  outerUpper : ℕ → ℝ
  endpointLower : ℕ → ℝ
  endpointUpper : ℕ → ℝ
  endpoint_nonempty : ∀ j ≤ count, endpointLower j < endpointUpper j
  start_mem : (0 : ℝ) ∈ Icc (endpointLower 0) (endpointUpper 0)
  inner_pos : ∀ j < count, innerLower j < innerUpper j
  outer_pos : ∀ j < count, outerLower j < outerUpper j
  start_subset : ∀ j < count, Icc (endpointLower j) (endpointUpper j) ⊆
    Ioo (innerLower j) (innerUpper j)
  end_subset : ∀ j < count, Icc (endpointLower (j + 1)) (endpointUpper (j + 1)) ⊆
    Ioo (innerLower j) (innerUpper j)
  bounds : ∀ j < count, ∀ t ∈ Icc (0 : ℝ) 1, |t - (j : ℝ) / count| ≤ 2 / count →
    outerLower j ≤ f t ∧ f t ≤ innerLower j ∧ innerUpper j ≤ g t ∧ g t ≤ outerUpper j
  inner_rate : |(∑ j ∈ Finset.range count,
    ((1 : ℝ) / count) * (1 / (innerUpper j - innerLower j) ^ 2)) -
    (∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2)| ≤ ε
  outer_rate : |(∑ j ∈ Finset.range count,
    ((1 : ℝ) / count) * (1 / (outerUpper j - outerLower j) ^ 2)) -
    (∫ t in (0 : ℝ)..1, 1 / (g t - f t) ^ 2)| ≤ ε

private theorem equalMesh_mem_Icc {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    (j : ℝ) / m ∈ Icc (0 : ℝ) 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact ⟨by positivity, (div_le_one hmR).mpr (by exact_mod_cast hj)⟩

private theorem equalMesh_step {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) / m - (j : ℝ) / m = 1 / (m : ℝ) := by
  rw [← sub_div]
  push_cast
  ring

private theorem rate_of_cellwise_approx {m : ℕ} (hm : 0 < m)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (0 : ℝ) 1)) {c : ℕ → ℝ} {ε : ℝ}
    (hc : ∀ j < m, ∀ t ∈ Icc (0 : ℝ) 1, |t - (j : ℝ) / m| ≤ 2 / m → |c j - F t| ≤ ε) :
    |(∑ j ∈ Finset.range m, (1 / (m : ℝ)) * c j) - (∫ t in (0 : ℝ)..1, F t)| ≤ ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmono : Monotone (fun j : ℕ => (j : ℝ) / m) :=
    fun j k hjk => div_le_div_of_nonneg_right (by exact_mod_cast hjk) hmR.le
  have hsubset (j : ℕ) (hj : j < m) :
      Icc ((j : ℝ) / m) (((j + 1 : ℕ) : ℝ) / m) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨(equalMesh_mem_Icc hm hj.le).1.trans ht.1,
      ht.2.trans (equalMesh_mem_Icc hm (Nat.succ_le_of_lt hj)).2⟩
  have hi : ∀ j < m, IntervalIntegrable F volume ((j : ℝ) / m) (((j + 1 : ℕ) : ℝ) / m) := by
    intro j hj
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hmono (Nat.le_succ j))]
    exact hF.mono (hsubset j hj)
  have h := abs_weighted_sum_sub_integral_le (t := fun j : ℕ => (j : ℝ) / m)
    (fun j _ => hmono (Nat.le_succ j)) hi (c := c) (ε := ε) (fun j hj t ht => by
      have hb := ht.2
      have ha := ht.1
      apply hc j hj t (hsubset j hj ht)
      rw [abs_of_nonneg (sub_nonneg.mpr ha)]
      have h := equalMesh_step hm j
      have hpositive : (0 : ℝ) ≤ 1 / m := by positivity
      have hdouble : (2 : ℝ) / m = 1 / m + 1 / m := by rw [← add_div]; norm_num
      linarith)
  simpa only [equalMesh_step hm, Nat.cast_zero, zero_div, div_self hmR.ne',
    sub_zero, one_mul] using h

/-- Given any positive error, continuous separated boundaries admit inner and outer
rectangular approximations with shared interior endpoint intervals and approximating rates. -/
theorem exists_tubeRectangles {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f t < g t) (hf0 : f 0 < 0) (hg0 : 0 < g 0)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (TubeRectangles f g ε) := by
  let width := fun t => g t - f t
  have hwidth : ContinuousOn width (Icc (0 : ℝ) 1) := hg.sub hf
  obtain ⟨s, hs, hsmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hwidth
  obtain ⟨u, hu, humax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) hwidth
  have hspos : 0 < width s := sub_pos.mpr (hfg s hs)
  have hlower : ∀ t ∈ Icc (0 : ℝ) 1, width s ≤ width t := fun t ht => hsmin ht
  have hupper : ∀ t ∈ Icc (0 : ℝ) 1, width t ≤ width u := fun t ht => humax ht
  have hinv : ContinuousOn (fun r : ℝ => 1 / r ^ 2) (Icc (width s / 2) (width u + width s)) := by
    refine continuousOn_const.div (continuous_id.pow 2).continuousOn fun r hr => ?_
    exact pow_ne_zero 2 ((half_pos hspos).trans_le hr.1).ne'
  obtain ⟨η, hη, hηclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hinv) ε hε
  let slack := min (min (width s / 8) (η / 8)) (min (-f 0 / 4) (g 0 / 4))
  have hslack : 0 < slack := by
    dsimp [slack]
    exact lt_min (lt_min (by positivity) (by positivity))
      (lt_min (div_pos (neg_pos.mpr hf0) (by norm_num)) (by positivity))
  have hslackWidth : slack ≤ width s / 8 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hslackEta : slack ≤ η / 8 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hslackLeft : slack ≤ -f 0 / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hslackRight : slack ≤ g 0 / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δf, hδf, hclosef⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) slack hslack
  obtain ⟨δg, hδg, hcloseg⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) slack hslack
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / min δf δg)
  have hδ : 0 < min δf δg := lt_min hδf hδg
  have hmR : (0 : ℝ) < m := (by positivity : 0 < 2 / min δf δg).trans hm
  have hmpos : 0 < m := by exact_mod_cast hmR
  have hmesh : (2 : ℝ) / m < min δf δg := by
    apply (div_lt_iff₀ hmR).mpr
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hm
  let t := fun j : ℕ => (j : ℝ) / m
  let center := fun j : ℕ => if j = 0 then 0 else (f (t j) + g (t j)) / 2
  have hclose (j : ℕ) (hj : j < m) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hd : |r - t j| ≤ 2 / m) : |f r - f (t j)| < slack ∧ |g r - g (t j)| < slack := by
    have hjt := equalMesh_mem_Icc hmpos hj.le
    have hd' : dist r (t j) < min δf δg := by
      simpa only [Real.dist_eq] using hd.trans_lt hmesh
    simpa only [Real.dist_eq] using
      And.intro (hclosef r hr (t j) hjt (hd'.trans_le (min_le_left _ _)))
        (hcloseg r hr (t j) hjt (hd'.trans_le (min_le_right _ _)))
  have hinside (j : ℕ) (hj : j < m) (k : ℕ) (hk : k = j ∨ k = j + 1) :
      Icc (center k - slack) (center k + slack) ⊆ Ioo (f (t j) + slack) (g (t j) - slack) := by
    intro y hy
    have hylo := hy.1
    have hyhi := hy.2
    by_cases hk0 : k = 0
    · have hj0 : j = 0 := by omega
      have hcenter : center k = 0 := by simp [center, hk0]
      simp [hcenter] at hylo hyhi
      simp only [hj0, t, Nat.cast_zero, zero_div, mem_Ioo]
      constructor <;> linarith
    · have hcenter : center k = (f (t k) + g (t k)) / 2 := by simp [center, hk0]
      have hkR : k ≤ m := by omega
      have htk := equalMesh_mem_Icc hmpos hkR
      have htkdist : |t k - t j| ≤ 2 / m := by
        rcases hk with rfl | rfl
        · simp only [sub_self, abs_zero]; positivity
        · dsimp [t]
          rw [equalMesh_step hmpos, abs_of_nonneg (by positivity)]
          exact div_le_div_of_nonneg_right (by norm_num) hmR.le
      obtain ⟨hcf, hcg⟩ := hclose j hj (t k) htk htkdist
      have hwd := hlower (t k) htk
      rw [hcenter] at hylo hyhi
      change width s ≤ g (t k) - f (t k) at hwd
      change f (t j) + slack < y ∧ y < g (t j) - slack
      constructor
      · have := neg_lt_of_abs_lt hcf
        linarith
      · have := lt_of_abs_lt hcg
        linarith
  have hF : ContinuousOn (fun r => 1 / (g r - f r) ^ 2) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (hwidth.pow 2) fun r hr => pow_ne_zero 2 (sub_pos.mpr (hfg r hr)).ne'
  have hlocal (j : ℕ) (hj : j < m) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hd : |r - t j| ≤ 2 / m) (offset : ℝ) (hoffset : |offset| ≤ 2 * slack) :
      |1 / (width (t j) + offset) ^ 2 - 1 / width r ^ 2| ≤ ε := by
    obtain ⟨hcf, hcg⟩ := hclose j hj r hr hd
    have hwind : |width (t j) - width r| < 2 * slack := by
      have h : width (t j) - width r = (f r - f (t j)) - (g r - g (t j)) := by
        dsimp [width]; ring
      rw [h]
      exact (abs_sub _ _).trans_lt (by linarith)
    have hjt := equalMesh_mem_Icc hmpos hj.le
    have hminj := hlower (t j) hjt
    have hmaxj := hupper (t j) hjt
    have hminr := hlower r hr
    have hmaxr := hupper r hr
    have hlowOffset := neg_le_of_abs_le hoffset
    have hhighOffset := le_of_abs_le hoffset
    have hplus : width (t j) + offset ∈ Icc (width s / 2) (width u + width s) :=
      ⟨by linarith, by linarith⟩
    have hrwidth : width r ∈ Icc (width s / 2) (width u + width s) :=
      ⟨by linarith, by linarith⟩
    have hd' : dist (width (t j) + offset) (width r) < η := by
      rw [Real.dist_eq, show width (t j) + offset - width r =
        (width (t j) - width r) + offset by ring]
      exact (abs_add_le _ _).trans_lt (by linarith)
    simpa only [Real.dist_eq] using (hηclose _ hplus _ hrwidth hd').le
  refine ⟨{
    count := m
    count_pos := hmpos
    innerLower := fun j => f (t j) + slack
    innerUpper := fun j => g (t j) - slack
    outerLower := fun j => f (t j) - slack
    outerUpper := fun j => g (t j) + slack
    endpointLower := fun j => center j - slack
    endpointUpper := fun j => center j + slack
    endpoint_nonempty := fun j _ => by linarith
    start_mem := by simp [center, hslack.le]
    inner_pos := ?_
    outer_pos := ?_
    start_subset := fun j hj => hinside j hj j (Or.inl rfl)
    end_subset := fun j hj => hinside j hj (j + 1) (Or.inr rfl)
    bounds := ?_
    inner_rate := ?_
    outer_rate := ?_ }⟩
  · intro j hj
    have h := hlower (t j) (equalMesh_mem_Icc hmpos hj.le)
    change width s ≤ g (t j) - f (t j) at h
    linarith
  · intro j hj
    have h := hfg (t j) (equalMesh_mem_Icc hmpos hj.le)
    linarith
  · intro j hj r hr hd
    obtain ⟨hcf, hcg⟩ := hclose j hj r hr hd
    exact ⟨by linarith [neg_lt_of_abs_lt hcf], by linarith [lt_of_abs_lt hcf],
      by linarith [neg_lt_of_abs_lt hcg], by linarith [lt_of_abs_lt hcg]⟩
  · apply rate_of_cellwise_approx hmpos hF
    intro j hj r hr hd
    rw [show g (t j) - slack - (f (t j) + slack) = width (t j) + -(2 * slack) by
      dsimp [width]; ring]
    exact hlocal j hj r hr hd _ (by simp [abs_of_nonneg hslack.le])
  · apply rate_of_cellwise_approx hmpos hF
    intro j hj r hr hd
    rw [show g (t j) + slack - (f (t j) - slack) = width (t j) + 2 * slack by
      dsimp [width]; ring]
    exact hlocal j hj r hr hd _ (by simp [abs_of_nonneg hslack.le])

noncomputable def tubeRectangles {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hfg : ∀ t ∈ Icc (0 : ℝ) 1, f t < g t) (hf0 : f 0 < 0) (hg0 : 0 < g 0)
    {ε : ℝ} (hε : 0 < ε) : TubeRectangles f g ε :=
  Classical.choice (exists_tubeRectangles hf hg hfg hf0 hg0 hε)

end Mogulskii.SmallDeviation



