import Mogulskii.ExponentialBounds
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Mogulskii

private noncomputable def exponentialWeight (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(n * r)))

private theorem exponentialWeight_anti (n : ℕ) : Antitone (exponentialWeight n) := by
  intro a b hab
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))))

private theorem exponentialWeight_add (n : ℕ) (r s : ℝ) :
    exponentialWeight n (r + s) = exponentialWeight n r * exponentialWeight n s := by
  unfold exponentialWeight
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

private theorem eventually_exponentialWeight_le {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, exponentialWeight n 1 ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc htop
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log c.toReal)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : -(n : ℝ) ≤ Real.log c.toReal := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log hc'] at he
  unfold exponentialWeight
  rw [mul_one, ← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_le_ofReal he

variable {E Ω : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exponential approximation in the uniform metric transfers the bounds from the approximating
paths when their costs dominate the candidate action and approximate each path at no extra cost. -/
theorem hasExponentialBounds_of_approximation
    {X : ℕ → Ω → E} {Y : ℕ → ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) (hY : ∀ m n, Measurable (Y m n))
    {I : E → ℝ≥0∞} {J : ℕ → E → ℝ≥0∞} {π : ℕ → E → E}
    (hI : GoodRate I) (hYbounds : ∀ m > 0, HasExponentialBounds (fun n => μ.map (Y m n)) (J m))
    (hdom : ∀ m > 0, ∀ x, I x ≤ J m x)
    (hπ : ∀ x, Tendsto (fun m => π m x) atTop (𝓝 x))
    (hcost : ∀ m > 0, ∀ x, J m (π m x) ≤ I x)
    (herr : ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, ∀ᶠ m : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop,
        μ {ω | δ < dist (X n ω) (Y m n ω)} ≤ ENNReal.ofReal (Real.exp (-(n * r)))) :
    HasExponentialBounds (fun n => μ.map (X n)) I := by
  refine ⟨hI, ?_, ?_⟩
  · intro F hF r hr
    change ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, (μ.map (X n)) F ≤ C * exponentialWeight n r
    by_cases hr₀ : r < 0
    · refine ⟨1, by simp, Eventually.of_forall fun n => ?_⟩
      haveI : IsProbabilityMeasure (μ.map (X n)) := Measure.isProbabilityMeasure_map (hX n).aemeasurable
      calc
        (μ.map (X n)) F ≤ 1 := prob_le_one
        _ = exponentialWeight n 0 := by simp [exponentialWeight]
        _ ≤ 1 * exponentialWeight n r := by
          simpa using exponentialWeight_anti n hr₀.le
    obtain ⟨s, hrs, hs⟩ := EReal.exists_between_coe_real hr
    have hrs' : r < s := EReal.coe_lt_coe_iff.mp hrs
    have hs₀ : 0 ≤ s := (le_of_not_gt hr₀).trans hrs'.le
    have hcoe : (ENNReal.ofReal s : EReal) = (s : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact congrArg (fun t : ℝ => (t : EReal)) (max_eq_left hs₀)
    let K : Set E := {x | I x ≤ ENNReal.ofReal s}
    have hK : IsCompact K := hI.isCompact_sublevel _ ENNReal.ofReal_ne_top
    have hKF : Disjoint K F := by
      rw [Set.disjoint_left]
      intro x hxK hxF
      have hFx : (⨅ y ∈ F, I y) ≤ I x := iInf₂_le x hxF
      have hx : (s : EReal) < (I x : EReal) :=
        hs.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hFx)
      exact (not_le_of_gt hx) (hcoe ▸ EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxK)
    obtain ⟨δ, hδ, hsep⟩ := hKF.exists_cthickenings hK hF
    obtain ⟨m, hmpos, hm⟩ := ((eventually_gt_atTop (0 : ℕ)).and (herr δ hδ r)).exists
    have hrJ : (r : EReal) < (⨅ x ∈ cthickening δ F, J m x : ℝ≥0∞) := by
      apply hrs.trans_le
      rw [← hcoe, EReal.coe_ennreal_le_coe_ennreal_iff]
      refine le_iInf₂ fun x hx => ?_
      have hxK : x ∉ K := fun hxK =>
        Set.disjoint_left.mp hsep (self_subset_cthickening K hxK) hx
      exact (le_of_lt (lt_of_not_ge hxK)).trans (hdom m hmpos x)
    obtain ⟨C, hC, hup⟩ := (hYbounds m hmpos).upper isClosed_cthickening hrJ
    refine ⟨C + 1, by simp [hC], ?_⟩
    filter_upwards [hm, hup] with n hn hn'
    rw [Measure.map_apply (hX n) hF.measurableSet]
    rw [Measure.map_apply (hY m n) isClosed_cthickening.measurableSet] at hn'
    have hsubset : X n ⁻¹' F ⊆
        Y m n ⁻¹' cthickening δ F ∪ {ω | δ < dist (X n ω) (Y m n ω)} := by
      intro ω hω
      by_cases hdist : δ < dist (X n ω) (Y m n ω)
      · exact Or.inr hdist
      · exact Or.inl (mem_cthickening_of_dist_le _ _ _ _ hω
          (by simpa [dist_comm] using le_of_not_gt hdist))
    calc
      μ (X n ⁻¹' F) ≤ μ (Y m n ⁻¹' cthickening δ F) +
          μ {ω | δ < dist (X n ω) (Y m n ω)} :=
        (measure_mono hsubset).trans (measure_union_le _ _)
      _ ≤ C * exponentialWeight n r + exponentialWeight n r := add_le_add hn' hn
      _ = _ := by rw [add_mul, one_mul]
  · intro x U hU r hr
    change ∃ C : ℝ≥0∞, C ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, C * exponentialWeight n r ≤ (μ.map (X n)) U
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    let δ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hπevent : ∀ᶠ m : ℕ in atTop, π m x ∈ ball x δ :=
      (hπ x).eventually (ball_mem_nhds _ hδ)
    obtain ⟨m, hmpos, hmπ, hm⟩ :=
      ((eventually_gt_atTop (0 : ℕ)).and (hπevent.and (herr δ hδ (r + 1)))).exists
    have hcost' : (J m (π m x) : EReal) < r :=
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hcost m hmpos x)).trans_lt hr
    obtain ⟨C, hC, hlo⟩ := (hYbounds m hmpos).lower (isOpen_ball.mem_nhds hmπ) hcost'
    let c : ℝ≥0∞ := min C 1 * ENNReal.ofReal (1 / 2)
    have hc : c ≠ 0 := by
      dsimp [c]
      simp [hC]
    have hc₂ : c + c ≤ C := by
      dsimp [c]
      rw [← mul_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.ofReal_one, mul_one]
      exact min_le_left _ _
    refine ⟨c, hc, ?_⟩
    filter_upwards [hlo, hm, eventually_exponentialWeight_le hc] with n hnlo hnerr hnsmall
    rw [Measure.map_apply (hY m n) isOpen_ball.measurableSet] at hnlo
    have hXball : (μ.map (X n)) (ball x ε) = μ (X n ⁻¹' ball x ε) :=
      Measure.map_apply (hX n) isOpen_ball.measurableSet
    have hsubset : Y m n ⁻¹' ball x δ ⊆
        X n ⁻¹' ball x ε ∪ {ω | δ < dist (X n ω) (Y m n ω)} := by
      intro ω hω
      by_cases hdist : δ < dist (X n ω) (Y m n ω)
      · exact Or.inr hdist
      · apply Or.inl
        change dist (X n ω) x < ε
        have hy : dist (Y m n ω) x < δ := hω
        have hxx := dist_triangle (X n ω) (Y m n ω) x
        dsimp [δ] at hdist hy
        linarith [le_of_not_gt hdist]
    have hpre : μ (Y m n ⁻¹' ball x δ) ≤
        μ (X n ⁻¹' ball x ε) + μ {ω | δ < dist (X n ω) (Y m n ω)} :=
      (measure_mono hsubset).trans (measure_union_le _ _)
    have herror : μ {ω | δ < dist (X n ω) (Y m n ω)} ≤ c * exponentialWeight n r := by
      calc
        _ ≤ exponentialWeight n (r + 1) := hnerr
        _ = exponentialWeight n r * exponentialWeight n 1 := exponentialWeight_add n r 1
        _ ≤ exponentialWeight n r * c := mul_le_mul_right hnsmall _
        _ = _ := mul_comm _ _
    have hsum : c * exponentialWeight n r + c * exponentialWeight n r ≤
        μ (X n ⁻¹' ball x ε) + c * exponentialWeight n r := by
      rw [← add_mul]
      exact (mul_le_mul_left hc₂ _).trans (hnlo.trans (hpre.trans (add_le_add_right herror _)))
    have hfin : c * exponentialWeight n r ≠ ⊤ := by
      dsimp [c, exponentialWeight]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
          ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    exact ((ENNReal.add_le_add_iff_right hfin).mp hsum).trans
      (hXball.symm.le.trans (measure_mono hεU))

end Mogulskii



