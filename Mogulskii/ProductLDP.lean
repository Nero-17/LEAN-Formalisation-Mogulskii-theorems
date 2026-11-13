/-
Portions of the proof adapt Degenne2023Existence at commit
208fe8bbf8820ec9093a2d7994ce94474cff3afc (Rémy Degenne, Apache-2.0).
-/
import Mogulskii.ExponentialBounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace Mogulskii

lemma GoodRate.weightedProduct {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ a, TopologicalSpace (X a)] {I : ∀ a, X a → ℝ≥0∞} (hI : ∀ a, GoodRate (I a))
    {w : ι → ℝ} (hw : ∀ a, 0 < w a) :
    GoodRate fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) := by
  have h_lsc : LowerSemicontinuous fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) :=
    lowerSemicontinuous_sum fun a _ ↦
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
        ((hI a).lowerSemicontinuous.comp (continuous_apply a)) fun _ _ h ↦ by dsimp only; gcongr
  refine ⟨h_lsc, fun c hc ↦ ?_⟩
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun a ↦ (hI a).isCompact_sublevel (c / ENNReal.ofReal (w a))
      (ENNReal.div_ne_top hc (by simpa using hw a)))
    (h_lsc.isClosed_preimage _) fun x hx a _ ↦ ?_
  have h_le : ENNReal.ofReal (w a) * I a (x a) ≤ c :=
    (Finset.single_le_sum (f := fun a ↦ ENNReal.ofReal (w a) * I a (x a))
      (fun _ _ ↦ zero_le) (Finset.mem_univ a)).trans hx
  change I a (x a) ≤ c / ENNReal.ofReal (w a)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hw a)) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact h_le



section
variable {α E : Type*} [Fintype α] [SeminormedAddCommGroup E]
  {I : α → E → ℝ≥0∞} {w : α → ℝ}

lemma exists_rate_lt_iInf_closedBall (hI : ∀ a, LowerSemicontinuous (I a)) (hw : ∀ a, 0 < w a)
    {x : α → E} {r : ℝ}
    (hr : (r : EReal) < ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal)) :
    ∃ s ε : α → ℝ, (∀ a, 0 ≤ s a) ∧ (∀ a, 0 < ε a) ∧ r < ∑ a, w a * s a ∧
      ∀ a, s a = 0 ∨ (s a : EReal) < ⨅ y ∈ Metric.closedBall (x a) (ε a), I a y := by
  have h_lsc (a : α) (u : ℝ) (hu : ENNReal.ofReal u < I a (x a)) :
      ∃ ε > 0, ENNReal.ofReal u ≤ ⨅ y ∈ Metric.closedBall (x a) ε, I a y := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hI a (x a) _ hu)
    refine ⟨ε / 2, by positivity, le_iInf₂ fun y hy ↦ (hball ?_).le⟩
    rw [Metric.mem_closedBall] at hy
    linarith
  suffices h : ∃ s : α → ℝ, (∀ a, 0 ≤ s a) ∧ r < ∑ a, w a * s a ∧
      ∀ a, s a = 0 ∨ ∃ u : ℝ, s a < u ∧ ENNReal.ofReal u < I a (x a) by
    obtain ⟨s, hs0, hsr, hs⟩ := h
    have h_each (a : α) : ∃ ε > 0,
        s a = 0 ∨ (s a : EReal) < ⨅ y ∈ Metric.closedBall (x a) ε, I a y := by
      rcases hs a with h0 | ⟨u, hsu, hu⟩
      · exact ⟨1, one_pos, Or.inl h0⟩
      obtain ⟨ε, hε, hε'⟩ := h_lsc a u hu
      refine ⟨ε, hε, Or.inr (lt_of_lt_of_le ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2 hε'))⟩
      rw [EReal.coe_ennreal_ofReal]
      exact EReal.coe_lt_coe_iff.2 (lt_max_of_lt_left hsu)
    choose ε hε hε' using h_each
    exact ⟨s, ε, hs0, hε, hsr, hε'⟩
  classical
  by_cases htop : ∃ a₀, I a₀ (x a₀) = ⊤
  · -- One of the rates is infinite: put all the weight on it.
    obtain ⟨a₀, ha₀⟩ := htop
    refine ⟨fun a ↦ if a = a₀ then (|r| + 1) / w a₀ else 0, fun a ↦ ?_, ?_, fun a ↦ ?_⟩
    · dsimp only
      split_ifs
      · exact div_nonneg (by positivity) (hw a₀).le
      · exact le_rfl
    · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [mul_div_cancel₀ _ (hw a₀).ne']
      linarith [le_abs_self r]
    · by_cases ha : a = a₀
      · subst ha
        exact Or.inr ⟨(|r| + 1) / w a + 1, by simp, by rw [ha₀]; exact ENNReal.ofReal_lt_top⟩
      · exact Or.inl (by simp [ha])
  -- All the rates are finite: lower each of them by `2 η`.
  simp only [not_exists] at htop
  set t : α → ℝ := fun a ↦ (I a (x a)).toReal
  have ht0 (a : α) : 0 ≤ t a := ENNReal.toReal_nonneg
  have hJ : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ENNReal.ofReal (∑ a, w a * t a) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mul_nonneg (hw a).le (ht0 a))]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [ENNReal.ofReal_mul (hw a).le, ENNReal.ofReal_toReal (htop a)]
  have hr' : r < ∑ a, w a * t a := by
    rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (Finset.sum_nonneg fun a _ ↦
      mul_nonneg (hw a).le (ht0 a))] at hr
    exact EReal.coe_lt_coe_iff.1 hr
  set W := ∑ a, w a
  have hW : 0 ≤ W := Finset.sum_nonneg fun a _ ↦ (hw a).le
  set η := (∑ a, w a * t a - r) / (2 * (W + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  refine ⟨fun a ↦ max 0 (t a - 2 * η), fun a ↦ le_max_left _ _, ?_, fun a ↦ ?_⟩
  · calc r < ∑ a, w a * t a - 2 * η * W := by
          have : 2 * η * W = (∑ a, w a * t a - r) * (W / (W + 1)) := by
            simp only [η]
            field_simp
          rw [this]
          have h1 : W / (W + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
          nlinarith
    _ = ∑ a, w a * (t a - 2 * η) := by
          simp only [W, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ ∑ a, w a * max 0 (t a - 2 * η) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (hw a).le
  · rcases le_or_gt (t a - 2 * η) 0 with h | h
    · exact Or.inl (max_eq_left h)
    refine Or.inr ⟨t a - η, (max_eq_right h.le).trans_lt (by linarith), ?_⟩
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (htop a)]
    linarith



omit [Fintype α] in
/-- If a property holds eventually along `atTop` for each coordinate, then it holds for all the
`n : α → ℕ` with `T w a - k ≤ n a`, for `T` large. -/
lemma eventually_forall_of_eventually [Finite α] {Q : α → ℕ → Prop} (h : ∀ a, ∀ᶠ m in atTop, Q a m)
    (hw : ∀ a, 0 < w a) (k : ℝ) :
    ∀ᶠ T : ℕ in atTop, ∀ n : α → ℕ, (∀ a, T * w a - k ≤ n a) → ∀ a, Q a (n a) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_all.2 h)
  filter_upwards [eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const
    (hw a)).eventually_ge_atTop ((N : ℝ) + k)] with T hT n hn a
  exact hN (n a) (by exact_mod_cast (show (N : ℝ) ≤ n a by linarith [hT a, hn a])) a

/-- If `n a ≥ T w a - k` and `r ≤ ∑ a, w a s a` for rates `s a ≥ 0`, then
`∏ a, exp (-(n a s a)) ≤ exp (k ∑ a, s a) exp (-(T r))`. -/
lemma prod_ofReal_exp_le {s : α → ℝ} (hs : ∀ a, 0 ≤ s a) {T : ℕ} {k r : ℝ}
    (hsr : r ≤ ∑ a, w a * s a) {n : α → ℕ} (hn : ∀ a, T * w a - k ≤ n a) :
    ∏ a, ENNReal.ofReal (Real.exp (-(n a * s a))) ≤
      ENNReal.ofReal (Real.exp (k * ∑ a, s a)) * ENNReal.ofReal (Real.exp (-(T * r))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 : ∑ a, (T * w a - k) * s a ≤ ∑ a, (n a : ℝ) * s a :=
    Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right (hn a) (hs a)
  have h2 : ∑ a, (T * w a - k) * s a = T * ∑ a, w a * s a - k * ∑ a, s a := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have h3 : (T : ℝ) * r ≤ T * ∑ a, w a * s a := mul_le_mul_of_nonneg_left hsr T.cast_nonneg
  rw [Finset.sum_neg_distrib]
  linarith


/-- Products of the lower exponential bounds, under the corresponding upper bound on
the number of samples in each block. -/
lemma prod_ofReal_exp_ge {s : α → ℝ} (hs : ∀ a, 0 ≤ s a) {T : ℕ} {k r : ℝ}
    (hsr : (∑ a, w a * s a) ≤ r) {n : α → ℕ} (hn : ∀ a, (n a : ℝ) ≤ T * w a + k) :
    ENNReal.ofReal (Real.exp (-(k * ∑ a, s a))) * ENNReal.ofReal (Real.exp (-(T * r))) ≤
      ∏ a, ENNReal.ofReal (Real.exp (-(n a * s a))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 : ∑ a, (n a : ℝ) * s a ≤ ∑ a, (T * w a + k) * s a :=
    Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right (hn a) (hs a)
  have h2 : ∑ a, (T * w a + k) * s a = T * ∑ a, w a * s a + k * ∑ a, s a := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have h3 : (T : ℝ) * ∑ a, w a * s a ≤ T * r :=
    mul_le_mul_of_nonneg_left hsr T.cast_nonneg
  rw [Finset.sum_neg_distrib]
  linarith

variable [MeasurableSpace E] [BorelSpace E]
  {P : α → ℕ → Measure E} [hProb : ∀ a n, IsProbabilityMeasure (P a n)]

omit [BorelSpace E] in
/-- Exponential tightness from compactness of the sublevels. -/
lemma HasExponentialBounds.eventually_norm_ge
    {Q : ℕ → Measure E} {J : E → ℝ≥0∞} (h : HasExponentialBounds Q J) (r : ℝ) :
    ∃ M : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, Q n {y | M ≤ ‖y‖} ≤ C * ENNReal.ofReal (Real.exp (-(n * r))) := by
  set c := ENNReal.ofReal (max r 0 + 1)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1
    (h.isGood.isCompact_sublevel c ENNReal.ofReal_ne_top).isBounded
  refine ⟨R + 1, h.upper (isClosed_le continuous_const continuous_norm) ?_⟩
  have hc : (c : EReal) = ((max r 0 + 1 : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by linarith [le_max_right r 0])]
  refine lt_of_lt_of_le (b := (c : EReal)) ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (le_iInf₂ fun x hx ↦ ?_))
  · rw [hc, EReal.coe_lt_coe_iff]
    linarith [le_max_left r 0]
  · by_contra hlt
    have hx' := hR (show x ∈ {x | J x ≤ c} from (not_le.1 hlt).le)
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    change R + 1 ≤ ‖x‖ at hx
    exact (not_le_of_gt (by linarith : R < ‖x‖)) hx'

/-- A finite product of marginal LDPs, with a deterministic number of samples in each
coordinate and a uniform bound on each discrepancy from its positive proportion. -/
theorem hasExponentialBounds_pi [ProperSpace E] (hP : ∀ a, HasExponentialBounds (P a) (I a))
    (hw : ∀ a, 0 < w a) (count : ℕ → α → ℕ) (k : ℝ)
    (hcount : ∀ T a, |(count T a : ℝ) - T * w a| ≤ k) :
    HasExponentialBounds (fun T ↦ Measure.pi fun a ↦ P a (count T a))
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a)) := by
  classical
  refine ⟨GoodRate.weightedProduct (fun a ↦ (hP a).isGood) hw, ?_, ?_⟩
  · intro F hF r hr
    rcases le_or_gt r 0 with hr0 | hr0
    · refine ⟨1, ENNReal.one_ne_top, Eventually.of_forall fun T ↦ ?_⟩
      rw [one_mul]
      refine prob_le_one.trans (ENNReal.one_le_ofReal.2 (Real.one_le_exp ?_))
      nlinarith [(T.cast_nonneg : (0 : ℝ) ≤ T)]
    choose M D hD hM using fun a ↦ (hP a).eventually_norm_ge (r / w a)
    have hrx : ∀ x ∈ F,
        (r : EReal) < ((∑ a, ENNReal.ofReal (w a) * I a (x a) : ℝ≥0∞) : EReal) :=
      fun x hx ↦ hr.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x hx))
    choose! s ε hs0 hε hsr hsε using fun x (hx : x ∈ F) ↦
      exists_rate_lt_iInf_closedBall (fun a ↦ (hP a).isGood.lowerSemicontinuous) hw (hrx x hx)

    have hK : IsCompact (F ∩ Set.univ.pi fun a ↦ Metric.closedBall (0 : E) (M a)) :=
      (isCompact_univ_pi fun a ↦ isCompact_closedBall _ _).inter_left hF
    obtain ⟨cover, hcover, hKcover⟩ := hK.elim_nhds_subcover
      (fun x ↦ Set.univ.pi fun a ↦ Metric.ball (x a) (ε x a)) fun x hx ↦
        set_pi_mem_nhds Set.finite_univ fun a _ ↦ Metric.ball_mem_nhds (x a) (hε x hx.1 a)
    have h_local (a : α) (x : α → E) (hx : x ∈ cover) :
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n in atTop,
          P a n (Metric.closedBall (x a) (ε x a)) ≤
            C * ENNReal.ofReal (Real.exp (-(n * s x a))) := by
      rcases hsε x (hcover x hx).1 a with hz | hp
      · refine ⟨1, ENNReal.one_ne_top, Eventually.of_forall fun n ↦ ?_⟩
        simpa [hz] using (prob_le_one (μ := P a n)
          (s := Metric.closedBall (x a) (ε x a)))
      · exact (hP a).upper Metric.isClosed_closedBall hp
    choose! C hC hloc using fun a x hx ↦ h_local a x hx
    have h_ev (a : α) : ∀ᶠ m in atTop, (∀ x ∈ cover,
        P a m (Metric.closedBall (x a) (ε x a)) ≤
          C a x * ENNReal.ofReal (Real.exp (-(m * s x a)))) ∧
        P a m {y | M a ≤ ‖y‖} ≤ D a * ENNReal.ofReal (Real.exp (-(m * (r / w a)))) :=
      ((eventually_all_finset cover).2 (fun x hx ↦ hloc a x hx)).and (hM a)
    refine ⟨(∑ x ∈ cover, (∏ a, C a x) *
      ENNReal.ofReal (Real.exp (k * ∑ a, s x a))) +
      ∑ a, D a * ENNReal.ofReal (Real.exp (k * (r / w a))), ?_, ?_⟩
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun x hx ↦ ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun a _ ↦ hC a x hx) ENNReal.ofReal_ne_top,
        ENNReal.sum_ne_top.2 fun a _ ↦ ENNReal.mul_ne_top (hD a) ENNReal.ofReal_ne_top⟩
    filter_upwards [eventually_forall_of_eventually h_ev hw k] with T hT
    let Q : Measure (α → E) := Measure.pi fun a ↦ P a (count T a)
    have hlo (a : α) : (T : ℝ) * w a - k ≤ count T a := by
      linarith [(abs_le.1 (hcount T a)).1]
    specialize hT (count T) hlo
    have h_sub : F ⊆ (⋃ x ∈ cover, Set.univ.pi fun a ↦ Metric.closedBall (x a) (ε x a)) ∪
        ⋃ a, {y | M a ≤ ‖y a‖} := by
      intro y hy
      by_cases h : ∃ a, M a ≤ ‖y a‖
      · obtain ⟨a, ha⟩ := h
        exact Or.inr (Set.mem_iUnion.2 ⟨a, ha⟩)
      simp only [not_exists, not_le] at h
      have hyK : y ∈ F ∩ Set.univ.pi (fun a ↦ Metric.closedBall (0 : E) (M a)) :=
        ⟨hy, fun a _ ↦ by simpa [Metric.mem_closedBall, dist_zero_right] using (h a).le⟩
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hKcover hyK)
      exact Or.inl (Set.mem_iUnion₂.2 ⟨x, hx, fun a ha ↦
        Metric.ball_subset_closedBall (hyx a ha)⟩)
    change Q F ≤ _
    refine (measure_mono h_sub).trans ((measure_union_le _ _).trans ?_)
    rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    gcongr ?_ + ?_
    · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x hx ↦ ?_)
      dsimp only [Q]
      rw [Measure.pi_pi]
      refine (Finset.prod_le_prod (fun _ _ ↦ zero_le) (fun a _ ↦ (hT a).1 x hx)).trans ?_
      rw [Finset.prod_mul_distrib, mul_assoc]
      exact mul_le_mul_right (prod_ofReal_exp_le
        (hs0 x (hcover x hx).1) (hsr x (hcover x hx).1).le hlo) _
    · refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
      have hm : MeasurableSet {z : E | M a ≤ ‖z‖} :=
        (isClosed_le continuous_const continuous_norm).measurableSet
      have htail : Q {y | M a ≤ ‖y a‖} = P a (count T a) {z | M a ≤ ‖z‖} := by
        have he := (measurePreserving_eval (μ := fun b ↦ P b (count T b)) a).map_eq
        rw [← he, Measure.map_apply (measurable_pi_apply a) hm]
        rfl
      rw [htail]
      refine (hT a).2.trans ?_
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _
      have h1 : (T * w a - k) * (r / w a) ≤ count T a * (r / w a) :=
        mul_le_mul_of_nonneg_right (hlo a) (div_nonneg hr0.le (hw a).le)
      have h2 : (T * w a - k) * (r / w a) = T * r - k * (r / w a) := by
        have := (hw a).ne'
        field_simp
      linarith

  · intro x U hU r hr
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    have htop (a : α) : I a (x a) ≠ ⊤ := by
      intro ha
      have h_top : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ⊤ :=
        ENNReal.sum_eq_top.2 ⟨a, Finset.mem_univ a, by
          rw [ha, ENNReal.mul_top (by simpa using hw a)]⟩
      rw [h_top] at hr
      exact absurd hr (not_lt.2 le_top)
    set t : α → ℝ := fun a ↦ (I a (x a)).toReal
    have ht0 (a : α) : 0 ≤ t a := ENNReal.toReal_nonneg
    have hr' : ∑ a, w a * t a < r := by
      have hJ : (∑ a, ENNReal.ofReal (w a) * I a (x a)) = ENNReal.ofReal (∑ a, w a * t a) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mul_nonneg (hw a).le (ht0 a))]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [ENNReal.ofReal_mul (hw a).le, ENNReal.ofReal_toReal (htop a)]
      rw [hJ, EReal.coe_ennreal_ofReal, max_eq_left (Finset.sum_nonneg fun a _ ↦
        mul_nonneg (hw a).le (ht0 a))] at hr
      exact EReal.coe_lt_coe_iff.1 hr
    set W := ∑ a, w a
    have hW : 0 ≤ W := Finset.sum_nonneg fun a _ ↦ (hw a).le
    set η := (r - ∑ a, w a * t a) / (W + 1)
    have hη : 0 < η := div_pos (by linarith) (by positivity)
    set s : α → ℝ := fun a ↦ t a + η
    have hs0 (a : α) : 0 ≤ s a := by positivity
    have hs (a : α) : (I a (x a) : EReal) < s a := by
      rw [← EReal.coe_ennreal_toReal (htop a)]
      exact EReal.coe_lt_coe_iff.2 (by simp only [s, t]; linarith)
    have hsr : ∑ a, w a * s a ≤ r := by
      have h1 : ∑ a, w a * s a = ∑ a, w a * t a + η * W := by
        simp only [s, W, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun a _ ↦ by ring
      have h2 : η * W ≤ r - ∑ a, w a * t a := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    choose C hC h_ev using fun a ↦ (hP a).lower
      (Metric.ball_mem_nhds (x a) hδ) (hs a)
    refine ⟨(∏ a, C a) * ENNReal.ofReal (Real.exp (-(k * ∑ a, s a))), ?_, ?_⟩
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ ↦ hC a) (by
        exact ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos _))
    filter_upwards [eventually_forall_of_eventually h_ev hw k] with T hT
    have hlo (a : α) : (T : ℝ) * w a - k ≤ count T a := by
      linarith [(abs_le.1 (hcount T a)).1]
    have hhi (a : α) : (count T a : ℝ) ≤ (T : ℝ) * w a + k := by
      linarith [(abs_le.1 (hcount T a)).2]
    have hsub : Set.univ.pi (fun a ↦ Metric.ball (x a) δ) ⊆ U := by
      simpa only [ball_pi _ hδ] using hδU
    refine le_trans ?_ (measure_mono hsub)
    rw [Measure.pi_pi, mul_assoc]
    refine (mul_le_mul_right (prod_ofReal_exp_ge hs0 hsr hhi) _).trans ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ ↦ zero_le) (fun a _ ↦ hT (count T) hlo a)

end
end Mogulskii

