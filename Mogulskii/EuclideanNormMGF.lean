import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory
open scoped BigOperators

namespace Mogulskii

local instance euclideanNormMGFMeasurableSpace {d : ℕ} :
    MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance euclideanNormMGFBorelSpace {d : ℕ} :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

theorem integrable_exp_mul_norm_of_inner {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)} (hX : Measurable X)
    (h : ∀ θ : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp (inner ℝ θ (X ω))) μ)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun ω => Real.exp (t * ‖X ω‖)) μ := by
  classical
  let θ : (Fin d → Bool) → EuclideanSpace ℝ (Fin d) :=
    fun s => WithLp.toLp 2 fun i => if s i then t else -t
  have hi : Integrable (fun ω => ∑ s : Fin d → Bool, Real.exp (inner ℝ (θ s) (X ω))) μ :=
    integrable_finsetSum _ fun s _ => h (θ s)
  refine hi.mono' (Real.continuous_exp.measurable.comp ((continuous_const.mul
    continuous_norm).measurable.comp hX)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  let s : Fin d → Bool := fun i => decide (0 ≤ X ω i)
  have hnorm : ‖X ω‖ ≤ ∑ i : Fin d, |X ω i| := by
    have heq : ∑ i : Fin d, PiLp.single 2 i (X ω i) = X ω := by
      ext j
      change EuclideanSpace.proj (𝕜 := ℝ) j (∑ i : Fin d, PiLp.single 2 i (X ω i)) = X ω j
      rw [map_sum]
      simp [EuclideanSpace.coe_proj, PiLp.single_apply, Finset.sum_ite_eq']
    calc
      ‖X ω‖ = ‖∑ i : Fin d, PiLp.single 2 i (X ω i)‖ := congrArg norm heq.symm
      _ ≤ ∑ i : Fin d, ‖PiLp.single (β := fun _ : Fin d => ℝ) 2 i (X ω i)‖ :=
        norm_sum_le Finset.univ (fun i : Fin d => PiLp.single 2 i (X ω i))
      _ = _ := by simp [PiLp.norm_single, Real.norm_eq_abs]
  have hinner : inner ℝ (θ s) (X ω) = t * ∑ i : Fin d, |X ω i| := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ X ω i
    · simp [θ, s, hi, abs_of_nonneg hi, mul_comm]
    · simp [θ, s, hi, abs_of_neg (lt_of_not_ge hi), mul_comm]
  calc
    _ ≤ Real.exp (inner ℝ (θ s) (X ω)) := Real.exp_le_exp.mpr (by
      rw [hinner]
      exact mul_le_mul_of_nonneg_left hnorm ht)
    _ ≤ ∑ sign : Fin d → Bool, Real.exp (inner ℝ (θ sign) (X ω)) :=
      Finset.single_le_sum (f := fun sign => Real.exp (inner ℝ (θ sign) (X ω)))
        (fun sign _ => (Real.exp_pos _).le) (Finset.mem_univ s)

end Mogulskii

