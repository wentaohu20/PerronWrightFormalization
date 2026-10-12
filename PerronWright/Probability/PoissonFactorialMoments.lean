import PerronWright.Probability.PoissonCountKernel
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact factorial moments of genuine Poisson count laws

All orders are computed from the actual exponential probability mass
series. The finite mixed moment identity uses the actual product law.
No Poisson moment formula is introduced as an interface assumption.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

namespace PerronWright.PoissonFactorialMoments

def weightedFactorial (r : ℝ≥0) (q n : ℕ) : ℝ :=
  (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) *
    (n.descFactorial q : ℝ)

theorem weightedFactorial_shift (r : ℝ≥0) (q n : ℕ) :
    weightedFactorial r q (n + q) =
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ q) *
        ((r : ℝ) ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hd : ((n + q).descFactorial q : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (Nat.le_add_left q n)))
  have hf : ((n + q).factorial : ℝ) =
      (n.factorial : ℝ) * ((n + q).descFactorial q : ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel] using
      (Nat.factorial_mul_descFactorial (Nat.le_add_left q n)).symm)
  unfold weightedFactorial
  rw [hf, pow_add]
  field_simp

theorem weightedFactorial_zero_of_lt (r : ℝ≥0) {q n : ℕ} (hn : n < q) :
    weightedFactorial r q n = 0 := by
  simp [weightedFactorial, Nat.descFactorial_of_lt hn]

theorem hasSum_weightedFactorial (r : ℝ≥0) (q : ℕ) :
    HasSum (weightedFactorial r q) ((r : ℝ) ^ q) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ q)
  have hvalue : (Real.exp (-(r : ℝ)) * (r : ℝ) ^ q) *
      NormedSpace.exp (r : ℝ) = (r : ℝ) ^ q := by
    rw [← Real.exp_eq_exp_ℝ]
    rw [mul_assoc, mul_comm ((r : ℝ) ^ q), ← mul_assoc, ← Real.exp_add]
    simp
  rw [hvalue] at hs
  have hshift : HasSum (fun n ↦ weightedFactorial r q (n + q)) ((r : ℝ) ^ q) := by
    simpa only [weightedFactorial_shift] using hs
  have hlow : (∑ n ∈ Finset.range q, weightedFactorial r q n) = 0 :=
    Finset.sum_eq_zero (fun n hn ↦ weightedFactorial_zero_of_lt r (Finset.mem_range.mp hn))
  simpa only [hlow, zero_add] using hshift.sum_range_add

theorem integrable_descFactorial (r : ℝ≥0) (q : ℕ) :
    Integrable (fun n : ℕ ↦ (n.descFactorial q : ℝ)) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  have he : (fun n : ℕ ↦
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) *
        ‖(n.descFactorial q : ℝ)‖) = weightedFactorial r q := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (n.descFactorial q : ℝ) from Nat.cast_nonneg _)]
    rfl
  rw [he]
  exact (hasSum_weightedFactorial r q).summable

/-- Every actual Poisson descending-factorial moment equals its rate power. -/
theorem integral_descFactorial (r : ℝ≥0) (q : ℕ) :
    (∫ n : ℕ, (n.descFactorial q : ℝ) ∂poissonMeasure r) = (r : ℝ) ^ q := by
  rw [integral_poissonMeasure' (integrable_descFactorial r q)]
  exact (hasSum_weightedFactorial r q).tsum_eq

variable {ι : Type*} [Fintype ι]

/-- Exact mixed factorial moments of the literal independent joint counts. -/
theorem integral_mixed_descFactorial (r : ι → ℝ≥0) (q : ι → ℕ) :
    (∫ n : ι → ℕ, ∏ i, ((n i).descFactorial (q i) : ℝ)
      ∂PoissonCountKernel.finiteCountLaw r) = ∏ i, (r i : ℝ) ^ q i := by
  unfold PoissonCountKernel.finiteCountLaw
  calc
    _ = ∏ i, ∫ n : ℕ, (n.descFactorial (q i) : ℝ) ∂poissonMeasure (r i) :=
      integral_fintype_prod_eq_prod (fun i (n : ℕ) ↦ (n.descFactorial (q i) : ℝ))
    _ = _ := by simp only [integral_descFactorial]

end PerronWright.PoissonFactorialMoments
