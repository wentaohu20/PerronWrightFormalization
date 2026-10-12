import PerronWright.Probability.BrownianGaussianSkeleton

/-! # Literal nonnegative rational dyadic time coordinates -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section

namespace PerronWright.BrownianDyadicGrid

open BrownianGaussianSkeleton

def dyadicTime (n k : ℕ) : RationalTime := ⟨(k : ℚ) / (2 : ℚ) ^ n,by positivity⟩

@[simp] theorem dyadicTime_val (n k : ℕ) : (dyadicTime n k).val = (k : ℚ) / (2 : ℚ) ^ n := rfl

@[simp] theorem dyadicTime_real (n k : ℕ) :
    ((dyadicTime n k).val : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by
  simp [dyadicTime]

theorem dyadicTime_adjacent_real (n k : ℕ) :
    ((dyadicTime n (k + 1)).val : ℝ) - ((dyadicTime n k).val : ℝ) = 1 / (2 : ℝ) ^ n := by
  rw [dyadicTime_real,dyadicTime_real,Nat.cast_add,Nat.cast_one]
  ring

theorem dyadicTime_adjacent_abs (n k : ℕ) :
    |((dyadicTime n (k + 1)).val : ℝ) - ((dyadicTime n k).val : ℝ)| = 1 / (2 : ℝ) ^ n := by
  rw [dyadicTime_adjacent_real,abs_of_nonneg (by positivity)]

theorem dyadicTime_succ_double (n k : ℕ) : dyadicTime (n + 1) (2 * k) = dyadicTime n k := by
  apply Subtype.ext
  simp only [dyadicTime_val,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  field_simp

theorem dyadicTime_zero (k : ℕ) : dyadicTime 0 k = ⟨(k : ℚ),by positivity⟩ := by
  apply Subtype.ext
  simp

end PerronWright.BrownianDyadicGrid
