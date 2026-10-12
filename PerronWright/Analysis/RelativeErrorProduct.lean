import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary relative-error products

This public algebraic lemma is used when the positive-surplus field estimate
is multiplied by the bounded-surplus scalar factor `t^(r-1)`.
-/

namespace PerronWright.RelativeErrorProduct

/-- Two relative errors of size `O(x)` remain of size `O(x)` under
multiplication, with an explicit constant valid for `0 ≤ x ≤ 1`. -/
theorem abs_two_factor_sub_one_le
    {a b x A B : ℝ}
    (hx : 0 ≤ x) (hxone : x ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a - 1| ≤ A * x) (hb : |b - 1| ≤ B * x) :
    |a * b - 1| ≤ (A * (1 + B) + B) * x := by
  have hBx : B * x ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxone hB
  have hbabs : |b| ≤ 1 + B := by
    calc
      |b| = |(b - 1) + 1| := by
        apply congrArg abs
        ring
      _ ≤ |b - 1| + 1 := by simpa using abs_add_le (b - 1) 1
      _ ≤ B * x + 1 := by linarith
      _ ≤ 1 + B := by linarith
  have hdecomp : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [hdecomp]
  calc
    |(a - 1) * b + (b - 1)| ≤ |a - 1| * |b| + |b - 1| := by
      simpa only [abs_mul] using abs_add_le ((a - 1) * b) (b - 1)
    _ ≤ (A * x) * (1 + B) + B * x :=
      add_le_add
        (mul_le_mul ha hbabs (abs_nonneg _) (mul_nonneg hA hx)) hb
    _ = (A * (1 + B) + B) * x := by ring

end PerronWright.RelativeErrorProduct
