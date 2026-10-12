import PerronWright.Transfer.CartesianDeltaSqrt

/-!
# Arbitrary powers of the Cartesian fold coordinate

The positive-surplus singular expansion contains every integral power of
the canonical square-root coordinate.  The identities below connect those
powers directly to principal complex powers of `1 - w`; they remove any
need to split later coefficient arguments according to parity.
-/

noncomputable section

namespace PerronWright.Transfer

/-- Every natural power of the canonical square-root coordinate is the
corresponding principal half-integer power of `1 - w`. -/
theorem cartesianDeltaSqrt_pow_eq_cpow (m : ℕ) (w : ℂ) :
    cartesianDeltaSqrt w ^ m =
      (1 - w) ^ ((((m : ℝ) / 2 : ℝ) : ℂ)) := by
  unfold cartesianDeltaSqrt Complex.sqrt
  rw [← Complex.cpow_mul_nat]
  congr 1
  push_cast
  ring

/-- Taking an inverse produces the elementary negative half-step
singularity used by transfer. -/
theorem cartesianDeltaSqrt_inv_pow_eq_neg_cpow (m : ℕ) (w : ℂ) :
    (cartesianDeltaSqrt w ^ m)⁻¹ =
      (1 - w) ^ (-((((m : ℝ) / 2 : ℝ) : ℂ))) := by
  rw [cartesianDeltaSqrt_pow_eq_cpow, Complex.cpow_neg]

end PerronWright.Transfer
