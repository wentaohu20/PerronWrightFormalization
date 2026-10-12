import PerronWright.Probability.BrownianParabolicDriftTiltGeometry
import PerronWright.Probability.FactorialDensity

/-! # Literal density factorization under excursion deletion

The proved parabolic exponential normalization is exactly twice the
homogeneous factorial-density exponent. Its deletion cocycle yields the
literal recursive density with the residual parameter `lambda - x`.
These are algebraic identities, not an assumed Brownian Palm law.
-/

open scoped BigOperators NNReal
noncomputable section

namespace PerronWright.BrownianFactorialDensityDeletion

open FactorialDensity

theorem energy_eq_twice_criticalExponent (lambda : ℝ) (T : ℝ≥0) :
    BrownianParabolicDriftTiltGeometry.energy lambda T =
      2 * criticalExponent 1 1 lambda (T : ℝ) := by
  unfold BrownianParabolicDriftTiltGeometry.energy criticalExponent
  ring

theorem criticalExponent_deletion (lambda x y : ℝ) :
    criticalExponent 1 1 lambda (x+y) =
      criticalExponent 1 1 lambda x + criticalExponent 1 1 (lambda-x) y := by
  unfold criticalExponent
  ring

theorem density_cons {q : ℕ} (lambda x : ℝ) (r : ℕ)
    (xs : Fin q → ℝ) (rs : Fin q → ℕ) :
    density 1 1 lambda (Fin.cons x xs) (Fin.cons r rs) =
      (Real.exp (-criticalExponent 1 1 lambda x)*sizeFactor 1 x r) *
        density 1 1 (lambda-x) xs rs := by
  unfold density
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [criticalExponent_deletion]
  rw [neg_add, Real.exp_add]
  ring

end PerronWright.BrownianFactorialDensityDeletion
