import PerronWright.Probability.BrownianBoundaryWrightCoefficients

/-! # Literal initial slopes of the actual boundary polynomials

Evaluation at the boundary sends the normalized series and its
formal inverse to one. Thus positive-order logarithmic coefficients
are exactly the normalized initial slopes, not a new coefficient family.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundarySeriesInitialSlope

open BrownianBoundaryNormalizedSeries BrownianBoundarySeriesRiccati
open BrownianBoundaryWrightCoefficients PolynomialCoefficientSeriesDerivation
open BrownianKilledBoundaryPolynomial

theorem eval_boundarySeries :
    PowerSeries.map (Polynomial.evalRingHom (0 : ℝ)) boundarySeries = 1 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map,coeff_boundarySeries]
  cases n with
  | zero => simp [normalizedBoundaryPolynomial_zero]
  | succ n =>
    simpa only [Polynomial.coe_evalRingHom,PowerSeries.coeff_one,Nat.add_one_ne_zero,if_false]
      using normalizedBoundaryPolynomial_succ_zero n

theorem eval_boundarySeriesInverse :
    PowerSeries.map (Polynomial.evalRingHom (0 : ℝ)) boundarySeriesInverse = 1 := by
  have h := congrArg (PowerSeries.map (Polynomial.evalRingHom (0 : ℝ))) boundarySeries_mul_inverse
  rwa [map_mul,map_one,eval_boundarySeries,one_mul] at h

theorem eval_logarithmicBoundarySeries :
    PowerSeries.map (Polynomial.evalRingHom (0 : ℝ)) logarithmicBoundarySeries =
      -1+PowerSeries.map (Polynomial.evalRingHom (0 : ℝ)) (spatialDerivative boundarySeries) := by
  rw [logarithmicBoundarySeries,map_add,map_neg,map_one,map_mul,eval_boundarySeriesInverse,mul_one]

theorem logCoefficient_succ_eq_actual_slope (n : ℕ) :
    logCoefficient (n+1) = normalization (n+1)*(boundaryPolynomial (n+1) 1).derivative.eval 0 := by
  have h := congrArg (PowerSeries.coeff (n+1)) eval_logarithmicBoundarySeries
  rw [PowerSeries.coeff_map,map_add,map_neg,PowerSeries.coeff_one,
    if_neg (by omega),neg_zero,zero_add,PowerSeries.coeff_map,
    coeff_spatialDerivative,coeff_boundarySeries] at h
  change logCoefficient (n+1) = (normalizedBoundaryPolynomial (n+1)).derivative.eval 0 at h
  rw [normalizedBoundaryPolynomial,derivative_C_mul,eval_mul,eval_C] at h
  exact h

theorem actual_slope_eq_logCoefficient (n : ℕ) :
    (boundaryPolynomial (n+1) 1).derivative.eval 0 =
      2*((n+1).factorial : ℝ)*logCoefficient (n+1) := by
  rw [logCoefficient_succ_eq_actual_slope,normalization]
  have hf : (((n+1).factorial : ℝ)) ≠ 0 := by positivity
  field_simp

end PerronWright.BrownianBoundarySeriesInitialSlope
