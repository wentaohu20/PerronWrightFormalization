import PerronWright.Probability.BrownianBoundaryNormalizedSeries

/-! # Riccati equation of the actual normalized boundary series

The logarithmic derivative is formed by a literal formal-series
inverse. Its Riccati equation is derived from the actual boundary
polynomial equation, not supplied as an Airy or differential interface.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundarySeriesRiccati

open BrownianBoundaryNormalizedSeries PolynomialCoefficientSeriesDerivation

theorem boundarySeriesInverse_spatialDerivative :
    spatialDerivative boundarySeriesInverse =
      -boundarySeriesInverse*spatialDerivative boundarySeries*boundarySeriesInverse := by
  have hp : spatialDerivative boundarySeries*boundarySeriesInverse+
      boundarySeries*spatialDerivative boundarySeriesInverse = 0 := by
    rw [← spatialDerivative_mul,boundarySeries_mul_inverse,spatialDerivative_one]
  calc
    _ = (boundarySeriesInverse*boundarySeries)*spatialDerivative boundarySeriesInverse := by
      rw [boundarySeries_inverse_mul,one_mul]
    _ = boundarySeriesInverse*(spatialDerivative boundarySeries*boundarySeriesInverse+
          boundarySeries*spatialDerivative boundarySeriesInverse)-
          boundarySeriesInverse*spatialDerivative boundarySeries*boundarySeriesInverse := by ring
    _ = _ := by rw [hp]; ring

def logarithmicBoundarySeries : PowerSeries ℝ[X] :=
  -1+spatialDerivative boundarySeries*boundarySeriesInverse

theorem coeff_zero_logarithmicBoundarySeries :
    PowerSeries.coeff 0 logarithmicBoundarySeries = -1 := by
  rw [logarithmicBoundarySeries,map_add]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_neg,map_one,map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_spatialDerivative,
    coeff_boundarySeries,normalizedBoundaryPolynomial_zero]
  simp

theorem logarithmicBoundarySeries_riccati :
    spatialDerivative logarithmicBoundarySeries+logarithmicBoundarySeries^2 =
      1-2*PowerSeries.X*PowerSeries.C X := by
  have hODE : spatialDerivative (spatialDerivative boundarySeries)-
      2*spatialDerivative boundarySeries = -2*PowerSeries.X*PowerSeries.C X*boundarySeries := by
    simpa only [map_ofNat] using boundarySeries_equation
  simp only [logarithmicBoundarySeries,spatialDerivative_add,spatialDerivative_neg,
    spatialDerivative_one,spatialDerivative_mul,boundarySeriesInverse_spatialDerivative]
  calc
    _ = 1+(spatialDerivative (spatialDerivative boundarySeries)-
        2*spatialDerivative boundarySeries)*boundarySeriesInverse := by ring
    _ = 1+(-2*PowerSeries.X*PowerSeries.C X*boundarySeries)*boundarySeriesInverse := by rw [hODE]
    _ = 1-2*PowerSeries.X*PowerSeries.C X := by
      rw [mul_assoc (-2*PowerSeries.X*PowerSeries.C X),boundarySeries_mul_inverse]
      ring

end PerronWright.BrownianBoundarySeriesRiccati
