import PerronWright.Probability.BrownianBoundarySeriesRiccati
import PerronWright.Probability.PolynomialSeriesFirstOrderUniqueness

/-! # The transport identity behind Wright's recurrence

Spatial and area-parameter differentiation of the proved Riccati
equation give a homogeneous first-order equation for the residual.
Polynomial coefficient uniqueness forces that residual to vanish.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundaryRiccatiTransport

open BrownianBoundarySeriesRiccati PolynomialCoefficientSeriesDerivation
open PolynomialSeriesFirstOrderUniqueness

private theorem euler_add (f g : PowerSeries ℝ[X]) :
    parameterEuler (f+g) = parameterEuler f+parameterEuler g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_parameterEuler,map_add]
  ring

private theorem euler_sub (f g : PowerSeries ℝ[X]) :
    parameterEuler (f-g) = parameterEuler f-parameterEuler g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_parameterEuler,map_sub]
  ring

private theorem euler_C (P : ℝ[X]) : parameterEuler (PowerSeries.C P) = 0 := by
  simp [parameterEuler]

private theorem euler_X : parameterEuler (PowerSeries.X : PowerSeries ℝ[X]) = PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_parameterEuler]
  | succ n =>
    cases n <;> simp [coeff_parameterEuler,PowerSeries.coeff_X]

private theorem d_two : spatialDerivative (2 : PowerSeries ℝ[X]) = 0 := by
  rw [← map_ofNat PowerSeries.C,spatialDerivative_C]
  simp

private theorem d_three : spatialDerivative (3 : PowerSeries ℝ[X]) = 0 := by
  rw [← map_ofNat PowerSeries.C,spatialDerivative_C]
  simp

private theorem e_two : parameterEuler (2 : PowerSeries ℝ[X]) = 0 := by
  rw [← map_ofNat PowerSeries.C,euler_C]

private theorem e_one : parameterEuler (1 : PowerSeries ℝ[X]) = 0 := by
  rw [← map_one PowerSeries.C,euler_C]

private theorem d_spatialX : spatialDerivative (PowerSeries.C (X : ℝ[X])) = 1 := by
  rw [spatialDerivative_C,derivative_X,map_one]

theorem logarithmicBoundarySeries_second_equation :
    spatialDerivative (spatialDerivative logarithmicBoundarySeries)+
      2*logarithmicBoundarySeries*spatialDerivative logarithmicBoundarySeries = -2*PowerSeries.X := by
  have h := congrArg spatialDerivative logarithmicBoundarySeries_riccati
  rw [pow_two] at h
  simp only [spatialDerivative_add,spatialDerivative_sub,spatialDerivative_mul,
    spatialDerivative_one,spatialDerivative_X,d_two,d_spatialX,mul_zero,zero_mul,
    zero_add,add_zero,mul_one] at h
  linear_combination h

theorem logarithmicBoundarySeries_euler_equation :
    spatialDerivative (parameterEuler logarithmicBoundarySeries)+
      2*logarithmicBoundarySeries*parameterEuler logarithmicBoundarySeries =
        -2*PowerSeries.X*PowerSeries.C X := by
  have h := congrArg parameterEuler logarithmicBoundarySeries_riccati
  rw [pow_two] at h
  simp only [euler_add,euler_sub,parameterEuler_mul,e_one,e_two,euler_X,euler_C,
    ← spatialDerivative_parameterEuler,mul_zero,zero_mul,zero_add,add_zero] at h
  linear_combination h

def transportResidual : PowerSeries ℝ[X] :=
  spatialDerivative logarithmicBoundarySeries-
    PowerSeries.X*(3*parameterEuler logarithmicBoundarySeries-logarithmicBoundarySeries-
      PowerSeries.C X*spatialDerivative logarithmicBoundarySeries)

theorem transportResidual_homogeneous :
    spatialDerivative transportResidual+2*logarithmicBoundarySeries*transportResidual = 0 := by
  have hD := logarithmicBoundarySeries_second_equation
  have hE := logarithmicBoundarySeries_euler_equation
  have hR := logarithmicBoundarySeries_riccati
  unfold transportResidual
  simp only [spatialDerivative_sub,spatialDerivative_mul,spatialDerivative_X,d_three,
    d_spatialX,zero_mul,zero_add,one_mul]
  linear_combination
    (1+PowerSeries.X*PowerSeries.C X)*hD-
      3*PowerSeries.X*hE+2*PowerSeries.X*hR

theorem transportResidual_zero : transportResidual = 0 := by
  apply homogeneous_first_order_zero logarithmicBoundarySeries transportResidual
    coeff_zero_logarithmicBoundarySeries
  simpa only [map_ofNat] using transportResidual_homogeneous

theorem logarithmicBoundarySeries_transport :
    spatialDerivative logarithmicBoundarySeries =
      PowerSeries.X*(3*parameterEuler logarithmicBoundarySeries-logarithmicBoundarySeries-
        PowerSeries.C X*spatialDerivative logarithmicBoundarySeries) := by
  exact sub_eq_zero.mp transportResidual_zero

end PerronWright.BrownianBoundaryRiccatiTransport
