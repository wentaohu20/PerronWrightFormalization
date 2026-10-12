import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic

/-! # Spatial differentiation of polynomial-coefficient power series

Coefficientwise polynomial differentiation is a genuine derivation,
and it commutes with the area-parameter Euler operator. All algebraic
identities are proved from the finite coefficient convolution.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.PolynomialCoefficientSeriesDerivation

private theorem formalDerivative_mul {R : Type*} [CommSemiring R]
    (f g : PowerSeries R) :
    PowerSeries.derivative R (f*g) = f*PowerSeries.derivative R g+g*PowerSeries.derivative R f := by
  simpa only [smul_eq_mul] using (PowerSeries.derivative R).leibniz f g

def spatialDerivative (f : PowerSeries ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mk (fun n ↦ (PowerSeries.coeff n f).derivative)

theorem coeff_spatialDerivative (f : PowerSeries ℝ[X]) (n : ℕ) :
    PowerSeries.coeff n (spatialDerivative f) = (PowerSeries.coeff n f).derivative := by
  simp only [spatialDerivative,PowerSeries.coeff_mk]

theorem spatialDerivative_add (f g : PowerSeries ℝ[X]) :
    spatialDerivative (f+g) = spatialDerivative f+spatialDerivative g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_spatialDerivative,map_add]

theorem spatialDerivative_neg (f : PowerSeries ℝ[X]) :
    spatialDerivative (-f) = -spatialDerivative f := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_spatialDerivative,map_neg]

theorem spatialDerivative_sub (f g : PowerSeries ℝ[X]) :
    spatialDerivative (f-g) = spatialDerivative f-spatialDerivative g := by
  rw [sub_eq_add_neg,spatialDerivative_add,spatialDerivative_neg,sub_eq_add_neg]

theorem spatialDerivative_mul (f g : PowerSeries ℝ[X]) :
    spatialDerivative (f*g) = spatialDerivative f*g+f*spatialDerivative g := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_spatialDerivative,PowerSeries.coeff_mul,derivative_sum,
    derivative_mul,map_add]
  rw [Finset.sum_add_distrib]

theorem spatialDerivative_C (P : ℝ[X]) :
    spatialDerivative (PowerSeries.C P) = PowerSeries.C P.derivative := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [coeff_spatialDerivative]

theorem spatialDerivative_one : spatialDerivative (1 : PowerSeries ℝ[X]) = 0 := by
  rw [← map_one PowerSeries.C,spatialDerivative_C]
  simp

theorem spatialDerivative_X : spatialDerivative (PowerSeries.X : PowerSeries ℝ[X]) = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_spatialDerivative]
  | succ n =>
    cases n <;> simp [coeff_spatialDerivative,PowerSeries.coeff_X]

theorem spatialDerivative_parameterDerivative (f : PowerSeries ℝ[X]) :
    spatialDerivative (PowerSeries.derivative ℝ[X] f) =
      PowerSeries.derivative ℝ[X] (spatialDerivative f) := by
  apply PowerSeries.ext
  intro n
  simp [coeff_spatialDerivative,PowerSeries.coeff_derivative,Polynomial.derivative_mul]

def parameterEuler (f : PowerSeries ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.X*PowerSeries.derivative ℝ[X] f

theorem coeff_parameterEuler (f : PowerSeries ℝ[X]) (n : ℕ) :
    PowerSeries.coeff n (parameterEuler f) = (n : ℝ[X])*PowerSeries.coeff n f := by
  cases n with
  | zero => simp [parameterEuler]
  | succ n =>
    rw [parameterEuler,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative]
    push_cast
    ring

theorem spatialDerivative_parameterEuler (f : PowerSeries ℝ[X]) :
    spatialDerivative (parameterEuler f) = parameterEuler (spatialDerivative f) := by
  rw [parameterEuler,spatialDerivative_mul,spatialDerivative_X,zero_mul,zero_add,
    spatialDerivative_parameterDerivative]
  rfl

theorem parameterEuler_mul (f g : PowerSeries ℝ[X]) :
    parameterEuler (f*g) = parameterEuler f*g+f*parameterEuler g := by
  unfold parameterEuler
  rw [formalDerivative_mul]
  ring

end PerronWright.PolynomialCoefficientSeriesDerivation
