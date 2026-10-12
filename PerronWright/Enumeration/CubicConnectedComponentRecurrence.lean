import PerronWright.Enumeration.CubicConnectedComponentConvolution
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Nonlinear recurrence of the literal connected cubic compensation

The pointing identity is the proved finite root-component decomposition.
The total-series differential equation comes from the proved labelled
half-edge coefficient count.  Cancelling the nonzero total series gives
the connected Riccati equation and its actual coefficient recurrence.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

def cubicAllSeries : PowerSeries ℝ := PowerSeries.mk allCubicCompensation

def cubicConnectedSeries : PowerSeries ℝ := PowerSeries.mk connectedCubicCompensation

def cubicEuler (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.derivative ℝ f

theorem coeff_cubicEuler (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (cubicEuler f) = (n : ℝ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [cubicEuler]
  | succ n =>
    rw [cubicEuler,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative]
    push_cast
    ring

theorem cubicEuler_mul (f g : PowerSeries ℝ) :
    cubicEuler (f * g) = cubicEuler f * g + f * cubicEuler g := by
  unfold cubicEuler
  rw [(PowerSeries.derivative ℝ).leibniz]
  simp only [smul_eq_mul]
  ring

theorem connectedCubicCompensation_pointing_convolution (n : ℕ) :
    (n : ℝ) * allCubicCompensation n =
      ∑ j ∈ Finset.Icc 1 n,
        (j : ℝ) * connectedCubicCompensation j * allCubicCompensation (n - j) := by
  have h := cubicCompensation_root_convolution n
  have hsum : (∑ j ∈ Finset.Icc 1 n,
      (2 * j : ℝ) * connectedCubicCompensation j * allCubicCompensation (n - j)) =
      ∑ j : CubicRootSize n,
        (2 * j.val : ℝ) * connectedCubicCompensation j.val *
          allCubicCompensation (n - j.val) :=
    Finset.sum_subtype (Finset.Icc 1 n)
      (fun _ ↦ by simp only [Finset.mem_Icc]; omega) _
  rw [← hsum] at h
  have hscale : (∑ j ∈ Finset.Icc 1 n,
      (2 * j : ℝ) * connectedCubicCompensation j * allCubicCompensation (n - j)) =
      2 * ∑ j ∈ Finset.Icc 1 n,
        (j : ℝ) * connectedCubicCompensation j * allCubicCompensation (n - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  rw [hscale] at h
  nlinarith only [h]

theorem cubicAllSeries_euler :
    cubicEuler cubicAllSeries = cubicEuler cubicConnectedSeries * cubicAllSeries := by
  apply PowerSeries.ext
  intro n
  rw [coeff_cubicEuler,PowerSeries.coeff_mul]
  simp_rw [coeff_cubicEuler]
  simp only [cubicAllSeries,cubicConnectedSeries,PowerSeries.coeff_mk]
  change (n : ℝ) * allCubicCompensation n =
    ∑ p ∈ Finset.antidiagonal n,
      ((p.1 : ℝ) * connectedCubicCompensation p.1) * allCubicCompensation p.2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hrange,Finset.sum_insert (by simp)]
  simpa only [Nat.cast_zero,zero_mul,zero_add] using
    connectedCubicCompensation_pointing_convolution n

theorem cubicAllSeries_derivative :
    PowerSeries.derivative ℝ cubicAllSeries =
      PowerSeries.derivative ℝ cubicConnectedSeries * cubicAllSeries := by
  apply PowerSeries.X_mul_cancel
  simpa only [cubicEuler,mul_assoc] using cubicAllSeries_euler

theorem cubicAllSeries_ne_zero : cubicAllSeries ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff 0) h
  simp [cubicAllSeries,allCubicCompensation_zero] at hc

theorem cubicAllSeries_differential_equation :
    PowerSeries.C (24 : ℝ) * PowerSeries.derivative ℝ cubicAllSeries =
      PowerSeries.C (36 : ℝ) * cubicEuler (cubicEuler cubicAllSeries) +
        PowerSeries.C (36 : ℝ) * cubicEuler cubicAllSeries +
        PowerSeries.C (5 : ℝ) * cubicAllSeries := by
  apply PowerSeries.ext
  intro n
  simp only [map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_derivative,
    coeff_cubicEuler]
  simp only [cubicAllSeries,PowerSeries.coeff_mk]
  have h := allCubicCompensation_recurrence n
  nlinarith only [h]

/-- Actual connected generating equation, obtained by dividing the total
configuration equation by its nonzero series, not by supplying a connected
recurrence as a premise. -/
theorem cubicConnectedSeries_differential_equation :
    PowerSeries.C (24 : ℝ) * PowerSeries.derivative ℝ cubicConnectedSeries =
      PowerSeries.C (36 : ℝ) * cubicEuler (cubicEuler cubicConnectedSeries) +
        PowerSeries.C (36 : ℝ) * cubicEuler cubicConnectedSeries +
        PowerSeries.C (36 : ℝ) * (cubicEuler cubicConnectedSeries) ^ 2 +
        PowerSeries.C (5 : ℝ) := by
  have heuler : cubicEuler (cubicEuler cubicAllSeries) =
      (cubicEuler (cubicEuler cubicConnectedSeries) +
        (cubicEuler cubicConnectedSeries) ^ 2) * cubicAllSeries := by
    rw [cubicAllSeries_euler,cubicEuler_mul,cubicAllSeries_euler]
    ring
  have h := cubicAllSeries_differential_equation
  rw [cubicAllSeries_derivative,heuler,cubicAllSeries_euler] at h
  apply mul_right_cancel₀ cubicAllSeries_ne_zero
  calc
    _ = PowerSeries.C (36 : ℝ) *
        ((cubicEuler (cubicEuler cubicConnectedSeries) +
          (cubicEuler cubicConnectedSeries) ^ 2) * cubicAllSeries) +
        PowerSeries.C (36 : ℝ) * (cubicEuler cubicConnectedSeries * cubicAllSeries) +
        PowerSeries.C (5 : ℝ) * cubicAllSeries := by simpa only [mul_assoc] using h
    _ = _ := by ring

/-- Nonlinear recurrence of the unchanged literal connected compensation
sum.  Zero-index factors automatically remove the two endpoint terms of
the antidiagonal, and the constant `5` occurs only at order zero. -/
theorem connectedCubicCompensation_nonlinear_recurrence (n : ℕ) :
    24 * ((n : ℝ) + 1) * connectedCubicCompensation (n + 1) =
      36 * (n : ℝ) * ((n : ℝ) + 1) * connectedCubicCompensation n +
        36 * ∑ p ∈ Finset.antidiagonal n,
          ((p.1 : ℝ) * connectedCubicCompensation p.1) *
            ((p.2 : ℝ) * connectedCubicCompensation p.2) +
        (if n = 0 then 5 else 0) := by
  have h := congrArg (PowerSeries.coeff n) cubicConnectedSeries_differential_equation
  simp only [map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_derivative,
    coeff_cubicEuler,PowerSeries.coeff_C] at h
  rw [pow_two,PowerSeries.coeff_mul] at h
  simp only [coeff_cubicEuler,cubicConnectedSeries,PowerSeries.coeff_mk] at h
  nlinarith only [h]

/-- The recurrence stated directly for the original finite labelled
connected-kernel sum, rather than for a newly specified coefficient family. -/
theorem sum_labelledCubicKernelInverseMultiplicityReal_nonlinear_recurrence (n : ℕ) :
    let c : ℕ → ℝ := fun ell ↦
      letI := labelledConnectedCubicKernelFintype ell
      ∑ K : LabelledConnectedCubicKernel ell, labelledCubicKernelInverseMultiplicityReal K
    24 * ((n : ℝ) + 1) * c (n + 1) =
      36 * (n : ℝ) * ((n : ℝ) + 1) * c n +
        36 * ∑ p ∈ Finset.antidiagonal n,
          ((p.1 : ℝ) * c p.1) * ((p.2 : ℝ) * c p.2) +
        (if n = 0 then 5 else 0) :=
  connectedCubicCompensation_nonlinear_recurrence n

/-- The unchanged paper Wright constant is precisely the Gamma-normalized
literal connected compensation coefficient governed by the recurrence. -/
theorem wrightConstant_eq_literal_connectedCompensation (ell : ℕ) :
    PerronWrightFormulaMainTerm.wrightConstant (ell + 2) =
      (Real.sqrt (2 * Real.pi) / Real.Gamma (3 * ((ell + 1 : ℕ) : ℝ) / 2)) *
        (Real.sqrt 2 ^ (3 * (ell + 1)))⁻¹ *
        (letI := labelledConnectedCubicKernelFintype (ell + 1)
          ∑ K : LabelledConnectedCubicKernel (ell + 1),
            labelledCubicKernelInverseMultiplicityReal K) := by
  rw [PerronWrightFormulaMainTerm.wrightConstant_succ_succ,
    positiveSurplusWrightConstantReal_eq_connectedCompensation]
  rfl

theorem connectedCubicCompensation_two : connectedCubicCompensation 2 = 5 / 16 := by
  have h := connectedCubicCompensation_nonlinear_recurrence 1
  norm_num [Finset.antidiagonal,connectedCubicCompensation_zero,
    connectedCubicCompensation_one] at h
  linarith

theorem connectedCubicCompensation_three : connectedCubicCompensation 3 = 1105 / 1152 := by
  have h := connectedCubicCompensation_nonlinear_recurrence 2
  norm_num [Finset.antidiagonal,connectedCubicCompensation_zero,
    connectedCubicCompensation_one,connectedCubicCompensation_two] at h
  linarith

end PerronWright.GraphCore
