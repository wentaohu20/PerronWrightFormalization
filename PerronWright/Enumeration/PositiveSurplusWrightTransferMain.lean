import PerronWright.Enumeration.PositiveSurplusWrightConstant
import PerronWright.Transfer.Base
import PerronWright.Transfer.QuantitativeStirling

/-!
# Fixed-surplus pure-power and factorial main terms

For excess `ell > 0`, the cubic singular exponent is `3 * ell / 2`.
This file separates the two standard asymptotic operations:

* pure-power coefficient extraction contributes
  `k ^ (3 * ell / 2 - 1) / Gamma (3 * ell / 2)`;
* passage from an EGF coefficient to a labelled weight contributes the
  Stirling main term for `k!`.

The final identity proves algebraically that their constant factor is exactly
the physical Wright constant, rather than the untransferred cubic EGF
constant.  No asymptotic hypothesis is introduced here.
-/

open PerronWright
open scoped Classical

noncomputable section

namespace PerronWright.GraphCore

/-- The pure-power singular exponent associated with excess `ell`. -/
def positiveSurplusCubicExponent (ell : ℕ) : ℝ :=
  3 * (ell : ℝ) / 2

/-- The exact coefficient supplied by the pure power
`(1 - z)^(-3 * ell / 2)`, multiplied by the cubic EGF amplitude. -/
def positiveSurplusCubicExactPurePowerCoefficient
    (ell k : ℕ) : ℂ :=
  positiveSurplusCubicEGFConstant ell *
    (PerronWright.Transfer.coefficient
      (positiveSurplusCubicExponent ell) k : ℂ)

/-- The corresponding exact labelled contribution before replacing either
the pure-power coefficient or `k!` by its leading asymptotic. -/
def positiveSurplusCubicExactFactorialCoefficient
    (ell k : ℕ) : ℂ :=
  (k.factorial : ℂ) *
    positiveSurplusCubicExactPurePowerCoefficient ell k

/-- The leading fixed-`ell` pure-power coefficient scale. -/
def positiveSurplusCubicPurePowerCoefficientMain
    (ell k : ℕ) : ℂ :=
  positiveSurplusCubicEGFConstant ell *
    ((Real.rpow (k : ℝ) (positiveSurplusCubicExponent ell - 1) /
      Real.Gamma (positiveSurplusCubicExponent ell) : ℝ) : ℂ)

/-- The labelled fixed-`ell` main term obtained by multiplying the
pure-power coefficient main term by Stirling's main term for `k!`. -/
def positiveSurplusCubicFactorialMain
    (ell k : ℕ) : ℂ :=
  (PerronWright.Transfer.factorialStirlingMainTerm k : ℂ) *
    positiveSurplusCubicPurePowerCoefficientMain ell k

/-- After extracting the constant `sqrt (2 * pi)` from Stirling's formula,
this is the remaining `k`-dependent power scale. -/
def positiveSurplusCubicWrightPowerScale
    (ell k : ℕ) : ℝ :=
  (PerronWright.Transfer.factorialStirlingMainTerm k /
      Real.sqrt (2 * Real.pi)) *
    Real.rpow (k : ℝ) (positiveSurplusCubicExponent ell - 1)

/-- Literal paper form of the remaining positive-surplus power scale. -/
theorem positiveSurplusCubicWrightPowerScale_eq_exp_rpow
    (ell : ℕ) {k : ℕ} (hk : 0 < k) :
    positiveSurplusCubicWrightPowerScale ell k =
      Real.exp (-(k : ℝ)) *
        (k : ℝ) ^
          ((k : ℝ) + positiveSurplusCubicExponent ell - 1 / 2) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have hsqrtProd :
      Real.sqrt (2 * Real.pi * (k : ℝ)) =
        Real.sqrt (2 * Real.pi) * Real.sqrt (k : ℝ) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hsqrtRatio :
      Real.sqrt (2 * Real.pi * (k : ℝ)) /
          Real.sqrt (2 * Real.pi) = Real.sqrt (k : ℝ) := by
    rw [hsqrtProd]
    field_simp [hsqrtTwoPi.ne']
  have hbase :
      ((k : ℝ) / Real.exp 1) ^ k =
        Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
    rw [div_pow, Real.exp_one_pow, Real.exp_neg]
    ring
  unfold positiveSurplusCubicWrightPowerScale
    PerronWright.Transfer.factorialStirlingMainTerm
  calc
    (Real.sqrt (2 * Real.pi * (k : ℝ)) *
          ((k : ℝ) / Real.exp 1) ^ k /
          Real.sqrt (2 * Real.pi)) *
          (k : ℝ) ^ (positiveSurplusCubicExponent ell - 1) =
        (Real.sqrt (2 * Real.pi * (k : ℝ)) /
            Real.sqrt (2 * Real.pi)) *
          ((k : ℝ) / Real.exp 1) ^ k *
          (k : ℝ) ^ (positiveSurplusCubicExponent ell - 1) := by
      ring
    _ = (k : ℝ) ^ (1 / 2 : ℝ) *
          (Real.exp (-(k : ℝ)) * (k : ℝ) ^ (k : ℝ)) *
          (k : ℝ) ^ (positiveSurplusCubicExponent ell - 1) := by
        rw [hsqrtRatio, hbase, ← Real.sqrt_eq_rpow,
          Real.rpow_natCast]
    _ =
        Real.exp (-(k : ℝ)) *
          (((k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (k : ℝ)) *
            (k : ℝ) ^ (positiveSurplusCubicExponent ell - 1)) := by
      ring
    _ = Real.exp (-(k : ℝ)) *
        (k : ℝ) ^
          ((k : ℝ) + positiveSurplusCubicExponent ell - 1 / 2) := by
      rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
      congr 2
      ring

/-- The real scalar identity combining the Gamma coefficient main term with
the Stirling main term. -/
theorem factorial_mul_purePowerScale_eq_transfer_mul_wrightPowerScale
    (ell k : ℕ) (hell : 0 < ell) :
    PerronWright.Transfer.factorialStirlingMainTerm k *
        (Real.rpow (k : ℝ) (positiveSurplusCubicExponent ell - 1) /
          Real.Gamma (positiveSurplusCubicExponent ell)) =
      (Real.sqrt (2 * Real.pi) /
          Real.Gamma (positiveSurplusCubicExponent ell)) *
        positiveSurplusCubicWrightPowerScale ell k := by
  have hs : 0 < positiveSurplusCubicExponent ell := by
    unfold positiveSurplusCubicExponent
    positivity
  have hgamma : Real.Gamma (positiveSurplusCubicExponent ell) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs).ne'
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)).ne'
  unfold positiveSurplusCubicWrightPowerScale
  field_simp [hgamma, hsqrt]

/-- Exact normalization identity: Stirling's factorial main term times the
pure-power coefficient main term is the physical Wright constant times the
remaining `k`-dependent power scale. -/
theorem positiveSurplusCubicFactorialMain_eq_wrightConstant
    (ell k : ℕ) (hell : 0 < ell) :
    positiveSurplusCubicFactorialMain ell k =
      positiveSurplusWrightConstant ell *
        (positiveSurplusCubicWrightPowerScale ell k : ℂ) := by
  have hscale :=
    factorial_mul_purePowerScale_eq_transfer_mul_wrightPowerScale
      ell k hell
  calc
    positiveSurplusCubicFactorialMain ell k =
        positiveSurplusCubicEGFConstant ell *
          ((PerronWright.Transfer.factorialStirlingMainTerm k *
            (Real.rpow (k : ℝ)
                (positiveSurplusCubicExponent ell - 1) /
              Real.Gamma (positiveSurplusCubicExponent ell)) : ℝ) : ℂ) := by
      unfold positiveSurplusCubicFactorialMain
        positiveSurplusCubicPurePowerCoefficientMain
      push_cast
      ring
    _ = positiveSurplusCubicEGFConstant ell *
        (((Real.sqrt (2 * Real.pi) /
            Real.Gamma (positiveSurplusCubicExponent ell)) *
          positiveSurplusCubicWrightPowerScale ell k : ℝ) : ℂ) := by
      rw [hscale]
    _ = positiveSurplusWrightConstant ell *
        (positiveSurplusCubicWrightPowerScale ell k : ℂ) := by
      rw [positiveSurplusWrightConstant_eq_transferFactor_mul_egfConstant]
      unfold positiveSurplusCubicExponent
      push_cast
      ring

/-- The positive-surplus factorial main term in the exact notation of the
Perron--Wright formula. -/
theorem positiveSurplusCubicFactorialMain_eq_exp_rpow
    (ell : ℕ) {k : ℕ} (hell : 0 < ell) (hk : 0 < k) :
    positiveSurplusCubicFactorialMain ell k =
      positiveSurplusWrightConstant ell *
        ((Real.exp (-(k : ℝ)) *
          (k : ℝ) ^
            ((k : ℝ) + positiveSurplusCubicExponent ell - 1 / 2) : ℝ) : ℂ) := by
  rw [positiveSurplusCubicFactorialMain_eq_wrightConstant ell k hell,
    positiveSurplusCubicWrightPowerScale_eq_exp_rpow ell hk]

end PerronWright.GraphCore
