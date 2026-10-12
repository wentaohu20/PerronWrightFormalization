import PerronWright.Enumeration.PositiveSurplusWrightConstant
import PerronWright.Enumeration.PositiveSurplusCubicKernelInhabitant

/-!
# Reality and positivity of the positive-surplus cubic constants

The analytic modules use complex scalars, although every multiplicity in the
finite cubic-kernel sum is a positive real number.  This file exposes the
underlying real constants and proves that the complex constants are their
canonical casts.  Strict positivity uses the explicit cycle-plus-matching
cubic kernel: all summands are already strictly positive, so nonemptiness is
the only remaining combinatorial fact.

For the physical Wright constant the Gamma transfer factor is positive when
`0 < ell`.  Thus its strict positivity reduces exactly to the same kernel
nonemptiness input.
-/

open PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

/-! ## Real forms of the finite cubic sums -/

/-- The reciprocal global presentation multiplicity as a real number. -/
def labelledCubicKernelInverseMultiplicityReal
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) : ℝ :=
  (labelledCubicKernelGlobalMultiplicity K : ℝ)⁻¹

theorem labelledCubicKernelInverseMultiplicityReal_pos
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    0 < labelledCubicKernelInverseMultiplicityReal K := by
  unfold labelledCubicKernelInverseMultiplicityReal
  exact inv_pos.mpr (by
    exact_mod_cast labelledCubicKernelGlobalMultiplicity_pos K)

theorem labelledCubicKernelInverseMultiplicityReal_nonneg
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    0 ≤ labelledCubicKernelInverseMultiplicityReal K :=
  (labelledCubicKernelInverseMultiplicityReal_pos K).le

/-- The real cubic EGF leading-amplitude constant. -/
def positiveSurplusCubicEGFConstantReal (ell : ℕ) : ℝ :=
  letI := labelledConnectedCubicKernelFintype ell
  ((Real.sqrt 2) ^ (3 * ell))⁻¹ *
    ∑ K : LabelledConnectedCubicKernel ell,
      labelledCubicKernelInverseMultiplicityReal K

/-- The complex EGF constant used by the analytic chain is the cast of its
literal real finite sum. -/
theorem positiveSurplusCubicEGFConstant_eq_ofReal (ell : ℕ) :
    positiveSurplusCubicEGFConstant ell =
      (positiveSurplusCubicEGFConstantReal ell : ℂ) := by
  unfold positiveSurplusCubicEGFConstant
    positiveSurplusCubicEGFConstantReal
    labelledCubicKernelInverseMultiplicity
    labelledCubicKernelInverseMultiplicityReal
  push_cast
  rfl

theorem positiveSurplusCubicEGFConstantReal_pos
    (ell : ℕ) (hell : 0 < ell) :
    0 < positiveSurplusCubicEGFConstantReal ell := by
  unfold positiveSurplusCubicEGFConstantReal
  apply mul_pos
  · positivity
  · apply Finset.sum_pos
    · intro K _
      exact labelledCubicKernelInverseMultiplicityReal_pos K
    · refine ⟨positiveSurplusCubicKernel ell hell, ?_⟩
      simp

theorem positiveSurplusCubicEGFConstantReal_nonneg (ell : ℕ) :
    0 ≤ positiveSurplusCubicEGFConstantReal ell := by
  unfold positiveSurplusCubicEGFConstantReal
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun K _ ↦
      labelledCubicKernelInverseMultiplicityReal_nonneg K)

theorem positiveSurplusCubicEGFConstant_im (ell : ℕ) :
    (positiveSurplusCubicEGFConstant ell).im = 0 := by
  rw [positiveSurplusCubicEGFConstant_eq_ofReal]
  exact Complex.ofReal_im _

theorem positiveSurplusCubicEGFConstant_re_pos
    (ell : ℕ) (hell : 0 < ell) :
    0 < (positiveSurplusCubicEGFConstant ell).re := by
  rw [positiveSurplusCubicEGFConstant_eq_ofReal, Complex.ofReal_re]
  exact positiveSurplusCubicEGFConstantReal_pos ell hell

theorem positiveSurplusCubicEGFConstant_re_nonneg (ell : ℕ) :
    0 ≤ (positiveSurplusCubicEGFConstant ell).re := by
  rw [positiveSurplusCubicEGFConstant_eq_ofReal, Complex.ofReal_re]
  exact positiveSurplusCubicEGFConstantReal_nonneg ell

theorem positiveSurplusCubicEGFConstant_ne_zero
    (ell : ℕ) (hell : 0 < ell) :
    positiveSurplusCubicEGFConstant ell ≠ 0 := by
  intro h
  have hre := positiveSurplusCubicEGFConstant_re_pos ell hell
  rw [h, Complex.zero_re] at hre
  exact (lt_irrefl 0) hre

/-! ## The Gamma-normalized physical Wright constant -/

/-- The real form of Wright's physical positive-surplus constant. -/
def positiveSurplusWrightConstantReal (ell : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi) /
      Real.Gamma (3 * (ell : ℝ) / 2)) *
    positiveSurplusCubicEGFConstantReal ell

theorem positiveSurplusWrightConstant_eq_ofReal (ell : ℕ) :
    positiveSurplusWrightConstant ell =
      (positiveSurplusWrightConstantReal ell : ℂ) := by
  rw [positiveSurplusWrightConstant_eq_transferFactor_mul_egfConstant,
    positiveSurplusCubicEGFConstant_eq_ofReal]
  unfold positiveSurplusWrightConstantReal
  push_cast
  rfl

theorem positiveSurplusWrightConstantReal_pos
    (ell : ℕ) (hell : 0 < ell) :
    0 < positiveSurplusWrightConstantReal ell := by
  have hs : 0 < 3 * (ell : ℝ) / 2 := by
    positivity
  unfold positiveSurplusWrightConstantReal
  exact mul_pos
    (div_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))
      (Real.Gamma_pos_of_pos hs))
    (positiveSurplusCubicEGFConstantReal_pos ell hell)

theorem positiveSurplusWrightConstantReal_nonneg
    (ell : ℕ) (hell : 0 < ell) :
    0 ≤ positiveSurplusWrightConstantReal ell := by
  have hs : 0 < 3 * (ell : ℝ) / 2 := by
    positivity
  unfold positiveSurplusWrightConstantReal
  exact mul_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (Real.Gamma_pos_of_pos hs).le)
    (positiveSurplusCubicEGFConstantReal_nonneg ell)

theorem positiveSurplusWrightConstant_im (ell : ℕ) :
    (positiveSurplusWrightConstant ell).im = 0 := by
  rw [positiveSurplusWrightConstant_eq_ofReal]
  exact Complex.ofReal_im _

theorem positiveSurplusWrightConstant_re_pos
    (ell : ℕ) (hell : 0 < ell) :
    0 < (positiveSurplusWrightConstant ell).re := by
  rw [positiveSurplusWrightConstant_eq_ofReal, Complex.ofReal_re]
  exact positiveSurplusWrightConstantReal_pos ell hell

theorem positiveSurplusWrightConstant_re_nonneg
    (ell : ℕ) (hell : 0 < ell) :
    0 ≤ (positiveSurplusWrightConstant ell).re := by
  rw [positiveSurplusWrightConstant_eq_ofReal, Complex.ofReal_re]
  exact positiveSurplusWrightConstantReal_nonneg ell hell

theorem positiveSurplusWrightConstant_ne_zero
    (ell : ℕ) (hell : 0 < ell) :
    positiveSurplusWrightConstant ell ≠ 0 := by
  intro h
  have hre := positiveSurplusWrightConstant_re_pos ell hell
  rw [h, Complex.zero_re] at hre
  exact (lt_irrefl 0) hre

end PerronWright.GraphCore
