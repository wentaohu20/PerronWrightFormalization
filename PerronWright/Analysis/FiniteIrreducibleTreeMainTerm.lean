import PerronWright.Analysis.FiniteIrreducibleFoldCoefficients
import PerronWright.Transfer.QuantitativeStirling

/-!
# Genuine finite irreducible tree main terms

These are algebraic conversions of the actual Perron moments; no operator
positivity beyond the literal irreducible model is required.
-/

noncomputable section

namespace PerronWright.FiniteIrreducibleTreeMainTerm

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The scale of the genuine normalized tree Taylor coefficient. -/
def treeCoefficientMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (n : ℕ) : ℝ :=
  FiniteIrreducibleFoldCoefficients.gamma M hM / (2 * Real.sqrt Real.pi) *
    (n : ℝ) ^ (-(5 / 2 : ℝ))

/-- The zero-surplus labelled main term in square-root-fold normalization. -/
def treePerronWrightMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (n : ℕ) : ℝ :=
  FiniteIrreducibleFoldCoefficients.gamma M hM / Real.sqrt 2 *
    (n : ℝ) ^ (-(2 : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n

/-- Stirling conversion preserves the exact labelled tree main term. -/
theorem factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    Transfer.factorialStirlingMainTerm n *
        treeCoefficientMainTerm M hM n =
      treePerronWrightMainTerm M hM n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hroot : Real.sqrt (2 * Real.pi * (n : ℝ)) =
      Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt (n : ℝ) := by
    rw [show 2 * Real.pi * (n : ℝ) = (2 * Real.pi) * (n : ℝ) by ring,
      Real.sqrt_mul (mul_nonneg (by norm_num) Real.pi_pos.le),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : Real.sqrt (n : ℝ) *
      (n : ℝ) ^ (-(5 / 2 : ℝ)) =
        (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnreal]
    norm_num
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold Transfer.factorialStirlingMainTerm treeCoefficientMainTerm
    treePerronWrightMainTerm
  rw [hroot]
  rw [show (Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt (n : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n *
        (FiniteIrreducibleFoldCoefficients.gamma M hM / (2 * Real.sqrt Real.pi) *
          (n : ℝ) ^ (-(5 / 2 : ℝ))) =
      (FiniteIrreducibleFoldCoefficients.gamma M hM * Real.sqrt 2 / 2) *
        (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ))) *
          ((n : ℝ) / Real.exp 1) ^ n by
        field_simp [hsqrtpi]]
  rw [hpow]
  field_simp [hsqrt2]
  rw [pow_two, hsqrt2sq]

end PerronWright.FiniteIrreducibleTreeMainTerm
