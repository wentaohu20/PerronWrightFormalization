import PerronWright.Model.FiniteIrreduciblePerronQuantities
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The genuine finite irreducible square-root coefficient, including periodic models. -/

noncomputable section

namespace PerronWright.FiniteIrreducibleFoldCoefficients

variable {S : Type*} [Fintype S] [DecidableEq S]

def gamma (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : ℝ :=
  Real.sqrt (2 / M.beta hcrit)

theorem gamma_pos (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    0 < gamma M hcrit := by
  unfold gamma
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) (M.beta_pos hcrit))

theorem gamma_sq (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    gamma M hcrit ^ 2 = 2 / M.beta hcrit := by
  unfold gamma
  exact Real.sq_sqrt (div_nonneg (by norm_num) (M.beta_pos hcrit).le)

theorem gamma_sq_mul_beta (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    gamma M hcrit ^ 2 * M.beta hcrit = 2 := by
  rw [gamma_sq, div_mul_cancel₀ _ (M.beta_pos hcrit).ne']

end PerronWright.FiniteIrreducibleFoldCoefficients
