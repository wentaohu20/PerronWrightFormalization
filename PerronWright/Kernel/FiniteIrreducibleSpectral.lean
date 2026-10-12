import PerronWright.Model.FiniteIrreducibleModel
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Actual finite Hilbert realization and literal matrix spectral bridge

The positive diagonal square-root change of coordinates conjugates
`κ diag(μ)` to the symmetric matrix `sqrt(μ) κ sqrt(μ)`.  The constructed
Euclidean operator has exactly the literal model matrix spectrum.
-/

open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

def sqrtWeight (M : FiniteIrreducibleModel S) (a : S) : ℝ := Real.sqrt (M.weight a)

theorem sqrtWeight_pos (M : FiniteIrreducibleModel S) (a : S) : 0 < M.sqrtWeight a :=
  Real.sqrt_pos.mpr (M.weight_pos a)

theorem sqrtWeight_sq (M : FiniteIrreducibleModel S) (a : S) :
    M.sqrtWeight a ^ 2 = M.weight a := Real.sq_sqrt (M.weight_pos a).le

def symmetricMatrix (M : FiniteIrreducibleModel S) : Matrix S S ℝ :=
  fun a b ↦ M.sqrtWeight a * M.kernel a b * M.sqrtWeight b

theorem symmetricMatrix_nonneg (M : FiniteIrreducibleModel S) (a b : S) :
    0 ≤ M.symmetricMatrix a b :=
  mul_nonneg (mul_nonneg (M.sqrtWeight_pos a).le (M.kernel_nonneg a b)) (M.sqrtWeight_pos b).le

theorem symmetricMatrix_pos_iff (M : FiniteIrreducibleModel S) (a b : S) :
    0 < M.symmetricMatrix a b ↔ 0 < M.kernel a b := by
  unfold symmetricMatrix
  rw [mul_pos_iff_of_pos_right (M.sqrtWeight_pos b),
    mul_pos_iff_of_pos_left (M.sqrtWeight_pos a)]

theorem symmetricMatrix_isHermitian (M : FiniteIrreducibleModel S) :
    M.symmetricMatrix.IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, symmetricMatrix]
  rw [M.symmetric b a]
  ring

def diagonalUnit (M : FiniteIrreducibleModel S) : (Matrix S S ℝ)ˣ where
  val := Matrix.diagonal M.sqrtWeight
  inv := Matrix.diagonal (fun a ↦ (M.sqrtWeight a)⁻¹)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    simp [Matrix.diagonal, Matrix.one_apply, (M.sqrtWeight_pos a).ne']
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    simp [Matrix.diagonal, Matrix.one_apply, (M.sqrtWeight_pos a).ne']

theorem symmetricMatrix_eq_conjugate (M : FiniteIrreducibleModel S) :
    M.symmetricMatrix = (↑M.diagonalUnit : Matrix S S ℝ) * M.meanMatrix *
      (↑(M.diagonalUnit⁻¹) : Matrix S S ℝ) := by
  ext a b
  change M.sqrtWeight a * M.kernel a b * M.sqrtWeight b =
    (Matrix.diagonal M.sqrtWeight * M.meanMatrix * Matrix.diagonal (fun a ↦ (M.sqrtWeight a)⁻¹)) a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, M.meanMatrix_apply, ← M.sqrtWeight_sq b]
  field_simp

theorem spectrum_symmetricMatrix (M : FiniteIrreducibleModel S) :
    spectrum ℝ M.symmetricMatrix = spectrum ℝ M.meanMatrix := by
  rw [M.symmetricMatrix_eq_conjugate, spectrum.units_conjugate]

abbrev Hilbert (_M : FiniteIrreducibleModel S) := EuclideanSpace ℝ S

def operator (M : FiniteIrreducibleModel S) : M.Hilbert →L[ℝ] M.Hilbert :=
  (Matrix.toLpLin 2 2 M.symmetricMatrix).toContinuousLinearMap

theorem operator_apply (M : FiniteIrreducibleModel S) (v : M.Hilbert) (a : S) :
    M.operator v a = ∑ b, M.symmetricMatrix a b * v b := rfl

theorem isSymmetric_operator (M : FiniteIrreducibleModel S) : M.operator.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr M.symmetricMatrix_isHermitian

theorem isCompactOperator_operator (M : FiniteIrreducibleModel S) : IsCompactOperator M.operator :=
  isCompactOperator_of_locallyCompactSpace_dom _

theorem spectrum_operator (M : FiniteIrreducibleModel S) :
    spectrum ℝ M.operator = spectrum ℝ M.meanMatrix := by
  rw [ContinuousLinearMap.spectrum_eq]
  change spectrum ℝ (Matrix.toLpLin 2 2 M.symmetricMatrix) = _
  rw [Matrix.spectrum_toLpLin, M.spectrum_symmetricMatrix]

theorem spectralRadius_operator (M : FiniteIrreducibleModel S) :
    spectralRadius ℝ M.operator = spectralRadius ℝ M.meanMatrix := by
  unfold spectralRadius
  rw [M.spectrum_operator]

theorem norm_operator_eq_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ‖M.operator‖ = 1 := by
  have he := M.spectralRadius_operator
  rw [ContinuousLinearMap.spectralRadius_eq_nnnorm M.operator M.isSymmetric_operator.isSelfAdjoint] at he
  have hn : (‖M.operator‖₊ : ENNReal) = 1 := he.trans hcrit
  have hnn : ‖M.operator‖₊ = (1 : NNReal) := by exact_mod_cast hn
  simpa using congrArg (fun x : NNReal ↦ (x : ℝ)) hnn

end PerronWright.FiniteIrreducibleModel
