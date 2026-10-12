import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Literal finite irreducible type models

Only the finite positive type law and symmetric irreducible nonnegative
matrix are model data.  Criticality is the actual spectral radius of
`κ diag(μ)`.  No positive power, Perron vector, or spectral conclusion is
included, so periodic and bipartite kernels remain admissible.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace PerronWright

structure FiniteIrreducibleModel (S : Type*) [Fintype S] [DecidableEq S] where
  weight : S → ℝ
  weight_pos : ∀ a, 0 < weight a
  weight_sum : ∑ a, weight a = 1
  kernel : Matrix S S ℝ
  symmetric : ∀ a b, kernel a b = kernel b a
  irreducible : kernel.IsIrreducible

namespace FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem nonempty (M : FiniteIrreducibleModel S) : Nonempty S := by
  by_contra h
  have hi : IsEmpty S := not_nonempty_iff.mp h
  let _ := hi
  have hs := M.weight_sum
  simp at hs

theorem kernel_nonneg (M : FiniteIrreducibleModel S) (a b : S) : 0 ≤ M.kernel a b :=
  M.irreducible.nonneg a b

def meanMatrix (M : FiniteIrreducibleModel S) : Matrix S S ℝ :=
  M.kernel * Matrix.diagonal M.weight

@[simp] theorem meanMatrix_apply (M : FiniteIrreducibleModel S) (a b : S) :
    M.meanMatrix a b = M.kernel a b * M.weight b := by
  simp [meanMatrix, Matrix.mul_diagonal]

def IsCritical (M : FiniteIrreducibleModel S) : Prop :=
  spectralRadius ℝ M.meanMatrix = 1

variable [MeasurableSpace S]

def measure (M : FiniteIrreducibleModel S) : Measure S :=
  ∑ a, ENNReal.ofReal (M.weight a) • Measure.dirac a

instance measure_isProbability (M : FiniteIrreducibleModel S) :
    IsProbabilityMeasure M.measure := by
  constructor
  simp only [measure, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ (M.weight_pos a).le), M.weight_sum]
  simp

end FiniteIrreducibleModel
end PerronWright
