import PerronWright.Kernel.FiniteIrreduciblePerron
import PerronWright.Analysis.SpectralGap

/-!
# Reduced resolvent for the general irreducible finite branch

The complement need not have norm below one: bipartite kernels may have
eigenvalue `-1`.  Nevertheless `I-K` on the fixed-space orthogonal
complement is genuinely invertible.  Finite dimension and absence of the
eigenvalue `+1` there suffice, with no primitivity hypothesis.
-/

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem fixedComplement_one_sub_isUnit (M : FiniteIrreducibleModel S) :
    IsUnit (1 - PerronWright.fixedComplementOperator M.operator M.isSymmetric_operator) := by
  let T := PerronWright.fixedComplementOperator M.operator M.isSymmetric_operator
  let A : PerronWright.fixedComplement M.operator →L[ℝ] PerronWright.fixedComplement M.operator := 1 - T
  have hno : ¬ Module.End.HasEigenvalue T.toLinearMap 1 :=
    PerronWright.fixedComplementOperator_no_one M.operator M.isSymmetric_operator
  have hi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hfix : T v = v := by
      have he : (1 - T) v = 0 := hv
      simp only [sub_apply, one_apply_eq_self] at he
      exact (sub_eq_zero.mp he).symm
    by_contra hvne
    apply hno
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨
      Module.End.mem_eigenspace_iff.mpr (by simpa using hfix), hvne⟩
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end PerronWright.FiniteIrreducibleModel
