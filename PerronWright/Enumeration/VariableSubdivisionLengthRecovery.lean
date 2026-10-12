import PerronWright.Enumeration.VariableSubdivisionSuppressionRecovery

/-!
# Recovering bounded-kernel subdivision lengths after suppression

Suppression replaces every nonempty chain of degree-two vertices by one
kernel edge and retains a direct branch edge when the chain is empty.  This
module records the corresponding intrinsic edge-length function and proves
that the canonical recovered edge labelling recovers the original length
profile pointwise.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The intrinsic length of the suppressed edge carrying an original
normalized kernel-edge label. -/
def BoundedKernelSubdivisionDatum.recoveredKernelEdgeLength
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) : ℕ :=
  kernelEdgeInternalLength D.reconstructedGraph
    ((D.recoveredKernelEdgeEquiv K).symm e)

/-- Suppression and canonical edge recovery preserve every entry of the
subdivision-length profile, including the zero-length direct edges. -/
theorem BoundedKernelSubdivisionDatum.recoveredKernelEdgeLength_eq
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.recoveredKernelEdgeLength K e = (D.profile.length e).val := by
  by_cases hpos : 0 < (D.profile.length e).val
  · let ep : {f : Fin K.shape.2.1.val // 0 < (D.profile.length f).val} :=
      ⟨e, hpos⟩
    have hedge : (D.recoveredKernelEdgeEquiv K).symm e =
        ((.inl (D.positiveEdgeComponent K ep)) :
          KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_positive K ep).symm
    rw [BoundedKernelSubdivisionDatum.recoveredKernelEdgeLength, hedge,
      kernelEdgeInternalLength_component, Nat.card_eq_fintype_card,
      D.positiveEdgeComponent_card K ep]
  · have hzero : (D.profile.length e).val = 0 :=
      Nat.eq_zero_of_not_pos hpos
    let ez : {f : Fin K.shape.2.1.val // (D.profile.length f).val = 0} :=
      ⟨e, hzero⟩
    have hedge : (D.recoveredKernelEdgeEquiv K).symm e =
        ((.inr (D.zeroLengthEdgeToDirectBranchEdge K ez)) :
          KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_zero K ez).symm
    rw [BoundedKernelSubdivisionDatum.recoveredKernelEdgeLength, hedge,
      kernelEdgeInternalLength_direct, hzero]

/-- In fixed kernel-edge coordinates, the intrinsic suppressed-edge lengths
determine the entire admissible subdivision-length profile.  The remaining
fields of a profile are propositions, so pointwise recovery of `length` is
the only data-level obligation. -/
theorem BoundedKernelSubdivisionDatum.profile_eq_of_recoveredKernelEdgeLength_eq
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (h : ∀ e : Fin K.shape.2.1.val,
      D.recoveredKernelEdgeLength K e =
        E.recoveredKernelEdgeLength K e) :
    D.profile = E.profile := by
  have hlength : D.profile.length = E.profile.length := by
    funext e
    apply Fin.ext
    rw [← D.recoveredKernelEdgeLength_eq K e,
      ← E.recoveredKernelEdgeLength_eq K e]
    exact h e
  cases hD : D.profile with
  | mk dlength dtotal dloop ddirect =>
      cases hE : E.profile with
      | mk elength etotal eloop edirect =>
          simp only [hD, hE] at hlength ⊢
          subst elength
          rfl

end PerronWright.GraphCore
