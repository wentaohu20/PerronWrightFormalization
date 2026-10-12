import PerronWright.Enumeration.VariableSubdivisionPositiveEndpointRecovery
import PerronWright.Enumeration.PathGraphAutomorphismRigidity

/-!
# Canonical path coordinates on recovered positive kernel edges

The existing equivalence `positiveEdgeIndexEquivComponent` already says that
the ordered internal slots on a positive kernel edge exhaust exactly one
degree-two component.  The first definition below upgrades that equivalence
to a graph isomorphism.  The remaining lemmas expose its endpoint data and
put it directly in the form required by `PathGraphAutomorphismRigidity`.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The last internal index of a positive-length normalized kernel edge. -/
def BoundedKernelSubdivisionDatum.positiveEdgeLastIndex
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Fin (D.profile.length e.1).val :=
  ⟨(D.profile.length e.1).val - 1, by omega⟩

@[simp]
theorem BoundedKernelSubdivisionDatum.positiveEdgeLastIndex_val
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    (D.positiveEdgeLastIndex K e).val =
      (D.profile.length e.1).val - 1 :=
  rfl

/-- The ordered internal labels on a positive kernel edge are canonically
isomorphic to the recovered degree-two component, with its induced graph. -/
noncomputable def BoundedKernelSubdivisionDatum.positiveEdgePathIso
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph := by
  refine { D.positiveEdgeIndexEquivComponent K e with map_rel_iff' := ?_ }
  intro i j
  change
    D.reconstructedGraph.Adj
        (D.pathLabel e.1 i) (D.pathLabel e.1 j) ↔
      (SimpleGraph.pathGraph (D.profile.length e.1).val).Adj i j
  simpa only [eq_self, true_and, SimpleGraph.pathGraph_adj] using
    (D.pathLabel_adj_iff e.1 e.1 i j)

/-- Evaluation of the canonical component coordinate in ambient labels. -/
@[simp]
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_apply_val
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (i : Fin (D.profile.length e.1).val) :
    (D.positiveEdgePathIso K e i).val.val = D.pathLabel e.1 i := by
  change (D.positiveEdgeIndexToComponent K e i).val.val = _
  rfl

/-- The zero coordinate is literally the internal endpoint in the first
boundary stub constructed in positive-endpoint recovery. -/
@[simp]
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_zero_eq_firstStub
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.positiveEdgePathIso K e
        (⟨0, e.2⟩ : Fin (D.profile.length e.1).val) =
      (D.positiveEdgeFirstBoundaryStub K e).val.1 := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The last coordinate is literally the internal endpoint in the second
boundary stub constructed in positive-endpoint recovery. -/
@[simp]
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_last_eq_lastStub
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.positiveEdgePathIso K e (D.positiveEdgeLastIndex K e) =
      (D.positiveEdgeLastBoundaryStub K e).val.1 := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The first endpoint of the canonical recovered path is adjacent to the
first canonically ordered kernel branch endpoint. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_first_adj_firstBranch
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.reconstructedGraph.Adj
      (D.positiveEdgePathIso K e
        (⟨0, e.2⟩ : Fin (D.profile.length e.1).val)).val.val
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1) := by
  rw [D.positiveEdgePathIso_apply_val]
  exact D.firstPathLabel_adj_firstBranch K e

/-- The last endpoint of the canonical recovered path is adjacent to the
second canonically ordered kernel branch endpoint. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_last_adj_secondBranch
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.reconstructedGraph.Adj
      (D.positiveEdgePathIso K e
        (D.positiveEdgeLastIndex K e)).val.val
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) := by
  rw [D.positiveEdgePathIso_apply_val]
  exact D.lastPathLabel_adj_secondBranch K e

/-- Any two graph coordinates on the same finite path component differ
pointwise by either the identity or reversal.  This is the transport wrapper
around `pathGraphIso_apply_eq_self_or_rev` needed by the fibre proof. -/
theorem boundedPathGraphCoordinates_eq_or_rev
    {W : Type*} {m : ℕ} {G : SimpleGraph W}
    (p q : SimpleGraph.pathGraph m ≃g G) :
    (∀ i, q i = p i) ∨ (∀ i, q i = p i.rev) := by
  let a : SimpleGraph.pathGraph m ≃g SimpleGraph.pathGraph m :=
    q.trans p.symm
  rcases pathGraphIso_toEquiv_eq_refl_or_rev a with h | h
  · left
    intro i
    have hi : a i = i :=
      congrArg (fun f : Fin m ≃ Fin m => f i) h
    apply p.symm.injective
    change p.symm (q i) = p.symm (p i)
    rw [p.symm_apply_apply]
    exact hi
  · right
    intro i
    have hi : a i = i.rev :=
      congrArg (fun f : Fin m ≃ Fin m => f i) h
    apply p.symm.injective
    change p.symm (q i) = p.symm (p i.rev)
    rw [p.symm_apply_apply]
    exact hi

/-- If the first coordinate is fixed, the reversal alternative disappears.
The positivity assumption merely excludes the empty path. -/
theorem boundedPathGraphCoordinates_eq_of_apply_zero_eq
    {W : Type*} {m : ℕ} {G : SimpleGraph W}
    (hm : 0 < m)
    (p q : SimpleGraph.pathGraph m ≃g G)
    (hzero : q (⟨0, hm⟩ : Fin m) = p ⟨0, hm⟩) :
    ∀ i, q i = p i := by
  cases m with
  | zero => omega
  | succ n =>
      let a : SimpleGraph.pathGraph (n + 1) ≃g
          SimpleGraph.pathGraph (n + 1) := q.trans p.symm
      have hzero' : q (0 : Fin (n + 1)) = p 0 := by
        simpa using hzero
      have ha0 : a 0 = 0 := by
        change p.symm (q 0) = 0
        rw [hzero', p.symm_apply_apply]
      have hfix :=
        pathGraphIso_apply_eq_self_of_apply_zero_eq_zero a ha0
      intro i
      apply p.symm.injective
      change p.symm (q i) = p.symm (p i)
      rw [p.symm_apply_apply]
      exact hfix i

/-- Specialized rigidity interface for a recovered positive edge. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_compare
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (q : SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph) :
    (∀ i, q i = D.positiveEdgePathIso K e i) ∨
      (∀ i, q i = D.positiveEdgePathIso K e i.rev) :=
  boundedPathGraphCoordinates_eq_or_rev (D.positiveEdgePathIso K e) q

/-- If a second coordinate has the same first boundary vertex, it equals the
canonical recovered coordinate pointwise.  This is the non-loop uniqueness
interface once equality of the first boundary stub has been established. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_eq_of_same_first
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (q : SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph)
    (hfirst : q ⟨0, e.2⟩ = D.positiveEdgePathIso K e ⟨0, e.2⟩) :
    ∀ i, q i = D.positiveEdgePathIso K e i :=
  boundedPathGraphCoordinates_eq_of_apply_zero_eq e.2
    (D.positiveEdgePathIso K e) q hfirst

end PerronWright.GraphCore
