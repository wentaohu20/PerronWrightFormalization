import PerronWright.Enumeration.CubicFixedCoordinateFibre

/-!
# Converse after recovered kernel coordinates have been fixed

The reconstructed simple graph cannot by itself distinguish parallel edges
of the suppressed cubic kernel.  The natural global inverse statement must
therefore first choose the recovered kernel-edge coordinates.  This file
proves that, after those coordinates and the branch coordinates are fixed,
the fibre is exactly the Boolean loop-orientation orbit.

The hypothesis `q` gives, for every positive-length normalized kernel edge,
the path coordinate read from a second subdivision labelling, but expressed
in the recovered degree-two component of the first datum.  Non-loop paths
are anchored at their first boundary coordinate.  Path rigidity then forces
identity on non-loops and identity-or-reversal on loops; the fixed-coordinate
assembly theorem packages the latter choices into one unique finite loop set.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Once recovered branch and edge-component coordinates agree, two
subdivision labellings differ by a unique simultaneous reversal set of loop
edges.  This is the complete converse on one fixed recovered-coordinate
fibre, including kernels with parallel edges. -/
theorem existsUnique_reverseLoops_eq_of_recovered_coordinates
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (labels' : CubicKernelSubdivisionSlot D.profile ≃ Fin k)
    (hbranch : ∀ v : Fin (2 * ell),
      labels' (.inl v) = D.labels (.inl v))
    (q : ∀ e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val},
      SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
        (D.positiveEdgeComponent K e).toSimpleGraph)
    (hq : ∀
      (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
      (i : Fin (D.profile.length e.1).val),
      (q e i).val.val = labels' (.inr ⟨e.1, i⟩))
    (hfirst : ∀
      (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}),
      ¬(K.graph.endpoints e.1).IsDiag →
        q e ⟨0, e.2⟩ = D.positiveEdgePathIso K e ⟨0, e.2⟩) :
    ∃! A : Finset (CubicKernelLoopEdge K.graph),
      D.reverseLoops A =
        (⟨D.profile, labels'⟩ : CubicKernelSubdivisionDatum k ell K.graph) := by
  have hnonloop : ∀ (f : Fin (3 * ell)),
      ¬(K.graph.endpoints f).IsDiag →
        ∀ i : Fin (D.profile.length f).val,
          labels' (.inr ⟨f, i⟩) = D.labels (.inr ⟨f, i⟩) := by
    intro f hf i
    have hpos : 0 < (D.profile.length f).val :=
      Nat.zero_lt_of_lt i.isLt
    let e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val} :=
      ⟨f, hpos⟩
    have hcoordinate : ∀ j,
        q e j = D.positiveEdgePathIso K e j :=
      D.positiveEdgePathIso_compare_anchored K e (q e) (hfirst e hf)
    calc
      labels' (.inr ⟨f, i⟩) = (q e i).val.val := (hq e i).symm
      _ = (D.positiveEdgePathIso K e i).val.val :=
        congrArg (fun x => x.val.val) (hcoordinate i)
      _ = D.pathLabel f i := D.positiveEdgePathIso_apply_val K e i
      _ = D.labels (.inr ⟨f, i⟩) := rfl
  have hloop : ∀ e : CubicKernelLoopEdge K.graph,
      (∀ i : Fin (D.profile.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) = D.labels (.inr ⟨e.1, i⟩)) ∨
      (∀ i : Fin (D.profile.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) =
          D.labels (.inr ⟨e.1, Fin.rev i⟩)) := by
    intro e
    have hpos : 0 < (D.profile.length e.1).val :=
      lt_of_lt_of_le (by omega) (D.profile.loopLength e.1 e.2)
    let ep : {f : Fin (3 * ell) // 0 < (D.profile.length f).val} :=
      ⟨e.1, hpos⟩
    rcases D.positiveEdgePathIso_compare K ep (q ep) with hsame | hrev
    · left
      intro i
      calc
        labels' (.inr ⟨e.1, i⟩) = (q ep i).val.val := (hq ep i).symm
        _ = (D.positiveEdgePathIso K ep i).val.val :=
          congrArg (fun x => x.val.val) (hsame i)
        _ = D.pathLabel e.1 i :=
          D.positiveEdgePathIso_apply_val K ep i
        _ = D.labels (.inr ⟨e.1, i⟩) := rfl
    · right
      intro i
      calc
        labels' (.inr ⟨e.1, i⟩) = (q ep i).val.val := (hq ep i).symm
        _ = (D.positiveEdgePathIso K ep i.rev).val.val :=
          congrArg (fun x => x.val.val) (hrev i)
        _ = D.pathLabel e.1 i.rev :=
          D.positiveEdgePathIso_apply_val K ep i.rev
        _ = D.labels (.inr ⟨e.1, Fin.rev i⟩) := rfl
  obtain ⟨A, hA⟩ := exists_reverseLoops_eq_of_fixed_coordinates
    D.profile D.labels labels' hbranch hnonloop hloop
  refine ⟨A, hA, ?_⟩
  intro B hB
  apply D.reverseLoops_injective
  exact hB.trans hA.symm

/-- Existence-only projection of the recovered-coordinate converse. -/
theorem exists_reverseLoops_eq_of_recovered_coordinates
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (labels' : CubicKernelSubdivisionSlot D.profile ≃ Fin k)
    (hbranch : ∀ v : Fin (2 * ell),
      labels' (.inl v) = D.labels (.inl v))
    (q : ∀ e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val},
      SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
        (D.positiveEdgeComponent K e).toSimpleGraph)
    (hq : ∀
      (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
      (i : Fin (D.profile.length e.1).val),
      (q e i).val.val = labels' (.inr ⟨e.1, i⟩))
    (hfirst : ∀
      (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}),
      ¬(K.graph.endpoints e.1).IsDiag →
        q e ⟨0, e.2⟩ = D.positiveEdgePathIso K e ⟨0, e.2⟩) :
    ∃ A : Finset (CubicKernelLoopEdge K.graph),
      D.reverseLoops A =
        (⟨D.profile, labels'⟩ : CubicKernelSubdivisionDatum k ell K.graph) := by
  exact (existsUnique_reverseLoops_eq_of_recovered_coordinates
    K D labels' hbranch q hq hfirst).exists

end PerronWright.GraphCore
