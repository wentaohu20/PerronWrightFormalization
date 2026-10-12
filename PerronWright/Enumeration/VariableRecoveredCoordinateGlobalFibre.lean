import PerronWright.Enumeration.VariableGlobalRecoveredCoordinateAlignment

/-!
# The recovered-coordinate fibre for variable bounded kernels

After branch and intrinsic suppressed-edge coordinates have been fixed, the
only remaining freedom in a subdivision datum is reversal of the internal
coordinate on loop edges.  This file transports the target's positive-edge
path coordinates into the source components, anchors every non-loop at its
first boundary endpoint, and packages the residual loop choices into one
unique finite loop set.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Equality-transported degree-two components have canonically isomorphic
induced component graphs. -/
noncomputable def variableDegreeTwoComponentGraphIsoOfGraphEq
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (C : (twoGraph G).ConnectedComponent)
    (C' : (twoGraph H).ConnectedComponent)
    (hC : variableDegreeTwoComponentEquivOfGraphEq h C = C') :
    C.toSimpleGraph ≃g C'.toSimpleGraph := by
  subst H
  change C = C' at hC
  subst C'
  exact SimpleGraph.Iso.refl

@[simp] theorem variableDegreeTwoComponentGraphIsoOfGraphEq_symm_apply_val
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (C : (twoGraph G).ConnectedComponent)
    (C' : (twoGraph H).ConnectedComponent)
    (hC : variableDegreeTwoComponentEquivOfGraphEq h C = C')
    (x : C') :
    (((variableDegreeTwoComponentGraphIsoOfGraphEq h C C' hC).symm x).val.val) =
      x.val.val := by
  subst H
  change C = C' at hC
  subst C'
  rfl

/-- Equality of path lengths gives the evident isomorphism of standard
finite path graphs. -/
def variablePathGraphIsoCongr {m n : ℕ} (h : m = n) :
    SimpleGraph.pathGraph m ≃g SimpleGraph.pathGraph n where
  toEquiv := finCongr h
  map_rel_iff' := by
    intro i j
    simp only [SimpleGraph.pathGraph_adj, finCongr_apply_coe]

/-- The recovered internal-coordinate equivalence, promoted to a standard
path-graph isomorphism. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredPathIndexGraphIso
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val) :
    SimpleGraph.pathGraph (D.profile.length e).val ≃g
      SimpleGraph.pathGraph
        (E.profile.length
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
  if _hloop :
      ((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag then
    variablePathGraphIsoCongr
      (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else if _hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints K.shape
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1 then
    variablePathGraphIsoCongr
      (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else
    (pathGraphRevIso (D.profile.length e).val).trans
      (variablePathGraphIsoCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e))

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredPathIndexGraphIso_toEquiv
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val) :
    (D.recoveredPathIndexGraphIso K E hG e).toEquiv =
      D.recoveredPathIndexEquiv K E hG e := by
  unfold BoundedKernelSubdivisionDatum.recoveredPathIndexGraphIso
    BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv
    variablePathGraphIsoCongr pathGraphRevIso
  split_ifs <;> rfl

/-- A positive edge transported to the corresponding recovered edge of the
second datum. -/
noncomputable abbrev BoundedKernelSubdivisionDatum.recoveredPositiveEdge
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    {f : Fin K.shape.2.1.val // 0 < (E.profile.length f).val} := by
  refine ⟨D.recoveredKernelEdgeCoordinatePerm K E hG e.1, ?_⟩
  rw [← D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e.1]
  exact e.2

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredPositiveEdge_val
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    (D.recoveredPositiveEdge K E hG e).1 =
      D.recoveredKernelEdgeCoordinatePerm K E hG e.1 :=
  rfl

/-- Intrinsic edge transport identifies the corresponding positive
degree-two components. -/
theorem BoundedKernelSubdivisionDatum.recoveredPositiveEdgeComponent_eq
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    variableDegreeTwoComponentEquivOfGraphEq hG
        (D.positiveEdgeComponent K e) =
      E.positiveEdgeComponent K (D.recoveredPositiveEdge K E hG e) := by
  have hD :
      (D.recoveredKernelEdgeEquiv K).symm e.1 =
        (.inl (D.positiveEdgeComponent K e) :
          KernelEdgeLabel D.reconstructedGraph) := by
    apply (D.recoveredKernelEdgeEquiv K).injective
    rw [Equiv.apply_symm_apply]
    exact (D.recoveredKernelEdgeEquiv_positive K e).symm
  have hE :
      (E.recoveredKernelEdgeEquiv K).symm
          (D.recoveredKernelEdgeCoordinatePerm K E hG e.1) =
        (.inl (E.positiveEdgeComponent K
          (D.recoveredPositiveEdge K E hG e)) :
          KernelEdgeLabel E.reconstructedGraph) := by
    apply (E.recoveredKernelEdgeEquiv K).injective
    rw [Equiv.apply_symm_apply]
    exact (E.recoveredKernelEdgeEquiv_positive K
      (D.recoveredPositiveEdge K E hG e)).symm
  apply Sum.inl.inj
  rw [← variableKernelEdgeLabelEquivOfGraphEq_inl hG, ← hD, ← hE]
  exact D.recoveredKernelEdgeCoordinatePerm_intrinsic K E hG e.1

/-- The aligned positive components as induced simple graphs. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredPositiveEdgeComponentIso
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    (D.positiveEdgeComponent K e).toSimpleGraph ≃g
      (E.positiveEdgeComponent K
        (D.recoveredPositiveEdge K E hG e)).toSimpleGraph :=
  variableDegreeTwoComponentGraphIsoOfGraphEq hG
    (D.positiveEdgeComponent K e)
    (E.positiveEdgeComponent K (D.recoveredPositiveEdge K E hG e))
    (D.recoveredPositiveEdgeComponent_eq K E hG e)

/-- The target's recovered path coordinate, transported back into the
source's intrinsic positive component. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph :=
  (D.recoveredPathIndexGraphIso K E hG e.1).trans
    ((E.positiveEdgePathIso K (D.recoveredPositiveEdge K E hG e)).trans
      (D.recoveredPositiveEdgeComponentIso K E hG e).symm)

theorem BoundedKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso_apply_val
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (i : Fin (D.profile.length e.1).val) :
    (D.recoveredAlignedPositiveEdgePathIso K E hG e i).val.val =
      D.recoveredCoordinateAlignedLabels K E hG
        ((.inr ⟨e.1, i⟩) : BoundedKernelSubdivisionSlot D.profile) := by
  rw [D.recoveredCoordinateAlignedLabels_path K E hG]
  rw [BoundedKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso,
    BoundedKernelSubdivisionDatum.recoveredPositiveEdgeComponentIso,
    RelIso.trans_apply, RelIso.trans_apply,
    variableDegreeTwoComponentGraphIsoOfGraphEq_symm_apply_val,
    E.positiveEdgePathIso_apply_val]
  rw [← D.recoveredPathIndexGraphIso_toEquiv K E hG e.1]
  rfl

/-- In a non-loop component, adjacency to the first ordered branch endpoint
selects the first canonical path coordinate. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgeComponent_eq_first_of_adj
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (hnonloop :
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints e.1).IsDiag)
    (x : D.positiveEdgeComponent K e)
    (hx : D.reconstructedGraph.Adj x.val.val
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1)) :
    x = D.positiveEdgePathIso K e ⟨0, e.2⟩ := by
  let qL := D.positiveEdgeFirstBoundaryStub K e
  let qR := D.positiveEdgeLastBoundaryStub K e
  let q : Σ _x : D.positiveEdgeComponent K e, Fin k :=
    ⟨x, D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1⟩
  have hq : q ∈ componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e) := by
    simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
      true_and, Finset.mem_filter,
      D.reconstructedGraph.mem_neighborFinset]
    refine ⟨hx, ?_⟩
    rw [D.branchVertex_degree_eq_kernelDegree]
    have hmin := K.minDegree
      (boundedKernelOrderedEndpoints K.shape e.1).1
    omega
  have hval : qL.val ≠ qR.val := by
    intro h
    exact D.positiveEdgeBoundaryStubs_ne K e (Subtype.ext h)
  have hpair : componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e) = {qL.val, qR.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact qL.property
      · exact qR.property
    · rw [Finset.card_pair hval,
        componentBoundaryStubs_card_eq_two D.reconstructedGraph hacyc
          (D.positiveEdgeComponent K e)]
  have hqpair : q = qL.val ∨ q = qR.val := by
    have hmem := hq
    rw [hpair] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hqpair with hfirst | hlast
  · have hxfirst : x = qL.val.1 := congrArg Sigma.fst hfirst
    rw [D.positiveEdgePathIso_zero_eq_firstStub K e]
    exact hxfirst
  · exfalso
    have hbranch :
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1 =
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2 :=
      congrArg Sigma.snd hlast
    have hordered :
        (boundedKernelOrderedEndpoints K.shape e.1).1 =
          (boundedKernelOrderedEndpoints K.shape e.1).2 := by
      change D.labels (.inl _) = D.labels (.inl _) at hbranch
      exact Sum.inl.inj (D.labels.injective hbranch)
    exact hnonloop
      ((boundedKernelOrderedEndpoints_eq_iff_isDiag K e.1).1 hordered)

/-- On a non-loop, the transported recovered coordinate starts at the first
canonical vertex. -/
theorem BoundedKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso_first
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin K.toLabelledBoundedKernel.shape.2.1.val //
      0 < (D.profile.length e).val})
    (hnonloop : ¬((boundedKernelFiniteMultiGraph
      K.toLabelledBoundedKernel.shape).endpoints e.1).IsDiag) :
    D.recoveredAlignedPositiveEdgePathIso
        K.toLabelledBoundedKernel E hG e ⟨0, e.2⟩ =
      D.positiveEdgePathIso K.toLabelledBoundedKernel e ⟨0, e.2⟩ := by
  let K0 := K.toLabelledBoundedKernel
  apply D.positiveEdgeComponent_eq_first_of_adj K0
    (D.reconstructedTwoGraph_isAcyclic K0 K.connected hell)
    e hnonloop
  let f := D.recoveredPositiveEdge K0 E hG e
  let oD := boundedKernelOrderedEndpoints K0.shape e.1
  let oE := boundedKernelOrderedEndpoints K0.shape f.1
  have hAdjTransport (a b : Fin k) :
      D.reconstructedGraph.Adj a b ↔ E.reconstructedGraph.Adj a b := by
    rw [hG]
  by_cases hfirst :
      D.recoveredBranchCoordinatePerm K0 E hG oD.1 = oE.1
  · have hindex :
        D.recoveredPathIndexEquiv K0 E hG e.1 ⟨0, e.2⟩ =
          (⟨0, f.2⟩ : Fin (E.profile.length f.1).val) := by
      rw [D.recoveredPathIndexEquiv_of_nonloop_direct
        K0 E hG e.1 hnonloop hfirst]
      apply Fin.ext
      rfl
    have hadj := E.firstPathLabel_adj_firstBranch K0 f
    apply (hAdjTransport _ _).2
    rw [D.recoveredAlignedPositiveEdgePathIso_apply_val K0 E hG e]
    rw [D.recoveredCoordinateAlignedLabels_path K0 E hG, hindex]
    rw [← D.branchLabel_recoveredBranchCoordinatePerm K0 E hG oD.1,
      hfirst]
    exact hadj
  · have hreversed :=
      D.orderedEndpoints_reversed_of_first_ne hell K E hG e.1 hfirst
    have hindex :
        D.recoveredPathIndexEquiv K0 E hG e.1 ⟨0, e.2⟩ =
          E.positiveEdgeLastIndex K0 f := by
      rw [D.recoveredPathIndexEquiv_of_nonloop_reversed
        K0 E hG e.1 hnonloop hfirst]
      apply Fin.ext
      have hlen : (D.profile.length e.1).val =
          (E.profile.length f.1).val := by
        simpa only [f, BoundedKernelSubdivisionDatum.recoveredPositiveEdge]
          using D.profile_length_recoveredKernelEdgeCoordinatePerm
            K0 E hG e.1
      calc
        (((Fin.revPerm : Equiv.Perm
              (Fin (D.profile.length e.1).val)).trans
            (finCongr
              (D.profile_length_recoveredKernelEdgeCoordinatePerm
                K0 E hG e.1))) ⟨0, e.2⟩).val =
            (D.profile.length e.1).val - 1 := by
          simp only [Equiv.trans_apply, finCongr_apply_coe,
            Fin.revPerm_apply, Fin.val_rev]
        _ = (E.profile.length f.1).val - 1 :=
          congrArg (fun n : ℕ ↦ n - 1) hlen
        _ = (E.positiveEdgeLastIndex K0 f).val :=
          (E.positiveEdgeLastIndex_val K0 f).symm
    have hadj := E.positiveEdgePathIso_last_adj_secondBranch K0 f
    apply (hAdjTransport _ _).2
    rw [D.recoveredAlignedPositiveEdgePathIso_apply_val K0 E hG e]
    rw [D.recoveredCoordinateAlignedLabels_path K0 E hG, hindex]
    rw [← D.branchLabel_recoveredBranchCoordinatePerm K0 E hG oD.1,
      hreversed.1]
    simpa only [E.positiveEdgePathIso_apply_val, f, K0,
      BoundedKernelSubdivisionDatum.recoveredPositiveEdge] using hadj

/-- Once recovered branch and edge-component coordinates agree, two
subdivision labellings differ by a unique simultaneous reversal set of loop
edges. -/
theorem existsUnique_reverseLoops_eq_of_variable_recovered_coordinates
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (labels' : BoundedKernelSubdivisionSlot D.profile ≃ Fin k)
    (hbranch : ∀ v : Fin K.shape.1.val,
      labels' (.inl v) = D.labels (.inl v))
    (q : ∀ e : {e : Fin K.shape.2.1.val //
      0 < (D.profile.length e).val},
      SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
        (D.positiveEdgeComponent K e).toSimpleGraph)
    (hq : ∀
      (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
      (i : Fin (D.profile.length e.1).val),
      (q e i).val.val = labels' (.inr ⟨e.1, i⟩))
    (hfirst : ∀
      (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}),
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints e.1).IsDiag →
        q e ⟨0, e.2⟩ = D.positiveEdgePathIso K e ⟨0, e.2⟩) :
    ∃! A : Finset (BoundedKernelLoopEdge K),
      D.reverseLoops A =
        (⟨D.profile, labels'⟩ : BoundedKernelSubdivisionDatum k K) := by
  have hnonloop : ∀ (f : Fin K.shape.2.1.val),
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag →
        ∀ i : Fin (D.profile.length f).val,
          labels' (.inr ⟨f, i⟩) = D.labels (.inr ⟨f, i⟩) := by
    intro f hf i
    have hpos : 0 < (D.profile.length f).val :=
      Nat.zero_lt_of_lt i.isLt
    let e : {e : Fin K.shape.2.1.val //
      0 < (D.profile.length e).val} := ⟨f, hpos⟩
    have hcoordinate : ∀ j,
        q e j = D.positiveEdgePathIso K e j :=
      D.positiveEdgePathIso_compare_anchored K e (q e) (hfirst e hf)
    calc
      labels' (.inr ⟨f, i⟩) = (q e i).val.val := (hq e i).symm
      _ = (D.positiveEdgePathIso K e i).val.val :=
        congrArg (fun x ↦ x.val.val) (hcoordinate i)
      _ = D.pathLabel f i := D.positiveEdgePathIso_apply_val K e i
      _ = D.labels (.inr ⟨f, i⟩) := rfl
  have hloop : ∀ e : BoundedKernelLoopEdge K,
      (∀ i : Fin (D.profile.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) = D.labels (.inr ⟨e.1, i⟩)) ∨
      (∀ i : Fin (D.profile.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) =
          D.labels (.inr ⟨e.1, Fin.rev i⟩)) := by
    intro e
    have hpos : 0 < (D.profile.length e.1).val :=
      lt_of_lt_of_le (by omega) (D.profile.loopLength e.1 e.2)
    let ep : {f : Fin K.shape.2.1.val //
      0 < (D.profile.length f).val} := ⟨e.1, hpos⟩
    rcases D.positiveEdgePathIso_compare K ep (q ep) with hsame | hrev
    · left
      intro i
      calc
        labels' (.inr ⟨e.1, i⟩) = (q ep i).val.val := (hq ep i).symm
        _ = (D.positiveEdgePathIso K ep i).val.val :=
          congrArg (fun x ↦ x.val.val) (hsame i)
        _ = D.pathLabel e.1 i := D.positiveEdgePathIso_apply_val K ep i
        _ = D.labels (.inr ⟨e.1, i⟩) := rfl
    · right
      intro i
      calc
        labels' (.inr ⟨e.1, i⟩) = (q ep i).val.val := (hq ep i).symm
        _ = (D.positiveEdgePathIso K ep i.rev).val.val :=
          congrArg (fun x ↦ x.val.val) (hrev i)
        _ = D.pathLabel e.1 i.rev :=
          D.positiveEdgePathIso_apply_val K ep i.rev
        _ = D.labels (.inr ⟨e.1, Fin.rev i⟩) := rfl
  obtain ⟨A, hA⟩ := exists_boundedKernel_reverseLoops_eq_of_fixed_coordinates
    D.profile D.labels labels' hbranch hnonloop hloop
  refine ⟨A, hA, ?_⟩
  intro B hB
  apply D.reverseLoops_injective
  exact hB.trans hA.symm

/-- After recovered branch, edge, and path alignment, the fixed-kernel fibre
is one unique loop-reversal orbit. -/
theorem BoundedKernelSubdivisionDatum.existsUnique_reverseLoops_eq_alignedDatum
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    ∃! A : Finset (BoundedKernelLoopEdge K.toLabelledBoundedKernel),
      D.reverseLoops A =
        D.recoveredCoordinateAlignedDatum
          K.toLabelledBoundedKernel E hG := by
  exact existsUnique_reverseLoops_eq_of_variable_recovered_coordinates
    K.toLabelledBoundedKernel D
    (D.recoveredCoordinateAlignedLabels K.toLabelledBoundedKernel E hG)
    (D.recoveredCoordinateAlignedLabels_branch
      K.toLabelledBoundedKernel E hG)
    (D.recoveredAlignedPositiveEdgePathIso
      K.toLabelledBoundedKernel E hG)
    (D.recoveredAlignedPositiveEdgePathIso_apply_val
      K.toLabelledBoundedKernel E hG)
    (D.recoveredAlignedPositiveEdgePathIso_first hell K E hG)

namespace BoundedKernelPresentation

/-- The target presentation differs from the globally aligned cast source by
one unique set of loop reversals. -/
theorem existsUnique_reverseLoops_globalRecoveredAlignedCastDatum_eq_target
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    ∃! A : Finset
        (BoundedKernelLoopEdge Q.1.toLabelledBoundedKernel),
      (P.globalRecoveredAlignedCastDatum hell Q hG).reverseLoops A = Q.2 := by
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  have haligned :=
    P.globalRecoveredAlignedCastDatum_recoveredCoordinateAlignedDatum
      hell Q hG
  obtain ⟨A, hA, hunique⟩ :=
    D.existsUnique_reverseLoops_eq_alignedDatum hell Q.1 Q.2 hDQ
  refine ⟨A, hA.trans haligned, ?_⟩
  intro B hB
  apply hunique B
  exact hB.trans haligned.symm

end BoundedKernelPresentation

end PerronWright.GraphCore
