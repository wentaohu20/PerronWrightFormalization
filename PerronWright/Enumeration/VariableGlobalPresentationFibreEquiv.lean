import PerronWright.Enumeration.VariableRecoveredCoordinateGlobalFibre

/-!
# Exact global bounded-kernel presentation fibres

For positive surplus and a chosen base presentation, simultaneous branch and
edge coordinate permutations together with independent loop reversals give
every bounded-kernel presentation of the same labelled reconstructed graph
exactly once.  The resulting equivalence proves the exact variable-kernel
coordinate-multiplicity factor without an additional counting interface.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A datum and its transport across equality of bounded-kernel indices are
heterogeneously equal. -/
theorem boundedKernelSubdivisionDatumCast_heq
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K) :
    HEq D (boundedKernelSubdivisionDatumCast h D) := by
  subst L
  rfl

/-- Casting a datum and its loop set commutes with simultaneous loop
reversal. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_cast_heq
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    HEq (D.reverseLoops A)
      ((boundedKernelSubdivisionDatumCast h D).reverseLoops
        (boundedKernelLoopSetCast h A)) := by
  subst L
  rfl

/-- Loop reversal leaves every non-loop path label unchanged. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_pathLabel_nonloop
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : Fin K.shape.2.1.val)
    (he : ¬((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag)
    (i : Fin (D.profile.length e).val) :
    (D.reverseLoops A).pathLabel e i = D.pathLabel e i := by
  change D.labels
      (boundedKernelLoopOrientationSetSlotEquiv
        D.profile A (.inr ⟨e, i⟩)) = D.labels (.inr ⟨e, i⟩)
  rw [boundedKernelLoopOrientationSetSlotEquiv_nonloop
    D.profile A e he]

/-- Loop reversal preserves each actual positive degree-two component. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_positiveEdgeComponent
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    variableDegreeTwoComponentEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        ((D.reverseLoops A).positiveEdgeComponent K e) =
      D.positiveEdgeComponent K e := by
  let i : Fin (D.profile.length e.1).val := ⟨0, e.2⟩
  unfold BoundedKernelSubdivisionDatum.positiveEdgeComponent
  by_cases hloop :
      ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1).IsDiag
  · let a : BoundedKernelLoopEdge K := ⟨e.1, hloop⟩
    by_cases ha : a ∈ A
    · let j : Fin (D.profile.length e.1).val := Fin.rev i
      calc
        variableDegreeTwoComponentEquivOfGraphEq
            (D.reverseLoops_reconstructedGraph A)
            ((twoGraph (D.reverseLoops A).reconstructedGraph).connectedComponentMk
              ⟨(D.reverseLoops A).pathLabel e.1 i,
                (D.reverseLoops A).internalVertex_degree_eq_two e.1 i⟩) =
            (twoGraph D.reconstructedGraph).connectedComponentMk
              ⟨D.pathLabel e.1 j,
                D.internalVertex_degree_eq_two e.1 j⟩ := by
          apply variableDegreeTwoComponentEquivOfGraphEq_connectedComponentMk
          exact D.reverseLoops_pathLabel_mem A a ha i
        _ = (twoGraph D.reconstructedGraph).connectedComponentMk
              ⟨D.pathLabel e.1 i,
                D.internalVertex_degree_eq_two e.1 i⟩ := by
          apply SimpleGraph.ConnectedComponent.eq.mpr
          exact D.internalPath_reachable_twoGraph K e.1 j i
    · apply variableDegreeTwoComponentEquivOfGraphEq_connectedComponentMk
      exact D.reverseLoops_pathLabel_not_mem A a ha i
  · apply variableDegreeTwoComponentEquivOfGraphEq_connectedComponentMk
    exact D.reverseLoops_pathLabel_nonloop A e.1 hloop i

theorem BoundedKernelSubdivisionDatum.reverseLoops_zeroLengthEdge_val
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0}) :
    ((D.reverseLoops A).zeroLengthEdgeToDirectBranchEdge K e).1 =
      (D.zeroLengthEdgeToDirectBranchEdge K e).1 := by
  change (D.reverseLoops A).subdivisionEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot (D.reverseLoops A)) =
    D.subdivisionEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D)
  calc
    (D.reverseLoops A).subdivisionEdge
        (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
          BoundedKernelSubdivisionEdgeSlot (D.reverseLoops A)) =
        s((D.reverseLoops A).branchLabel
            (boundedKernelOrderedEndpoints K.shape e.1).1,
          (D.reverseLoops A).branchLabel
            (boundedKernelOrderedEndpoints K.shape e.1).2) :=
      (D.reverseLoops A).subdivisionEdge_direct e.1 e.2
    _ = s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1,
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) := by
      simp only [BoundedKernelSubdivisionDatum.reverseLoops_branchLabel]
    _ = D.subdivisionEdge
        (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
          BoundedKernelSubdivisionEdgeSlot D) :=
      (D.subdivisionEdge_direct e.1 e.2).symm

/-- The full intrinsic recovered edge is invariant under simultaneous loop
reversal. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_recoveredKernelEdgeEquiv_symm
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : Fin K.shape.2.1.val) :
    variableKernelEdgeLabelEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        (((D.reverseLoops A).recoveredKernelEdgeEquiv K).symm e) =
      (D.recoveredKernelEdgeEquiv K).symm e := by
  by_cases hpos : 0 < (D.profile.length e).val
  · let ep : {f : Fin K.shape.2.1.val //
        0 < (D.profile.length f).val} := ⟨e, hpos⟩
    have hsource :
        (D.recoveredKernelEdgeEquiv K).symm e =
          (.inl (D.positiveEdgeComponent K ep) :
            KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_positive K ep).symm
    have htarget :
        ((D.reverseLoops A).recoveredKernelEdgeEquiv K).symm e =
          (.inl ((D.reverseLoops A).positiveEdgeComponent K ep) :
            KernelEdgeLabel (D.reverseLoops A).reconstructedGraph) := by
      apply ((D.reverseLoops A).recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact ((D.reverseLoops A).recoveredKernelEdgeEquiv_positive K ep).symm
    rw [htarget, hsource, variableKernelEdgeLabelEquivOfGraphEq_inl,
      D.reverseLoops_positiveEdgeComponent K A ep]
  · have hzero : (D.profile.length e).val = 0 :=
      Nat.eq_zero_of_not_pos hpos
    let ez : {f : Fin K.shape.2.1.val //
        (D.profile.length f).val = 0} := ⟨e, hzero⟩
    have hsource :
        (D.recoveredKernelEdgeEquiv K).symm e =
          (.inr (D.zeroLengthEdgeToDirectBranchEdge K ez) :
            KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_zero K ez).symm
    have htarget :
        ((D.reverseLoops A).recoveredKernelEdgeEquiv K).symm e =
          (.inr ((D.reverseLoops A).zeroLengthEdgeToDirectBranchEdge K ez) :
            KernelEdgeLabel (D.reverseLoops A).reconstructedGraph) := by
      apply ((D.reverseLoops A).recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact ((D.reverseLoops A).recoveredKernelEdgeEquiv_zero K ez).symm
    rw [htarget, hsource]
    apply variableKernelEdgeLabelEquivOfGraphEq_inr_eq
    exact D.reverseLoops_zeroLengthEdge_val K A ez

namespace BoundedKernelPresentation

/-- Reading a transported branch coordinate after applying a variable-kernel
symmetry returns the original branch label. -/
theorem applySymmetry_branchLabel
    {k ell : ℕ}
    (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel)
    (v : Fin P.1.toLabelledBoundedKernel.shape.1.val) :
    (P.applySymmetry c).2.branchLabel (c.1.1 v) =
      P.2.branchLabel v := by
  rcases c with ⟨gamma, orient⟩
  change ((P.2.coordinateRelabel gamma).reverseLoops
    (P.targetLoopSet ⟨gamma, orient⟩)).branchLabel (gamma.1 v) =
      P.2.branchLabel v
  calc
    ((P.2.coordinateRelabel gamma).reverseLoops
        (P.targetLoopSet ⟨gamma, orient⟩)).branchLabel (gamma.1 v) =
        (P.2.coordinateRelabel gamma).branchLabel (gamma.1 v) :=
      BoundedKernelSubdivisionDatum.reverseLoops_branchLabel
        (P.2.coordinateRelabel gamma)
        (P.targetLoopSet ⟨gamma, orient⟩) (gamma.1 v)
    _ = P.2.branchLabel v :=
      P.2.coordinateRelabel_branchLabel gamma v

/-- Recovering branch coordinates from the image of a code returns the
branch permutation written in that code. -/
theorem globalRecoveredBranchCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    P.globalRecoveredBranchCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1.1 := by
  apply Equiv.ext
  intro v
  have hRecovered :=
    P.branchLabel_globalRecoveredBranchCoordinateEquiv
      (P.applySymmetry c) (P.applySymmetry_reconstructedGraph c).symm v
  have hCast :=
    P.branchCoordinateCountCast_globalRecoveredBranchCoordinatePerm
      (P.applySymmetry c) (P.applySymmetry_reconstructedGraph c).symm v
  have hcode := P.applySymmetry_branchLabel c v
  have hEquiv :
      P.globalRecoveredBranchCoordinateEquiv (P.applySymmetry c)
          (P.applySymmetry_reconstructedGraph c).symm v = c.1.1 v := by
    apply Sum.inl.inj
    apply (P.applySymmetry c).2.labels.injective
    exact hRecovered.trans hcode.symm
  apply Fin.ext
  have hCastVal := congrArg Fin.val hCast
  have hEquivVal := congrArg Fin.val hEquiv
  simpa only [branchCoordinateCountCast, finCongr_apply_coe] using
    hCastVal.trans hEquivVal

/-- Recovering suppressed-edge coordinates from the image of a code returns
the edge permutation written in that code. -/
theorem globalRecoveredKernelEdgeCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    P.globalRecoveredKernelEdgeCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1.2 := by
  rcases c with ⟨gamma, orient⟩
  apply Equiv.ext
  intro e
  let K := P.1.toLabelledBoundedKernel
  let Kgamma := K.coordinateRelabel gamma
  let Dgamma : BoundedKernelSubdivisionDatum k Kgamma :=
    P.2.coordinateRelabel gamma
  let A := P.targetLoopSet
    (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K)
  let R : BoundedKernelSubdivisionDatum k Kgamma := Dgamma.reverseLoops A
  let hReverse : R.reconstructedGraph = Dgamma.reconstructedGraph :=
    Dgamma.reverseLoops_reconstructedGraph A
  let hCoordinate : Dgamma.reconstructedGraph = P.2.reconstructedGraph :=
    P.2.coordinateRelabel_reconstructedGraph gamma
  let hBack : R.reconstructedGraph = P.2.reconstructedGraph :=
    hReverse.trans hCoordinate
  let hForward : P.2.reconstructedGraph = R.reconstructedGraph :=
    (P.applySymmetry_reconstructedGraph
      (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K)).symm
  let sigma := P.globalRecoveredKernelEdgeCoordinatePerm
    (P.applySymmetry
      (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K)) hForward
  have hglobalEquiv :=
    P.globalRecoveredKernelEdgeCoordinateEquiv_intrinsic
      (P.applySymmetry
        (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K)) hForward e
  have hcount :=
    P.kernelEdgeCoordinateCountCast_globalRecoveredKernelEdgeCoordinatePerm
      (P.applySymmetry
        (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K)) hForward e
  have htargetCoordinate :
      P.globalRecoveredKernelEdgeCoordinateEquiv
          (P.applySymmetry
            (⟨gamma, orient⟩ : BoundedKernelCoordinateCode K))
          hForward e = sigma e := by
    apply Fin.ext
    have hval := congrArg Fin.val hcount
    simpa only [kernelEdgeCoordinateCountCast, finCongr_apply_coe] using
      hval.symm
  rw [htargetCoordinate] at hglobalEquiv
  change variableKernelEdgeLabelEquivOfGraphEq hForward
      ((P.2.recoveredKernelEdgeEquiv K).symm e) =
    (R.recoveredKernelEdgeEquiv Kgamma).symm (sigma e) at hglobalEquiv
  have hproof : hBack = hForward.symm := Subsingleton.elim _ _
  have hglobalBack :
      variableKernelEdgeLabelEquivOfGraphEq hBack
          ((R.recoveredKernelEdgeEquiv Kgamma).symm (sigma e)) =
        (P.2.recoveredKernelEdgeEquiv K).symm e := by
    rw [hproof, ← hglobalEquiv]
    exact variableKernelEdgeLabelEquivOfGraphEq_symm_apply_apply hForward _
  have hcodeBack :
      variableKernelEdgeLabelEquivOfGraphEq hBack
          ((R.recoveredKernelEdgeEquiv Kgamma).symm (gamma.2 e)) =
        (P.2.recoveredKernelEdgeEquiv K).symm e := by
    rw [← variableKernelEdgeLabelEquivOfGraphEq_trans
      hReverse hCoordinate]
    rw [Dgamma.reverseLoops_recoveredKernelEdgeEquiv_symm
      Kgamma A (gamma.2 e)]
    exact P.2.coordinateRelabel_recoveredKernelEdgeEquiv_symm K gamma e
  have hintrinsic :
      (R.recoveredKernelEdgeEquiv Kgamma).symm (sigma e) =
        (R.recoveredKernelEdgeEquiv Kgamma).symm (gamma.2 e) :=
    (variableKernelEdgeLabelEquivOfGraphEq hBack).injective
      (hglobalBack.trans hcodeBack.symm)
  exact (R.recoveredKernelEdgeEquiv Kgamma).symm.injective hintrinsic

/-- Recovering both coordinate families from a symmetry image returns the
coordinate pair written in the code. -/
theorem globalRecoveredCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    P.globalRecoveredCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1 := by
  apply Prod.ext
  · exact P.globalRecoveredBranchCoordinatePerm_applySymmetry c
  · exact P.globalRecoveredKernelEdgeCoordinatePerm_applySymmetry c

theorem globalRecoveredCoordinatePerm_proof_irrel
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (h h' : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.globalRecoveredCoordinatePerm Q h =
      P.globalRecoveredCoordinatePerm Q h' := by
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

theorem globalRecoveredCoordinatePerm_congr_target
    {k ell : ℕ}
    (P Q R : BoundedKernelPresentation k ell)
    (hQR : Q = R)
    (hQ : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (hR : P.2.reconstructedGraph = R.2.reconstructedGraph) :
    P.globalRecoveredCoordinatePerm Q hQ =
      P.globalRecoveredCoordinatePerm R hR := by
  subst R
  exact P.globalRecoveredCoordinatePerm_proof_irrel Q hQ hR

/-- The variable-kernel symmetry map is injective. -/
theorem symmetryFibreMap_injective
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    Function.Injective (symmetryFibreMap P) := by
  intro c d hcd
  have hval : P.1.applySymmetry c = P.1.applySymmetry d :=
    congrArg Subtype.val hcd
  have hcoord : c.1 = d.1 := by
    have hc := P.1.globalRecoveredCoordinatePerm_applySymmetry c
    have hd := P.1.globalRecoveredCoordinatePerm_applySymmetry d
    have hcongr := P.1.globalRecoveredCoordinatePerm_congr_target
      (P.1.applySymmetry c) (P.1.applySymmetry d) hval
      (P.1.applySymmetry_reconstructedGraph c).symm
      (P.1.applySymmetry_reconstructedGraph d).symm
    exact hc.symm.trans (hcongr.trans hd)
  rcases c with ⟨gamma, orient⟩
  rcases d with ⟨eta, orient'⟩
  change gamma = eta at hcoord
  subst eta
  have hsets :
      P.1.targetLoopSet
          (⟨gamma, orient⟩ :
            BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel) =
        P.1.targetLoopSet
          (⟨gamma, orient'⟩ :
            BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel) := by
    apply (P.1.2.coordinateRelabel gamma).reverseLoops_injective
    exact eq_of_heq (Sigma.mk.inj_iff.mp hval).2
  have horient : orient = orient' := by
    funext e
    have hmem := congrArg
      (fun A ↦ boundedKernelLoopEdgeCoordinateRelabelEquiv
        P.1.1.toLabelledBoundedKernel gamma e ∈ A) hsets
    have hiff : orient e = true ↔ orient' e = true := by
      simpa only [P.1.targetLoopSet_mem] using Iff.of_eq hmem
    cases he : orient e <;> cases he' : orient' e <;>
      simp_all
  subst orient'
  rfl

/-- The unique target loop set produced by fixed-kernel recovery. -/
noncomputable def recoveredTargetLoopSet
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Finset (BoundedKernelLoopEdge Q.1.toLabelledBoundedKernel) :=
  Classical.choose
    (P.existsUnique_reverseLoops_globalRecoveredAlignedCastDatum_eq_target
      hell Q hG)

theorem recoveredTargetLoopSet_spec
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).reverseLoops
        (P.recoveredTargetLoopSet hell Q hG) = Q.2 :=
  (Classical.choose_spec
    (P.existsUnique_reverseLoops_globalRecoveredAlignedCastDatum_eq_target
      hell Q hG)).1

/-- Pull the unique target loop set back through the recovered kernel cast
and the coordinate relabelling, producing a Boolean code based at `P`. -/
noncomputable def recoveredSymmetryCode
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel :=
  let hG := P.2.trans Q.2.symm
  let gamma := P.1.globalRecoveredCoordinatePerm Q.1 hG
  let hConnected :=
    P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q.1 hG
  let hK : P.1.1.toLabelledBoundedKernel.coordinateRelabel gamma =
      Q.1.1.toLabelledBoundedKernel :=
    congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel hConnected
  let AQ := P.1.recoveredTargetLoopSet hell Q.1 hG
  let Agamma := boundedKernelLoopSetCast hK.symm AQ
  ⟨gamma, fun e ↦ decide
    (boundedKernelLoopEdgeCoordinateRelabelEquiv
      P.1.1.toLabelledBoundedKernel gamma e ∈ Agamma)⟩

/-- The target loop set generated by the recovered Boolean code is exactly
the inverse-cast unique loop set. -/
theorem recoveredSymmetryCode_targetLoopSet
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    let hG := P.2.trans Q.2.symm
    let gamma := P.1.globalRecoveredCoordinatePerm Q.1 hG
    let hConnected :=
      P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q.1 hG
    let hK : P.1.1.toLabelledBoundedKernel.coordinateRelabel gamma =
        Q.1.1.toLabelledBoundedKernel :=
      congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel hConnected
    P.1.targetLoopSet (recoveredSymmetryCode hell P Q) =
      boundedKernelLoopSetCast hK.symm
        (P.1.recoveredTargetLoopSet hell Q.1 hG) := by
  let hG := P.2.trans Q.2.symm
  let gamma := P.1.globalRecoveredCoordinatePerm Q.1 hG
  let hConnected :=
    P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q.1 hG
  let hK : P.1.1.toLabelledBoundedKernel.coordinateRelabel gamma =
      Q.1.1.toLabelledBoundedKernel :=
    congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel hConnected
  let AQ := P.1.recoveredTargetLoopSet hell Q.1 hG
  let Agamma := boundedKernelLoopSetCast hK.symm AQ
  change P.1.targetLoopSet
      (⟨gamma, fun e ↦ decide
        (boundedKernelLoopEdgeCoordinateRelabelEquiv
          P.1.1.toLabelledBoundedKernel gamma e ∈ Agamma)⟩ :
        BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel) = Agamma
  ext e
  obtain ⟨d, rfl⟩ :=
    (boundedKernelLoopEdgeCoordinateRelabelEquiv
      P.1.1.toLabelledBoundedKernel gamma).surjective e
  simp [targetLoopSet, sourceLoopSet]

/-- The recovered code maps back to its target fibre element. -/
theorem symmetryFibreMap_recoveredSymmetryCode
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    symmetryFibreMap P (recoveredSymmetryCode hell P Q) = Q := by
  apply Subtype.ext
  let hG := P.2.trans Q.2.symm
  let gamma := P.1.globalRecoveredCoordinatePerm Q.1 hG
  let Kgamma := P.1.1.coordinateRelabel gamma
  let Dgamma := P.1.2.coordinateRelabel gamma
  let hConnected : Kgamma = Q.1.1 :=
    P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q.1 hG
  let hK : Kgamma.toLabelledBoundedKernel =
      Q.1.1.toLabelledBoundedKernel :=
    congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel hConnected
  let AQ := P.1.recoveredTargetLoopSet hell Q.1 hG
  let Agamma := boundedKernelLoopSetCast hK.symm AQ
  let Dcast := boundedKernelSubdivisionDatumCast hK Dgamma
  have htargetSet :
      P.1.targetLoopSet (recoveredSymmetryCode hell P Q) = Agamma :=
    recoveredSymmetryCode_targetLoopSet hell P Q
  change (⟨Kgamma,
    Dgamma.reverseLoops
      (P.1.targetLoopSet (recoveredSymmetryCode hell P Q))⟩ :
      BoundedKernelPresentation k ell) = Q.1
  rw [htargetSet]
  apply Sigma.ext hConnected
  have hreverse : HEq (Dgamma.reverseLoops Agamma)
      (Dcast.reverseLoops (boundedKernelLoopSetCast hK Agamma)) :=
    Dgamma.reverseLoops_cast_heq hK Agamma
  have hset : boundedKernelLoopSetCast hK Agamma = AQ :=
    boundedKernelLoopSetCast_symm_apply hK AQ
  rw [hset] at hreverse
  have htarget : Dcast.reverseLoops AQ = Q.1.2 :=
    P.1.recoveredTargetLoopSet_spec hell Q.1 hG
  exact hreverse.trans (heq_of_eq htarget)

theorem symmetryFibreMap_surjective
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    Function.Surjective (symmetryFibreMap P) := by
  intro Q
  exact ⟨recoveredSymmetryCode hell P Q,
    symmetryFibreMap_recoveredSymmetryCode hell P Q⟩

/-- Exact equivalence between the coordinate-code space based at `P` and its
whole global reconstruction fibre. -/
noncomputable def symmetryReconstructionFibreEquiv
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel ≃
      ReconstructionFibre (ell := ell) G :=
  Equiv.ofBijective (symmetryFibreMap P)
    ⟨symmetryFibreMap_injective P,
      symmetryFibreMap_surjective hell P⟩

@[instance_reducible] noncomputable def reconstructionFibreFintypeOfBase
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    Fintype (ReconstructionFibre (ell := ell) G) :=
  Fintype.ofEquiv
    (BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel)
    (symmetryReconstructionFibreEquiv hell P)

/-- Exact variable-kernel reconstruction-fibre cardinality, conditional on a
chosen base presentation in that fibre. -/
theorem reconstructionFibre_card_of_base
    {k ell : ℕ} (hell : 0 < ell)
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    @Fintype.card (ReconstructionFibre (ell := ell) G)
        (reconstructionFibreFintypeOfBase hell P) =
      P.1.1.toLabelledBoundedKernel.coordinateMultiplicity := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase hell P
  calc
    Fintype.card (ReconstructionFibre (ell := ell) G) =
        Fintype.card
          (BoundedKernelCoordinateCode
            P.1.1.toLabelledBoundedKernel) :=
      (Fintype.card_congr
        (symmetryReconstructionFibreEquiv hell P)).symm
    _ = P.1.1.toLabelledBoundedKernel.coordinateMultiplicity :=
      P.1.symmetryCode_card

end BoundedKernelPresentation

end PerronWright.GraphCore
