import PerronWright.Enumeration.CubicRecoveredKernelEdgeNaturality

/-!
# Exact global cubic-presentation reconstruction fibres

Fix a base presentation `P` in the reconstruction fibre of a labelled graph.
The coordinate permutations and loop reversals based at `P` give every other
presentation in that fibre exactly once.  The base point is an explicit
hypothesis throughout: no assertion is made that an arbitrary graph admits a
cubic-kernel presentation.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Casting a loop set across an equality and immediately back is the
identity. -/
theorem cubicKernelLoopSetCast_symm_apply
    {ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E) (A : Finset (CubicKernelLoopEdge E)) :
    cubicKernelLoopSetCast h (cubicKernelLoopSetCast h.symm A) = A := by
  subst E
  rfl

/-- A datum and its explicit transport along an endpoint-table equality are
heterogeneously equal. -/
theorem cubicKernelSubdivisionDatumCast_heq
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E) (D : CubicKernelSubdivisionDatum k ell H) :
    HEq D (cubicKernelSubdivisionDatumCast h D) := by
  subst E
  rfl

/-- Equality transport followed by transport along the inverse graph equality
fixes every intrinsic suppressed-edge label. -/
theorem kernelEdgeLabelEquivOfGraphEq_symm_apply_apply
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (z : KernelEdgeLabel G) :
    kernelEdgeLabelEquivOfGraphEq h.symm
        (kernelEdgeLabelEquivOfGraphEq h z) = z := by
  subst E
  rfl

/-- Loop reversal leaves every non-loop path label unchanged. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_pathLabel_nonloop
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (e : Fin (3 * ell)) (he : ¬(H.endpoints e).IsDiag)
    (i : Fin (D.profile.length e).val) :
    (D.reverseLoops A).pathLabel e i = D.pathLabel e i := by
  change D.labels
      (loopOrientationSetSlotEquiv D.profile A (.inr ⟨e, i⟩)) =
    D.labels (.inr ⟨e, i⟩)
  rw [loopOrientationSetSlotEquiv_nonloop D.profile A e he]

/-- Loop reversal preserves each actual degree-two component.  If the edge is
a reversed loop, its first internal vertex becomes its last internal vertex;
the two vertices lie in the same degree-two component by the internal path. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_positiveEdgeComponent
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    degreeTwoComponentEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        ((D.reverseLoops A).positiveEdgeComponent K e) =
      D.positiveEdgeComponent K e := by
  let i : Fin (D.profile.length e.1).val := ⟨0, e.2⟩
  unfold CubicKernelSubdivisionDatum.positiveEdgeComponent
  by_cases hloop : (K.graph.endpoints e.1).IsDiag
  · let a : CubicKernelLoopEdge K.graph := ⟨e.1, hloop⟩
    by_cases ha : a ∈ A
    · let j : Fin (D.profile.length e.1).val := Fin.rev i
      calc
        degreeTwoComponentEquivOfGraphEq
            (D.reverseLoops_reconstructedGraph A)
            ((twoGraph (D.reverseLoops A).reconstructedGraph).connectedComponentMk
                ⟨(D.reverseLoops A).pathLabel e.1 i,
                  (D.reverseLoops A).internalVertex_degree_eq_two K e.1 i⟩) =
            (twoGraph D.reconstructedGraph).connectedComponentMk
              ⟨D.pathLabel e.1 j,
                D.internalVertex_degree_eq_two K e.1 j⟩ := by
              apply degreeTwoComponentEquivOfGraphEq_connectedComponentMk
              exact D.reverseLoops_pathLabel_mem A a ha i
        _ = (twoGraph D.reconstructedGraph).connectedComponentMk
              ⟨D.pathLabel e.1 i,
                D.internalVertex_degree_eq_two K e.1 i⟩ := by
              apply SimpleGraph.ConnectedComponent.eq.mpr
              exact D.internalPath_reachable_twoGraph K e.1 j i
    · apply degreeTwoComponentEquivOfGraphEq_connectedComponentMk
      exact D.reverseLoops_pathLabel_not_mem A a ha i
  · apply degreeTwoComponentEquivOfGraphEq_connectedComponentMk
    exact D.reverseLoops_pathLabel_nonloop A e.1 hloop i

/-- The positive component summand of `KernelEdgeLabel` is unchanged by loop
reversal. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_positiveKernelEdgeLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    kernelEdgeLabelEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        (.inl ((D.reverseLoops A).positiveEdgeComponent K e)) =
      (.inl (D.positiveEdgeComponent K e) :
        KernelEdgeLabel D.reconstructedGraph) := by
  rw [kernelEdgeLabelEquivOfGraphEq_inl,
    D.reverseLoops_positiveEdgeComponent K A e]

/-- A zero-length edge emits the same direct branch edge after any loop
reversal. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_zeroLengthEdge_val
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (e : {e : Fin (3 * ell) // (D.profile.length e).val = 0}) :
    ((D.reverseLoops A).zeroLengthEdgeToDirectBranchEdge K e).1 =
      (D.zeroLengthEdgeToDirectBranchEdge K e).1 := by
  change (D.reverseLoops A).subdivisionEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot (D.reverseLoops A)) =
    D.subdivisionEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot D)
  calc
    (D.reverseLoops A).subdivisionEdge
        (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoops A)) =
        s((D.reverseLoops A).branchLabel
            (cubicKernelOrderedEndpoints K.graph e.1).1,
          (D.reverseLoops A).branchLabel
            (cubicKernelOrderedEndpoints K.graph e.1).2) :=
      (D.reverseLoops A).subdivisionEdge_direct e.1 e.2
    _ = s(D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).1,
          D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).2) := by
      simp only [CubicKernelSubdivisionDatum.reverseLoops_branchLabel]
    _ = D.subdivisionEdge
        (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot D) :=
      (D.subdivisionEdge_direct e.1 e.2).symm

/-- The direct-edge summand of `KernelEdgeLabel` is unchanged by loop
reversal. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_zeroKernelEdgeLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (e : {e : Fin (3 * ell) // (D.profile.length e).val = 0}) :
    kernelEdgeLabelEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        (.inr ((D.reverseLoops A).zeroLengthEdgeToDirectBranchEdge K e)) =
      (.inr (D.zeroLengthEdgeToDirectBranchEdge K e) :
        KernelEdgeLabel D.reconstructedGraph) := by
  apply kernelEdgeLabelEquivOfGraphEq_inr_eq
  exact D.reverseLoops_zeroLengthEdge_val K A e

/-- The full intrinsic recovered edge is invariant under loop reversal. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_recoveredKernelEdgeEquiv_symm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (e : Fin (3 * ell)) :
    kernelEdgeLabelEquivOfGraphEq
        (D.reverseLoops_reconstructedGraph A)
        (((D.reverseLoops A).recoveredKernelEdgeEquiv K).symm e) =
      (D.recoveredKernelEdgeEquiv K).symm e := by
  by_cases hpos : 0 < (D.profile.length e).val
  · let ep : {f : Fin (3 * ell) // 0 < (D.profile.length f).val} :=
      ⟨e, hpos⟩
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
    rw [htarget, hsource]
    exact D.reverseLoops_positiveKernelEdgeLabel K A ep
  · have hzero : (D.profile.length e).val = 0 :=
      Nat.eq_zero_of_not_pos hpos
    let ez : {f : Fin (3 * ell) // (D.profile.length f).val = 0} :=
      ⟨e, hzero⟩
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
    exact D.reverseLoops_zeroKernelEdgeLabel K A ez

namespace CubicKernelPresentation

/-- Reading a transported branch coordinate after applying a global symmetry
returns the original branch label. -/
theorem applySymmetry_branchLabel
    {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) (v : Fin (2 * ell)) :
    (P.applySymmetry c).2.branchLabel (c.1.1 v) = P.2.branchLabel v := by
  rcases c with ⟨γ, A⟩
  change Finset (CubicKernelLoopEdge
    (finiteMultiGraphCoordinateRelabel γ P.1.graph)) at A
  change ((P.2.coordinateRelabel γ).reverseLoops A).branchLabel (γ.1 v) =
    P.2.branchLabel v
  rw [CubicKernelSubdivisionDatum.reverseLoops_branchLabel,
    P.2.coordinateRelabel_branchLabel]

/-- The globally recovered branch permutation of the image of a symmetry code
is the branch permutation written in that code. -/
theorem globalRecoveredBranchCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) :
    P.globalRecoveredBranchCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1.1 := by
  apply Equiv.ext
  intro v
  let hG := (P.applySymmetry_reconstructedGraph c).symm
  have hrecovered :=
    P.branchLabel_globalRecoveredBranchCoordinatePerm
      (P.applySymmetry c) hG v
  have hcode := P.applySymmetry_branchLabel c v
  apply Sum.inl.inj
  apply (P.applySymmetry c).2.labels.injective
  exact hrecovered.trans hcode.symm

/-- The globally recovered edge permutation of the image of a symmetry code
is the edge permutation written in that code. -/
theorem globalRecoveredKernelEdgeCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) :
    P.globalRecoveredKernelEdgeCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1.2 := by
  rcases c with ⟨γ, A⟩
  apply Equiv.ext
  intro e
  let Kγ := P.1.coordinateRelabel γ
  let Dγ : CubicKernelSubdivisionDatum k ell Kγ.graph :=
    P.2.coordinateRelabel γ
  let R : CubicKernelSubdivisionDatum k ell Kγ.graph := Dγ.reverseLoops A
  let hReverse : R.reconstructedGraph = Dγ.reconstructedGraph :=
    Dγ.reverseLoops_reconstructedGraph A
  let hCoordinate : Dγ.reconstructedGraph = P.2.reconstructedGraph :=
    P.2.coordinateRelabel_reconstructedGraph γ
  let hBack : R.reconstructedGraph = P.2.reconstructedGraph :=
    hReverse.trans hCoordinate
  let hForward : P.2.reconstructedGraph = R.reconstructedGraph :=
    (P.applySymmetry_reconstructedGraph (⟨γ, A⟩ : P.SymmetryCode)).symm
  let σ := P.globalRecoveredKernelEdgeCoordinatePerm
    (P.applySymmetry (⟨γ, A⟩ : P.SymmetryCode)) hForward
  have hglobal := P.globalRecoveredKernelEdgeCoordinatePerm_intrinsic
    (P.applySymmetry (⟨γ, A⟩ : P.SymmetryCode)) hForward e
  change kernelEdgeLabelEquivOfGraphEq hForward
      ((P.2.recoveredKernelEdgeEquiv P.1).symm e) =
    (R.recoveredKernelEdgeEquiv Kγ).symm (σ e) at hglobal
  have hproof : hBack = hForward.symm := Subsingleton.elim _ _
  have hglobalBack :
      kernelEdgeLabelEquivOfGraphEq hBack
          ((R.recoveredKernelEdgeEquiv (P.1.coordinateRelabel γ)).symm
            (σ e)) =
        (P.2.recoveredKernelEdgeEquiv P.1).symm e := by
    rw [hproof, ← hglobal]
    exact kernelEdgeLabelEquivOfGraphEq_symm_apply_apply hForward _
  have hcodeBack :
      kernelEdgeLabelEquivOfGraphEq hBack
          ((R.recoveredKernelEdgeEquiv (P.1.coordinateRelabel γ)).symm
            (γ.2 e)) =
        (P.2.recoveredKernelEdgeEquiv P.1).symm e := by
    rw [← kernelEdgeLabelEquivOfGraphEq_trans hReverse hCoordinate]
    rw [Dγ.reverseLoops_recoveredKernelEdgeEquiv_symm
      (P.1.coordinateRelabel γ) A (γ.2 e)]
    exact P.2.coordinateRelabel_recoveredKernelEdgeEquiv_symm P.1 γ e
  have hintrinsic :
      (R.recoveredKernelEdgeEquiv (P.1.coordinateRelabel γ)).symm (σ e) =
        (R.recoveredKernelEdgeEquiv (P.1.coordinateRelabel γ)).symm
          (γ.2 e) :=
    (kernelEdgeLabelEquivOfGraphEq hBack).injective
      (hglobalBack.trans hcodeBack.symm)
  exact (R.recoveredKernelEdgeEquiv (P.1.coordinateRelabel γ)).symm.injective
    hintrinsic

/-- Recovering both coordinate families from the image of a code returns the
coordinate pair of that code. -/
theorem globalRecoveredCoordinatePerm_applySymmetry
    {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) :
    P.globalRecoveredCoordinatePerm (P.applySymmetry c)
        (P.applySymmetry_reconstructedGraph c).symm = c.1 := by
  apply Prod.ext
  · exact P.globalRecoveredBranchCoordinatePerm_applySymmetry c
  · exact P.globalRecoveredKernelEdgeCoordinatePerm_applySymmetry c

/-- The recovered coordinate pair is independent of the proof used to identify
the two reconstructed graphs. -/
theorem globalRecoveredCoordinatePerm_proof_irrel
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (h h' : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.globalRecoveredCoordinatePerm Q h =
      P.globalRecoveredCoordinatePerm Q h' := by
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

/-- The recovered coordinate pair is compatible with equality of the target
presentation. -/
theorem globalRecoveredCoordinatePerm_congr_target
    {k ell : ℕ}
    (P Q R : CubicKernelPresentation k ell)
    (hQR : Q = R)
    (hQ : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (hR : P.2.reconstructedGraph = R.2.reconstructedGraph) :
    P.globalRecoveredCoordinatePerm Q hQ =
      P.globalRecoveredCoordinatePerm R hR := by
  subst R
  exact P.globalRecoveredCoordinatePerm_proof_irrel Q hQ hR

/-- The global symmetry map is injective.  Coordinate injectivity is recovered
intrinsically; once those coordinates agree, fixed-kernel loop freeness gives
equality of the dependent loop sets. -/
theorem symmetryFibreMap_injective
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
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
  rcases c with ⟨γ, A⟩
  rcases d with ⟨η, B⟩
  change γ = η at hcoord
  subst η
  have hAB : A = B := by
    apply (P.1.2.coordinateRelabel γ).reverseLoops_injective
    exact eq_of_heq (Sigma.mk.inj_iff.mp hval).2
  subst B
  rfl

/-- The canonical target loop set selected by the unique fixed-kernel loop
orbit theorem. -/
noncomputable def recoveredTargetLoopSet
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Finset (CubicKernelLoopEdge Q.1.graph) :=
  Classical.choose
    (P.existsUnique_reverseLoops_globalRecoveredAlignedCastDatum_eq_target Q hG)

theorem recoveredTargetLoopSet_spec
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum Q hG).reverseLoops
        (P.recoveredTargetLoopSet Q hG) = Q.2 :=
  (Classical.choose_spec
    (P.existsUnique_reverseLoops_globalRecoveredAlignedCastDatum_eq_target
      Q hG)).1

/-- Pull the unique target loop set back along the recovered kernel equality;
the resulting dependent pair is a symmetry code based at `P`. -/
noncomputable def recoveredSymmetryCode
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    P.1.SymmetryCode :=
  let hG := P.2.trans Q.2.symm
  let γ := P.1.globalRecoveredCoordinatePerm Q.1 hG
  let hK := P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm Q.1 hG
  let hKG := congrArg LabelledConnectedCubicKernel.graph hK
  ⟨γ, cubicKernelLoopSetCast hKG.symm
    (P.1.recoveredTargetLoopSet Q.1 hG)⟩

/-- The recovered code maps back to its target fibre element.  The proof uses
an explicit datum cast and transports the loop set in the inverse direction. -/
theorem symmetryFibreMap_recoveredSymmetryCode
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    symmetryFibreMap P (recoveredSymmetryCode P Q) = Q := by
  apply Subtype.ext
  let hG := P.2.trans Q.2.symm
  let γ := P.1.globalRecoveredCoordinatePerm Q.1 hG
  let Kγ := P.1.1.coordinateRelabel γ
  let Dγ := P.1.2.coordinateRelabel γ
  let hK : Kγ = Q.1.1 :=
    P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm Q.1 hG
  let hKG : Kγ.graph = Q.1.1.graph :=
    congrArg LabelledConnectedCubicKernel.graph hK
  let AQ := P.1.recoveredTargetLoopSet Q.1 hG
  let Aγ := cubicKernelLoopSetCast hKG.symm AQ
  let Dcast := cubicKernelSubdivisionDatumCast hKG Dγ
  change (⟨Kγ, Dγ.reverseLoops Aγ⟩ : CubicKernelPresentation k ell) = Q.1
  apply Sigma.ext hK
  have hdatum : HEq Dγ Dcast :=
    cubicKernelSubdivisionDatumCast_heq hKG Dγ
  have hreverse : HEq (Dγ.reverseLoops Aγ)
      (Dcast.reverseLoops (cubicKernelLoopSetCast hKG Aγ)) :=
    Dγ.reverseLoops_cast_heq hKG hdatum Aγ
  have hset : cubicKernelLoopSetCast hKG Aγ = AQ := by
    exact cubicKernelLoopSetCast_symm_apply hKG AQ
  rw [hset] at hreverse
  have htarget : Dcast.reverseLoops AQ = Q.1.2 := by
    exact P.1.recoveredTargetLoopSet_spec Q.1 hG
  exact hreverse.trans (heq_of_eq htarget)

/-- Every target in the reconstruction fibre has a symmetry-code preimage. -/
theorem symmetryFibreMap_surjective
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    Function.Surjective (symmetryFibreMap P) := by
  intro Q
  exact ⟨recoveredSymmetryCode P Q,
    symmetryFibreMap_recoveredSymmetryCode P Q⟩

/-- Every target has one unique symmetry-code preimage. -/
theorem existsUnique_symmetryFibreMap_preimage
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    ∃! c : P.1.SymmetryCode, symmetryFibreMap P c = Q := by
  refine ⟨recoveredSymmetryCode P Q,
    symmetryFibreMap_recoveredSymmetryCode P Q, ?_⟩
  intro c hc
  apply symmetryFibreMap_injective P
  exact hc.trans (symmetryFibreMap_recoveredSymmetryCode P Q).symm

/-- Exact equivalence between the dependent symmetry-code space based at `P`
and the whole global reconstruction fibre containing `P`. -/
noncomputable def symmetryReconstructionFibreEquiv
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    P.1.SymmetryCode ≃ ReconstructionFibre (ell := ell) G :=
  Equiv.ofBijective (symmetryFibreMap P)
    ⟨symmetryFibreMap_injective P, symmetryFibreMap_surjective P⟩

/-- A chosen base presentation supplies the finite structure on its global
reconstruction fibre.  This is a definition rather than a global instance,
because an arbitrary graph need not possess any such base presentation. -/
@[instance_reducible] noncomputable def reconstructionFibreFintypeOfBase
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    Fintype (ReconstructionFibre (ell := ell) G) :=
  Fintype.ofEquiv P.1.SymmetryCode (symmetryReconstructionFibreEquiv P)

/-- Exact global reconstruction-fibre cardinality, conditional on the given
base presentation `P` in that fibre. -/
theorem reconstructionFibre_card_of_base
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    @Fintype.card (ReconstructionFibre (ell := ell) G)
        (reconstructionFibreFintypeOfBase P) =
      (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge P.1.1.graph) := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase P
  calc
    Fintype.card (ReconstructionFibre (ell := ell) G) =
        Fintype.card P.1.SymmetryCode :=
      (Fintype.card_congr (symmetryReconstructionFibreEquiv P)).symm
    _ = (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge P.1.1.graph) :=
      P.1.symmetryCode_card

end CubicKernelPresentation

end PerronWright.GraphCore
