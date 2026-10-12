import PerronWright.Enumeration.VariableRecoveredCoordinateAlignment

/-!
# Global recovered-coordinate alignment for bounded-kernel presentations

The globally recovered source coordinate permutation is followed by the
dependent cast to the target bounded kernel.  This file proves that the
resulting fixed-kernel datum has the target's branch labels and length
profile, and that its recovered branch, edge, and oriented path coordinates
relative to the target are all the identity.  Consequently the recovered
coordinate-aligned datum is literally the target datum.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

private noncomputable def boundedKernelSubdivisionSlotEquivOfProfileEq
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    {L M : BoundedKernelLengthProfile k K}
    (h : L = M) :
    BoundedKernelSubdivisionSlot L ≃ BoundedKernelSubdivisionSlot M :=
  Equiv.cast (congrArg BoundedKernelSubdivisionSlot h)

private theorem boundedKernelSubdivisionSlotEquivOfProfileEq_inl
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    {L M : BoundedKernelLengthProfile k K}
    (h : L = M) (v : Fin K.shape.1.val) :
    boundedKernelSubdivisionSlotEquivOfProfileEq h (.inl v) = .inl v := by
  subst M
  rfl

private theorem boundedKernelSubdivisionSlotEquivOfProfileEq_inr
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    {L M : BoundedKernelLengthProfile k K}
    (h : L = M) (e : Fin K.shape.2.1.val)
    (i : Fin (L.length e).val) :
    boundedKernelSubdivisionSlotEquivOfProfileEq h (.inr ⟨e, i⟩) =
      .inr ⟨e,
        cast (congrArg (fun N ↦ Fin (N.length e).val) h) i⟩ := by
  subst M
  rfl

private theorem boundedKernelSubdivisionSlotEquivOfProfileEq_trans_heq
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    {L M : BoundedKernelLengthProfile k K}
    (h : L = M) (f : BoundedKernelSubdivisionSlot M ≃ Fin k) :
    HEq ((boundedKernelSubdivisionSlotEquivOfProfileEq h).trans f) f := by
  subst M
  rfl

/-- Equality-casting a bounded-kernel datum preserves its branch labels at
the correspondingly cast coordinate. -/
theorem boundedKernelSubdivisionDatumCast_branchLabel
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (hK : K = L)
    (D : BoundedKernelSubdivisionDatum k K)
    (v : Fin K.shape.1.val) :
    (boundedKernelSubdivisionDatumCast hK D).branchLabel
        (Fin.cast
          (congrArg (fun J : LabelledBoundedKernel ell ↦
            J.shape.1.val) hK) v) =
      D.branchLabel v := by
  subst L
  rfl

namespace BoundedKernelPresentation

/-- The vertex-count cast induced by the exact globally aligned kernel
equality agrees with the recovered cross-presentation branch equivalence. -/
theorem globalRecoveredAlignedCastDatum_branchCoordinate_cast
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin P.1.toLabelledBoundedKernel.shape.1.val) :
    let gamma := P.globalRecoveredCoordinatePerm Q hG
    let hK :
        P.1.toLabelledBoundedKernel.coordinateRelabel gamma =
          Q.1.toLabelledBoundedKernel :=
      congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel
        (P.kernel_coordinateRelabel_globalRecoveredCoordinatePerm
          hell Q hG)
    Fin.cast
        (congrArg (fun J : LabelledBoundedKernel ell ↦
          J.shape.1.val) hK)
        (gamma.1 v) =
      P.globalRecoveredBranchCoordinateEquiv Q hG v := by
  dsimp only
  rw [← P.branchCoordinateCountCast_globalRecoveredBranchCoordinatePerm
    Q hG v]
  apply Fin.ext
  change
    (Fin.cast _
      (P.globalRecoveredBranchCoordinatePerm Q hG v)).val =
      (P.globalRecoveredBranchCoordinatePerm Q hG v).val
  exact Fin.val_cast _ _

/-- At corresponding globally recovered branch coordinates, the aligned cast
datum and target datum carry the same original label. -/
theorem globalRecoveredAlignedCastDatum_branchLabel_apply
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin P.1.toLabelledBoundedKernel.shape.1.val) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).branchLabel
        (P.globalRecoveredBranchCoordinateEquiv Q hG v) =
      Q.2.branchLabel
        (P.globalRecoveredBranchCoordinateEquiv Q hG v) := by
  let gamma := P.globalRecoveredCoordinatePerm Q hG
  let KP := P.1.toLabelledBoundedKernel
  let KQ := Q.1.toLabelledBoundedKernel
  let Dgamma := P.2.coordinateRelabel gamma
  let hConnected : P.1.coordinateRelabel gamma = Q.1 :=
    P.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q hG
  let hK : KP.coordinateRelabel gamma = KQ :=
    congrArg LabelledConnectedBoundedKernel.toLabelledBoundedKernel hConnected
  change (boundedKernelSubdivisionDatumCast hK Dgamma).branchLabel
      (P.globalRecoveredBranchCoordinateEquiv Q hG v) =
    Q.2.branchLabel (P.globalRecoveredBranchCoordinateEquiv Q hG v)
  rw [← P.globalRecoveredAlignedCastDatum_branchCoordinate_cast
    hell Q hG v]
  calc
    (boundedKernelSubdivisionDatumCast hK Dgamma).branchLabel
        (Fin.cast
          (congrArg (fun J : LabelledBoundedKernel ell ↦
            J.shape.1.val) hK) (gamma.1 v)) =
        Dgamma.branchLabel (gamma.1 v) :=
      boundedKernelSubdivisionDatumCast_branchLabel hK Dgamma (gamma.1 v)
    _ = P.2.branchLabel v :=
      P.2.coordinateRelabel_branchLabel gamma v
    _ = Q.2.branchLabel
        (P.globalRecoveredBranchCoordinateEquiv Q hG v) :=
      (P.branchLabel_globalRecoveredBranchCoordinateEquiv Q hG v).symm

/-- The aligned cast datum and target datum agree at every branch
coordinate. -/
theorem globalRecoveredAlignedCastDatum_branchLabel
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin Q.1.toLabelledBoundedKernel.shape.1.val) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).branchLabel v =
      Q.2.branchLabel v := by
  let sigma := P.globalRecoveredBranchCoordinateEquiv Q hG
  obtain ⟨u, rfl⟩ := sigma.surjective v
  exact P.globalRecoveredAlignedCastDatum_branchLabel_apply
    hell Q hG u

/-- The recovered branch-coordinate permutation from the aligned cast datum
to the target datum is the identity. -/
theorem globalRecoveredAlignedCastDatum_recoveredBranchCoordinatePerm
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).recoveredBranchCoordinatePerm
          Q.1.toLabelledBoundedKernel Q.2
          (P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG) =
      Equiv.refl
        (Fin Q.1.toLabelledBoundedKernel.shape.1.val) := by
  apply Equiv.ext
  intro v
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  have hlabel :=
    D.branchLabel_recoveredBranchCoordinatePerm
      Q.1.toLabelledBoundedKernel Q.2 hDQ v
  have hsame :
      Q.2.branchLabel
          (D.recoveredBranchCoordinatePerm
            Q.1.toLabelledBoundedKernel Q.2 hDQ v) =
        Q.2.branchLabel v := by
    exact hlabel.trans
      (P.globalRecoveredAlignedCastDatum_branchLabel hell Q hG v)
  change Q.2.labels (.inl _) = Q.2.labels (.inl _) at hsame
  exact Sum.inl.inj (Q.2.labels.injective hsame)

/-- The aligned cast datum and target datum have the same complete admissible
length profile. -/
theorem globalRecoveredAlignedCastDatum_profile
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).profile = Q.2.profile := by
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let K := Q.1.toLabelledBoundedKernel
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  have hedge :=
    P.globalRecoveredAlignedCastDatum_recoveredKernelEdgeCoordinatePerm
      hell Q hG
  have hlength : D.profile.length = Q.2.profile.length := by
    funext e
    apply Fin.ext
    have h := D.profile_length_recoveredKernelEdgeCoordinatePerm
      K Q.2 hDQ e
    have hedgeAt := congrArg (fun sigma => sigma e) hedge
    simpa only [Equiv.refl_apply] using h.trans
      (congrArg (fun f => (Q.2.profile.length f).val) hedgeAt)
  cases hD : D.profile with
  | mk dlength dtotal dloop ddirect =>
      cases hQ : Q.2.profile with
      | mk qlength qtotal qloop qdirect =>
          simp only [hD, hQ] at hlength ⊢
          subst qlength
          rfl

/-- Once the recovered branch and edge coordinates are both the identity,
the recovered internal path equivalence preserves its numerical index. -/
theorem globalRecoveredAlignedCastDatum_recoveredPathIndexEquiv_val
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin Q.1.toLabelledBoundedKernel.shape.2.1.val)
    (i : Fin ((P.globalRecoveredAlignedCastDatum hell Q hG).profile.length e).val) :
    (((P.globalRecoveredAlignedCastDatum hell Q hG).recoveredPathIndexEquiv
      Q.1.toLabelledBoundedKernel Q.2
      (P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG) e) i).val =
      i.val := by
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let K := Q.1.toLabelledBoundedKernel
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  have hedge :=
    P.globalRecoveredAlignedCastDatum_recoveredKernelEdgeCoordinatePerm
      hell Q hG
  have hbranch :=
    P.globalRecoveredAlignedCastDatum_recoveredBranchCoordinatePerm
      hell Q hG
  by_cases hloop :
      ((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag
  · rw [D.recoveredPathIndexEquiv_of_loop K Q.2 hDQ e hloop]
    simp only [finCongr_apply_coe]
  · have hfirst :
        D.recoveredBranchCoordinatePerm K Q.2 hDQ
            (boundedKernelOrderedEndpoints K.shape e).1 =
          (boundedKernelOrderedEndpoints K.shape
            (D.recoveredKernelEdgeCoordinatePerm K Q.2 hDQ e)).1 := by
      rw [hbranch, hedge]
      rfl
    rw [D.recoveredPathIndexEquiv_of_nonloop_direct
      K Q.2 hDQ e hloop hfirst]
    simp only [finCongr_apply_coe]

/-- Dependent form of the preceding path-index statement. -/
theorem globalRecoveredAlignedCastDatum_recoveredPathIndexEquiv_heq
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin Q.1.toLabelledBoundedKernel.shape.2.1.val)
    (i : Fin ((P.globalRecoveredAlignedCastDatum hell Q hG).profile.length e).val) :
    HEq
      (((P.globalRecoveredAlignedCastDatum hell Q hG).recoveredPathIndexEquiv
        Q.1.toLabelledBoundedKernel Q.2
        (P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG) e) i)
      i := by
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let K := Q.1.toLabelledBoundedKernel
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  apply variableFin_heq_of_card_eq_of_val_eq
    (D.profile_length_recoveredKernelEdgeCoordinatePerm K Q.2 hDQ e).symm
  exact P.globalRecoveredAlignedCastDatum_recoveredPathIndexEquiv_val
    hell Q hG e i

/-- Expressing the target datum in the recovered coordinates of the globally
aligned cast datum changes nothing. -/
theorem globalRecoveredAlignedCastDatum_recoveredCoordinateAlignedDatum
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).recoveredCoordinateAlignedDatum
          Q.1.toLabelledBoundedKernel Q.2
          (P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG) =
      Q.2 := by
  rcases Q with ⟨QK, ⟨qprofile, qlabels⟩⟩
  let Q : BoundedKernelPresentation k ell :=
    ⟨QK, ⟨qprofile, qlabels⟩⟩
  let D := P.globalRecoveredAlignedCastDatum hell Q hG
  let K := QK.toLabelledBoundedKernel
  let hDQ :=
    P.globalRecoveredAlignedCastDatum_graph_eq_target hell Q hG
  have hprofile :=
    P.globalRecoveredAlignedCastDatum_profile hell Q hG
  have hedge :=
    P.globalRecoveredAlignedCastDatum_recoveredKernelEdgeCoordinatePerm
      hell Q hG
  change D.profile = qprofile at hprofile
  change
    (⟨D.profile, D.recoveredCoordinateAlignedLabels K ⟨qprofile, qlabels⟩ hDQ⟩ :
      BoundedKernelSubdivisionDatum k K) = ⟨qprofile, qlabels⟩
  congr 1
  have hlabels :
      D.recoveredCoordinateAlignedLabels K ⟨qprofile, qlabels⟩ hDQ =
        (boundedKernelSubdivisionSlotEquivOfProfileEq hprofile).trans
          qlabels := by
    apply Equiv.ext
    intro z
    change D.recoveredCoordinateAlignedLabels K ⟨qprofile, qlabels⟩ hDQ z =
      qlabels (boundedKernelSubdivisionSlotEquivOfProfileEq hprofile z)
    cases z with
    | inl v =>
        rw [boundedKernelSubdivisionSlotEquivOfProfileEq_inl]
        change D.recoveredCoordinateAlignedLabels
            K ⟨qprofile, qlabels⟩ hDQ (.inl v) =
          qlabels (.inl v)
        rw [D.recoveredCoordinateAlignedLabels_branch]
        have hv :=
          P.globalRecoveredAlignedCastDatum_branchLabel hell Q hG v
        simpa only [Q, BoundedKernelSubdivisionDatum.branchLabel] using hv
    | inr s =>
        rcases s with ⟨e, i⟩
        rw [boundedKernelSubdivisionSlotEquivOfProfileEq_inr]
        rw [D.recoveredCoordinateAlignedLabels_path]
        let s1 : BoundedKernelSubdivisionSlot qprofile :=
          .inr ⟨D.recoveredKernelEdgeCoordinatePerm
              K ⟨qprofile, qlabels⟩ hDQ e,
            D.recoveredPathIndexEquiv K ⟨qprofile, qlabels⟩ hDQ e i⟩
        let s2 : BoundedKernelSubdivisionSlot qprofile :=
          .inr ⟨e,
            cast (congrArg (fun N ↦ Fin (N.length e).val) hprofile) i⟩
        change qlabels s1 = qlabels s2
        apply congrArg qlabels
        dsimp only [s1, s2]
        apply congrArg Sum.inr
        apply Sigma.ext
        · have hedgeAt := congrArg (fun sigma => sigma e) hedge
          simpa only [Equiv.refl_apply] using hedgeAt
        ·
          have hindex :=
            P.globalRecoveredAlignedCastDatum_recoveredPathIndexEquiv_heq
              hell Q hG e i
          have hcast :=
            eqRec_heq
              (φ := fun T : Type ↦ T)
              (congrArg (fun N ↦ Fin (N.length e).val) hprofile) i
          exact hindex.trans hcast.symm
  exact (heq_of_eq hlabels).trans
    (boundedKernelSubdivisionSlotEquivOfProfileEq_trans_heq
      hprofile qlabels)

end BoundedKernelPresentation

end PerronWright.GraphCore
