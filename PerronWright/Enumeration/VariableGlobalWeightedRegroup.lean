import PerronWright.Enumeration.ActualNoncubicSubdivisionForward
import PerronWright.Enumeration.VariableGlobalPresentationFibreEquiv
import PerronWright.Enumeration.VariableKernelNoncubicPresentationClassification

/-!
# Exact weighted regrouping of global noncubic bounded-kernel presentations

For positive surplus, every actual noncubic admissible core has a canonical
connected bounded-kernel presentation.  Conversely, every connected
strictly noncubic bounded-kernel presentation reconstructs such a core.
The global variable-kernel fibre equivalence therefore identifies the full
presentation fibre over one actual core with the coordinate-code space of
any chosen base presentation.

This file turns that classification into exact finite-sum identities.  In
particular, the multiplicity of one reconstructed core is the intrinsic
`coordinateMultiplicity` of its canonical bounded kernel.  Dividing every
presentation by that proved multiplicity recovers the literal sum over
actual labelled noncubic cores.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical BigOperators

namespace BoundedKernelPresentation

/-- The exact coordinate multiplicity attached to a variable-kernel
presentation. -/
def globalMultiplicity {k ell : ℕ}
    (P : BoundedKernelPresentation k ell) : ℕ :=
  P.1.toLabelledBoundedKernel.coordinateMultiplicity

theorem globalMultiplicity_pos {k ell : ℕ}
    (P : BoundedKernelPresentation k ell) :
    0 < P.globalMultiplicity :=
  P.1.toLabelledBoundedKernel.coordinateMultiplicity_pos

/-- The displayed coordinate multiplicity depends only on the reconstructed
labelled graph. -/
theorem globalMultiplicity_eq_of_reconstructedGraph_eq
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.globalMultiplicity = Q.globalMultiplicity := by
  let G : SimpleGraph (Fin k) := P.2.reconstructedGraph
  let P₀ : ReconstructionFibre (ell := ell) G := ⟨P, rfl⟩
  let Q₀ : ReconstructionFibre (ell := ell) G := ⟨Q, hG.symm⟩
  let FP : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase hell P₀
  let FQ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase hell Q₀
  have hcard :
      @Fintype.card (ReconstructionFibre (ell := ell) G) FP =
        @Fintype.card (ReconstructionFibre (ell := ell) G) FQ :=
    @Fintype.card_congr
      (ReconstructionFibre (ell := ell) G)
      (ReconstructionFibre (ell := ell) G) FP FQ
      (Equiv.refl _)
  calc
    P.globalMultiplicity =
        @Fintype.card (ReconstructionFibre (ell := ell) G) FP := by
      exact (reconstructionFibre_card_of_base hell P₀).symm
    _ = @Fintype.card (ReconstructionFibre (ell := ell) G) FQ := hcard
    _ = Q.globalMultiplicity := by
      exact reconstructionFibre_card_of_base hell Q₀

/-- A graph-invariant weight summed over one global variable-kernel fibre is
the exact coordinate multiplicity times the weight of its target graph. -/
theorem sum_reconstructionFibre_graphInvariant
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (W : SimpleGraph (Fin k) → R) :
    letI := reconstructionFibreFintypeOfBase hell P
    (∑ Q : ReconstructionFibre (ell := ell) G,
        W Q.1.2.reconstructedGraph) =
      P.1.globalMultiplicity • W G := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase hell P
  calc
    (∑ Q : ReconstructionFibre (ell := ell) G,
        W Q.1.2.reconstructedGraph) =
        ∑ _Q : ReconstructionFibre (ell := ell) G, W G := by
      apply Fintype.sum_congr
      intro Q
      rw [Q.2]
    _ = Fintype.card (ReconstructionFibre (ell := ell) G) • W G := by
      simp
    _ = P.1.globalMultiplicity • W G := by
      simpa only [globalMultiplicity] using
        congrArg (fun n : ℕ ↦ n • W G)
          (reconstructionFibre_card_of_base hell P)

/-- The reciprocal coordinate multiplicity counts one reconstructed graph
exactly once inside its full global presentation fibre. -/
theorem sum_reconstructionFibre_invMultiplicity_graphInvariant
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (W : SimpleGraph (Fin k) → 𝕜) :
    letI := reconstructionFibreFintypeOfBase hell P
    (∑ Q : ReconstructionFibre (ell := ell) G,
        (Q.1.globalMultiplicity : 𝕜)⁻¹ *
          W Q.1.2.reconstructedGraph) = W G := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase hell P
  have hmul (Q : ReconstructionFibre (ell := ell) G) :
      Q.1.globalMultiplicity = P.1.globalMultiplicity :=
    Q.1.globalMultiplicity_eq_of_reconstructedGraph_eq hell P.1
      (Q.2.trans P.2.symm)
  have hm0 : (P.1.globalMultiplicity : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt P.1.globalMultiplicity_pos)
  calc
    (∑ Q : ReconstructionFibre (ell := ell) G,
        (Q.1.globalMultiplicity : 𝕜)⁻¹ *
          W Q.1.2.reconstructedGraph) =
        ∑ _Q : ReconstructionFibre (ell := ell) G,
          (P.1.globalMultiplicity : 𝕜)⁻¹ * W G := by
      apply Fintype.sum_congr
      intro Q
      rw [hmul Q, Q.2]
    _ = Fintype.card (ReconstructionFibre (ell := ell) G) •
          ((P.1.globalMultiplicity : 𝕜)⁻¹ * W G) := by
      simp
    _ = P.1.globalMultiplicity •
          ((P.1.globalMultiplicity : 𝕜)⁻¹ * W G) := by
      simpa only [globalMultiplicity] using
        congrArg
          (fun n : ℕ ↦ n •
            ((P.1.globalMultiplicity : 𝕜)⁻¹ * W G))
          (reconstructionFibre_card_of_base hell P)
    _ = W G := by
      simp [nsmul_eq_mul, hm0]

/-- A bounded-kernel presentation of a noncubic reconstructed graph is
itself in the strict noncubic kernel range. -/
theorem kernelEdgeCount_lt_of_reconstructedGraph_isNoncubic
    {k ell : ℕ} (hell : 0 < ell)
    (P : BoundedKernelPresentation k ell)
    (hP : IsNoncubicAdmissibleAttachmentCore k ell
      P.2.reconstructedGraph) :
    P.1.toLabelledBoundedKernel.shape.2.1.val < 3 * ell := by
  calc
    P.1.toLabelledBoundedKernel.shape.2.1.val =
        Nat.card
          (Fin P.1.toLabelledBoundedKernel.shape.2.1.val) :=
      (Nat.card_fin _).symm
    _ = Nat.card (KernelEdgeLabel P.2.reconstructedGraph) :=
      (Nat.card_congr
        (P.2.recoveredKernelEdgeEquiv
          P.1.toLabelledBoundedKernel)).symm
    _ < 3 * ell :=
      kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic hell hP

end BoundedKernelPresentation

namespace ConnectedNoncubicBoundedKernelPresentation

/-- Forget the strict edge-count proof and regard a noncubic presentation as
a presentation in the ambient connected bounded-kernel type. -/
def toBoundedKernelPresentation {k ell : ℕ}
    (P : ConnectedNoncubicBoundedKernelPresentation k ell) :
    BoundedKernelPresentation k ell :=
  ⟨P.1.1, P.2⟩

@[simp] theorem toBoundedKernelPresentation_reconstructedGraph
    {k ell : ℕ}
    (P : ConnectedNoncubicBoundedKernelPresentation k ell) :
    P.toBoundedKernelPresentation.2.reconstructedGraph =
      P.2.reconstructedGraph :=
  rfl

/-- Exact multiplicity of the ambient global fibre containing a noncubic
presentation. -/
def globalMultiplicity {k ell : ℕ}
    (P : ConnectedNoncubicBoundedKernelPresentation k ell) : ℕ :=
  P.toBoundedKernelPresentation.globalMultiplicity

theorem globalMultiplicity_pos {k ell : ℕ}
    (P : ConnectedNoncubicBoundedKernelPresentation k ell) :
    0 < P.globalMultiplicity :=
  P.toBoundedKernelPresentation.globalMultiplicity_pos

end ConnectedNoncubicBoundedKernelPresentation

/-- A canonical base presentation of every actual noncubic admissible core.
Its kernel and length profile are the intrinsic suppressed data of the
actual graph. -/
noncomputable def noncubicAdmissibleAttachmentCoreBasePresentation
    {k ell : ℕ} (hell : 0 < ell)
    (G : NoncubicAdmissibleAttachmentCore k ell) :
    BoundedKernelPresentation.ReconstructionFibre
      (ell := ell) G.1 := by
  let K : LabelledConnectedBoundedKernel ell :=
    noncubicCoreConnectedBoundedKernel hell G
  let hexists := exists_actual_noncubic_subdivision_labels hell G
  let labels := Classical.choose hexists
  have hgraph := Classical.choose_spec hexists
  let D : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel :=
    { profile := noncubicCoreBoundedLengthProfile hell G
      labels := labels }
  exact ⟨⟨K, D⟩, by
    simpa [K, D, noncubicCoreConnectedBoundedKernel] using hgraph⟩

/-- A noncubic presentation together with its reconstructed actual core,
expressed using the full ambient reconstruction fibre. -/
abbrev NoncubicPresentationOverAdmissibleCore (k ell : ℕ) :=
  Σ G : NoncubicAdmissibleAttachmentCore k ell,
    BoundedKernelPresentation.ReconstructionFibre (ell := ell) G.1

/-- Connected strict-noncubic presentations are exactly the ambient
presentations lying over actual noncubic admissible cores. -/
noncomputable def connectedNoncubicBoundedKernelPresentationEquivOverAdmissibleCore
    {k ell : ℕ} (hell : 0 < ell) :
    ConnectedNoncubicBoundedKernelPresentation k ell ≃
      NoncubicPresentationOverAdmissibleCore k ell where
  toFun P :=
    ⟨⟨P.2.reconstructedGraph,
      P.reconstructedGraph_isNoncubicAdmissibleAttachmentCore hell⟩,
      ⟨P.toBoundedKernelPresentation, rfl⟩⟩
  invFun Q :=
    ⟨⟨Q.2.1.1,
      Q.2.1.kernelEdgeCount_lt_of_reconstructedGraph_isNoncubic hell
        (Q.2.2.symm ▸ Q.1.2)⟩,
      Q.2.1.2⟩
  left_inv P := by
    rcases P with ⟨⟨K, hK⟩, D⟩
    rfl
  right_inv Q := by
    rcases Q with ⟨⟨G, hG⟩, ⟨P, hP⟩⟩
    cases hP
    rfl

/-- The finite structure on presentations over actual noncubic cores,
built fibrewise from the proved global coordinate equivalence. -/
@[instance_reducible] noncomputable def
    noncubicPresentationOverAdmissibleCoreFintype
    {k ell : ℕ} (hell : 0 < ell) :
    Fintype (NoncubicPresentationOverAdmissibleCore k ell) := by
  let _ (G : NoncubicAdmissibleAttachmentCore k ell) :
      Fintype (BoundedKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    BoundedKernelPresentation.reconstructionFibreFintypeOfBase hell
      (noncubicAdmissibleAttachmentCoreBasePresentation hell G)
  infer_instance

/-- The induced finite structure on the raw noncubic presentation type. -/
@[instance_reducible] noncomputable def
    connectedNoncubicBoundedKernelPresentationFintype
    {k ell : ℕ} (_hell : 0 < ell) :
    Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) := by
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelSubdivisionDatum k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelSubdivisionDatumFintype k
      K.1.toLabelledBoundedKernel
  infer_instance

/-- The presentation fibre over an actual noncubic core has exactly the
coordinate multiplicity of its canonical bounded kernel. -/
theorem noncubicPresentationFibre_card_eq_base_coordinateMultiplicity
    {k ell : ℕ} (hell : 0 < ell)
    (G : NoncubicAdmissibleAttachmentCore k ell) :
    let P := noncubicAdmissibleAttachmentCoreBasePresentation hell G
    letI := BoundedKernelPresentation.reconstructionFibreFintypeOfBase hell P
    Fintype.card
        (BoundedKernelPresentation.ReconstructionFibre
          (ell := ell) G.1) =
      P.1.1.toLabelledBoundedKernel.coordinateMultiplicity := by
  dsimp only
  exact BoundedKernelPresentation.reconstructionFibre_card_of_base hell
    (noncubicAdmissibleAttachmentCoreBasePresentation hell G)

/-- Exact global regrouping of a reconstructed-graph invariant over all
connected noncubic bounded-kernel presentations. -/
theorem sum_connectedNoncubicPresentations_graphInvariant
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} (hell : 0 < ell)
    (W : SimpleGraph (Fin k) → R) :
    letI := connectedNoncubicBoundedKernelPresentationFintype
      (k := k) (ell := ell) hell
    (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
        W P.2.reconstructedGraph) =
      ∑ G : NoncubicAdmissibleAttachmentCore k ell,
        BoundedKernelPresentation.globalMultiplicity
          (noncubicAdmissibleAttachmentCoreBasePresentation hell G).1 •
            W G.1 := by
  let _ (G : NoncubicAdmissibleAttachmentCore k ell) :
      Fintype (BoundedKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    BoundedKernelPresentation.reconstructionFibreFintypeOfBase hell
      (noncubicAdmissibleAttachmentCoreBasePresentation hell G)
  let _ : Fintype (NoncubicPresentationOverAdmissibleCore k ell) := by
    infer_instance
  let _ : Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) :=
    connectedNoncubicBoundedKernelPresentationFintype hell
  let e : ConnectedNoncubicBoundedKernelPresentation k ell ≃
      NoncubicPresentationOverAdmissibleCore k ell :=
    connectedNoncubicBoundedKernelPresentationEquivOverAdmissibleCore hell
  calc
    (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
        W P.2.reconstructedGraph) =
        ∑ Q : NoncubicPresentationOverAdmissibleCore k ell,
          W Q.1.1 := by
      exact Fintype.sum_equiv e
        (fun P : ConnectedNoncubicBoundedKernelPresentation k ell ↦
          W P.2.reconstructedGraph)
        (fun Q : NoncubicPresentationOverAdmissibleCore k ell ↦ W Q.1.1)
        (by intro P; rfl)
    _ = ∑ G : NoncubicAdmissibleAttachmentCore k ell,
          ∑ _Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W G.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ G : NoncubicAdmissibleAttachmentCore k ell,
        BoundedKernelPresentation.globalMultiplicity
          (noncubicAdmissibleAttachmentCoreBasePresentation hell G).1 •
            W G.1 := by
      apply Fintype.sum_congr
      intro G
      calc
        (∑ _Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W G.1) =
            ∑ Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W Q.1.2.reconstructedGraph := by
          apply Fintype.sum_congr
          intro Q
          rw [Q.2]
        _ = BoundedKernelPresentation.globalMultiplicity
              (noncubicAdmissibleAttachmentCoreBasePresentation hell G).1 •
                W G.1 :=
          BoundedKernelPresentation.sum_reconstructionFibre_graphInvariant
            hell
            (noncubicAdmissibleAttachmentCoreBasePresentation hell G) W

/-- After division by the exact variable coordinate multiplicity, the
global presentation sum is literally the sum over actual labelled
noncubic cores. -/
theorem sum_connectedNoncubicPresentations_invMultiplicity_graphInvariant
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} (hell : 0 < ell)
    (W : SimpleGraph (Fin k) → 𝕜) :
    letI := connectedNoncubicBoundedKernelPresentationFintype
      (k := k) (ell := ell) hell
    (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ *
          W P.2.reconstructedGraph) =
      ∑ G : NoncubicAdmissibleAttachmentCore k ell, W G.1 := by
  let _ (G : NoncubicAdmissibleAttachmentCore k ell) :
      Fintype (BoundedKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    BoundedKernelPresentation.reconstructionFibreFintypeOfBase hell
      (noncubicAdmissibleAttachmentCoreBasePresentation hell G)
  let _ : Fintype (NoncubicPresentationOverAdmissibleCore k ell) := by
    infer_instance
  let _ : Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) :=
    connectedNoncubicBoundedKernelPresentationFintype hell
  let e : ConnectedNoncubicBoundedKernelPresentation k ell ≃
      NoncubicPresentationOverAdmissibleCore k ell :=
    connectedNoncubicBoundedKernelPresentationEquivOverAdmissibleCore hell
  calc
    (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ *
          W P.2.reconstructedGraph) =
        ∑ Q : NoncubicPresentationOverAdmissibleCore k ell,
          (Q.2.1.globalMultiplicity : 𝕜)⁻¹ * W Q.1.1 := by
      exact Fintype.sum_equiv e
        (fun P : ConnectedNoncubicBoundedKernelPresentation k ell ↦
          (P.globalMultiplicity : 𝕜)⁻¹ *
            W P.2.reconstructedGraph)
        (fun Q : NoncubicPresentationOverAdmissibleCore k ell ↦
          (Q.2.1.globalMultiplicity : 𝕜)⁻¹ * W Q.1.1)
        (by intro P; rfl)
    _ = ∑ G : NoncubicAdmissibleAttachmentCore k ell,
          ∑ Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
            (Q.1.globalMultiplicity : 𝕜)⁻¹ * W G.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ G : NoncubicAdmissibleAttachmentCore k ell, W G.1 := by
      apply Fintype.sum_congr
      intro G
      calc
        (∑ Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
            (Q.1.globalMultiplicity : 𝕜)⁻¹ * W G.1) =
            ∑ Q : BoundedKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
              (Q.1.globalMultiplicity : 𝕜)⁻¹ *
                W Q.1.2.reconstructedGraph := by
          apply Fintype.sum_congr
          intro Q
          rw [Q.2]
        _ = W G.1 :=
          BoundedKernelPresentation.sum_reconstructionFibre_invMultiplicity_graphInvariant
            hell (noncubicAdmissibleAttachmentCoreBasePresentation hell G) W

end PerronWright.GraphCore
