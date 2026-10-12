import PerronWright.Enumeration.CubicGlobalPresentationFibreEquiv
import PerronWright.Enumeration.CubicSubdivisionClassification

/-!
# Exact weighted regrouping of global cubic presentations

For positive surplus, every cubic admissible attachment core has a global
kernel presentation.  The exact global fibre theorem identifies all of its
presentations with branch-coordinate permutations, kernel-edge-coordinate
permutations, and independent loop reversals.  Consequently its exact
presentation multiplicity is

`(2 * ell)! * (3 * ell)! * 2 ^ (# loop edge labels)`.

This file turns that fibre statement into finite-sum identities.  The first
identity groups an arbitrary reconstructed-graph invariant over all global
presentations.  The second assigns every presentation the reciprocal of its
exact multiplicity and therefore recovers the literal sum over cubic
admissible labelled cores.  No automorphism factor or unproved orbit
interface is introduced.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical BigOperators

namespace CubicKernelPresentation

/-- The exact size of the global reconstruction fibre containing `P`. -/
def globalMultiplicity {k ell : ℕ}
    (P : CubicKernelPresentation k ell) : ℕ :=
  (2 * ell).factorial * (3 * ell).factorial *
    2 ^ Fintype.card (CubicKernelLoopEdge P.1.graph)

theorem globalMultiplicity_pos {k ell : ℕ}
    (P : CubicKernelPresentation k ell) :
    0 < P.globalMultiplicity := by
  unfold globalMultiplicity
  positivity

/-- The exact multiplicity is intrinsic to the reconstructed labelled graph,
even though its displayed formula is written using one kernel presentation. -/
theorem globalMultiplicity_eq_of_reconstructedGraph_eq
    {k ell : ℕ} (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.globalMultiplicity = Q.globalMultiplicity := by
  let G : SimpleGraph (Fin k) := P.2.reconstructedGraph
  let P₀ : ReconstructionFibre (ell := ell) G := ⟨P, rfl⟩
  let Q₀ : ReconstructionFibre (ell := ell) G := ⟨Q, hG.symm⟩
  let FP : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase P₀
  let FQ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase Q₀
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
      exact (reconstructionFibre_card_of_base P₀).symm
    _ = @Fintype.card (ReconstructionFibre (ell := ell) G) FQ := hcard
    _ = Q.globalMultiplicity := by
      exact reconstructionFibre_card_of_base Q₀

/-- A graph-invariant weight summed over one global reconstruction fibre is
the exact presentation multiplicity times the weight of the target graph. -/
theorem sum_reconstructionFibre_graphInvariant
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (W : SimpleGraph (Fin k) → R) :
    letI := reconstructionFibreFintypeOfBase P
    (∑ Q : ReconstructionFibre (ell := ell) G,
        W Q.1.2.reconstructedGraph) =
      P.1.globalMultiplicity • W G := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase P
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
          (reconstructionFibre_card_of_base P)

/-- Weighting each presentation in one fibre by the reciprocal of its exact
multiplicity counts the reconstructed graph exactly once. -/
theorem sum_reconstructionFibre_invMultiplicity_graphInvariant
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (W : SimpleGraph (Fin k) → 𝕜) :
    letI := reconstructionFibreFintypeOfBase P
    (∑ Q : ReconstructionFibre (ell := ell) G,
        (Q.1.globalMultiplicity : 𝕜)⁻¹ *
          W Q.1.2.reconstructedGraph) = W G := by
  let _ : Fintype (ReconstructionFibre (ell := ell) G) :=
    reconstructionFibreFintypeOfBase P
  have hmul (Q : ReconstructionFibre (ell := ell) G) :
      Q.1.globalMultiplicity = P.1.globalMultiplicity :=
    Q.1.globalMultiplicity_eq_of_reconstructedGraph_eq P.1
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
          (fun n : ℕ ↦ n • ((P.1.globalMultiplicity : 𝕜)⁻¹ * W G))
          (reconstructionFibre_card_of_base P)
    _ = W G := by
      simp [nsmul_eq_mul, hm0]

end CubicKernelPresentation

/-- Labelled cubic admissible attachment cores of fixed size and surplus. -/
abbrev CubicAdmissibleAttachmentCore (k ell : ℕ) :=
  {G : SimpleGraph (Fin k) // IsCubicAdmissibleAttachmentCore k ell G}

/-- The classification theorem supplies a canonical (choice-dependent) base
presentation for every cubic admissible core at positive surplus. -/
noncomputable def cubicAdmissibleAttachmentCoreBasePresentation
    {k ell : ℕ} (hell : 0 < ell)
    (G : CubicAdmissibleAttachmentCore k ell) :
    CubicKernelPresentation.ReconstructionFibre (ell := ell) G.1 := by
  let hex := (isCubicAdmissibleAttachmentCore_iff_exists_reconstruction
    hell G.1).mp G.2
  let K := Classical.choose hex
  let hK := Classical.choose_spec hex
  let D := Classical.choose hK
  exact ⟨⟨K, D⟩, Classical.choose_spec hK⟩

/-- A global presentation together with its (necessarily cubic admissible)
reconstructed core.  This dependent form is the exact codomain needed for
fibrewise regrouping. -/
abbrev CubicPresentationOverAdmissibleCore (k ell : ℕ) :=
  Σ G : CubicAdmissibleAttachmentCore k ell,
    CubicKernelPresentation.ReconstructionFibre (ell := ell) G.1

/-- For positive surplus, raw global cubic presentations are exactly the
presentations lying over cubic admissible attachment cores. -/
noncomputable def cubicKernelPresentationEquivOverAdmissibleCore
    {k ell : ℕ} (hell : 0 < ell) :
    CubicKernelPresentation k ell ≃
      CubicPresentationOverAdmissibleCore k ell where
  toFun P :=
    ⟨⟨P.2.reconstructedGraph,
      (isCubicAdmissibleAttachmentCore_iff_exists_reconstruction
        hell P.2.reconstructedGraph).2 ⟨P.1, P.2, rfl⟩⟩,
      ⟨P, rfl⟩⟩
  invFun Q := Q.2.1
  left_inv _P := rfl
  right_inv Q := by
    rcases Q with ⟨⟨G, hG⟩, ⟨P, hP⟩⟩
    cases hP
    rfl

/-- The finite structure on all presentations over cubic admissible cores,
built fibrewise from the exact symmetry equivalence. -/
@[instance_reducible] noncomputable def cubicPresentationOverAdmissibleCoreFintype
    {k ell : ℕ} (hell : 0 < ell) :
    Fintype (CubicPresentationOverAdmissibleCore k ell) := by
  let _ (G : CubicAdmissibleAttachmentCore k ell) :
      Fintype (CubicKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    CubicKernelPresentation.reconstructionFibreFintypeOfBase
      (cubicAdmissibleAttachmentCoreBasePresentation hell G)
  infer_instance

/-- The induced finite structure on the raw global presentation type. -/
@[instance_reducible] noncomputable def cubicKernelPresentationFintype
    {k ell : ℕ} (hell : 0 < ell) :
    Fintype (CubicKernelPresentation k ell) := by
  letI : Fintype (CubicPresentationOverAdmissibleCore k ell) :=
    cubicPresentationOverAdmissibleCoreFintype hell
  exact Fintype.ofEquiv (CubicPresentationOverAdmissibleCore k ell)
    (cubicKernelPresentationEquivOverAdmissibleCore hell).symm

/-- Exact global regrouping: a reconstructed-graph invariant summed over all
kernel presentations is the sum over cubic admissible cores, each multiplied
by its exact global presentation multiplicity. -/
theorem sum_cubicKernelPresentations_graphInvariant
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} (hell : 0 < ell)
    (W : SimpleGraph (Fin k) → R) :
    letI := cubicKernelPresentationFintype (k := k) (ell := ell) hell
    (∑ P : CubicKernelPresentation k ell,
        W P.2.reconstructedGraph) =
      ∑ G : CubicAdmissibleAttachmentCore k ell,
        (cubicAdmissibleAttachmentCoreBasePresentation hell G).1.globalMultiplicity •
          W G.1 := by
  let _ (G : CubicAdmissibleAttachmentCore k ell) :
      Fintype (CubicKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    CubicKernelPresentation.reconstructionFibreFintypeOfBase
      (cubicAdmissibleAttachmentCoreBasePresentation hell G)
  let _ : Fintype (CubicPresentationOverAdmissibleCore k ell) := by
    infer_instance
  let _ : Fintype (CubicKernelPresentation k ell) :=
    cubicKernelPresentationFintype (k := k) (ell := ell) hell
  let e : CubicKernelPresentation k ell ≃
      CubicPresentationOverAdmissibleCore k ell :=
    cubicKernelPresentationEquivOverAdmissibleCore
      (k := k) (ell := ell) hell
  calc
    (∑ P : CubicKernelPresentation k ell,
        W P.2.reconstructedGraph) =
        ∑ Q : CubicPresentationOverAdmissibleCore k ell, W Q.1.1 := by
      exact Fintype.sum_equiv e
        (fun P : CubicKernelPresentation k ell ↦
          W P.2.reconstructedGraph)
        (fun Q : CubicPresentationOverAdmissibleCore k ell ↦ W Q.1.1)
        (by intro P; rfl)
    _ = ∑ G : CubicAdmissibleAttachmentCore k ell,
          ∑ _Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W G.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ G : CubicAdmissibleAttachmentCore k ell,
        (cubicAdmissibleAttachmentCoreBasePresentation hell G).1.globalMultiplicity •
          W G.1 := by
      apply Fintype.sum_congr
      intro G
      calc
        (∑ _Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W G.1) =
            ∑ Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1, W Q.1.2.reconstructedGraph := by
          apply Fintype.sum_congr
          intro Q
          rw [Q.2]
        _ = (cubicAdmissibleAttachmentCoreBasePresentation hell G).1.globalMultiplicity •
              W G.1 :=
          CubicKernelPresentation.sum_reconstructionFibre_graphInvariant
            (cubicAdmissibleAttachmentCoreBasePresentation hell G) W

/-- Exact normalized regrouping: after division by the proved presentation
multiplicity, the global presentation sum is literally the graph sum over
cubic admissible labelled cores. -/
theorem sum_cubicKernelPresentations_invMultiplicity_graphInvariant
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} (hell : 0 < ell)
    (W : SimpleGraph (Fin k) → 𝕜) :
    letI := cubicKernelPresentationFintype (k := k) (ell := ell) hell
    (∑ P : CubicKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ *
          W P.2.reconstructedGraph) =
      ∑ G : CubicAdmissibleAttachmentCore k ell, W G.1 := by
  let _ (G : CubicAdmissibleAttachmentCore k ell) :
      Fintype (CubicKernelPresentation.ReconstructionFibre
        (ell := ell) G.1) :=
    CubicKernelPresentation.reconstructionFibreFintypeOfBase
      (cubicAdmissibleAttachmentCoreBasePresentation hell G)
  let _ : Fintype (CubicPresentationOverAdmissibleCore k ell) := by
    infer_instance
  let _ : Fintype (CubicKernelPresentation k ell) :=
    cubicKernelPresentationFintype (k := k) (ell := ell) hell
  let e : CubicKernelPresentation k ell ≃
      CubicPresentationOverAdmissibleCore k ell :=
    cubicKernelPresentationEquivOverAdmissibleCore
      (k := k) (ell := ell) hell
  calc
    (∑ P : CubicKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ *
          W P.2.reconstructedGraph) =
        ∑ Q : CubicPresentationOverAdmissibleCore k ell,
          (Q.2.1.globalMultiplicity : 𝕜)⁻¹ * W Q.1.1 := by
      exact Fintype.sum_equiv e
        (fun P : CubicKernelPresentation k ell ↦
          (P.globalMultiplicity : 𝕜)⁻¹ *
            W P.2.reconstructedGraph)
        (fun Q : CubicPresentationOverAdmissibleCore k ell ↦
          (Q.2.1.globalMultiplicity : 𝕜)⁻¹ * W Q.1.1)
        (by intro P; rfl)
    _ = ∑ G : CubicAdmissibleAttachmentCore k ell,
          ∑ Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
            (Q.1.globalMultiplicity : 𝕜)⁻¹ * W G.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ G : CubicAdmissibleAttachmentCore k ell, W G.1 := by
      apply Fintype.sum_congr
      intro G
      calc
        (∑ Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
            (Q.1.globalMultiplicity : 𝕜)⁻¹ * W G.1) =
            ∑ Q : CubicKernelPresentation.ReconstructionFibre
              (ell := ell) G.1,
              (Q.1.globalMultiplicity : 𝕜)⁻¹ *
                W Q.1.2.reconstructedGraph := by
          apply Fintype.sum_congr
          intro Q
          rw [Q.2]
        _ = W G.1 :=
          CubicKernelPresentation.sum_reconstructionFibre_invMultiplicity_graphInvariant
            (cubicAdmissibleAttachmentCoreBasePresentation hell G) W

end PerronWright.GraphCore
