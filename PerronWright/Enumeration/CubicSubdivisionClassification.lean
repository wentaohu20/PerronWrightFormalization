import PerronWright.Enumeration.ActualCubicSubdivisionForward
import PerronWright.Enumeration.CubicSubdivisionConnectivityConverse
import PerronWright.Enumeration.CubicReconstructionFibreBound
import PerronWright.Enumeration.CoreAttachmentChooseClassification

/-!
# Cubic admissible cores are exactly reconstructed subdivisions

This file connects the intrinsic cubic-subdivision classification to the
ordered admissible cores which occur in the exact fixed-surplus composition
formula.  It makes no assertion about an automorphism factor.  The existing
fibre theorem is used only in its proved form: after a normalized cubic
kernel has been fixed, every labelled reconstruction fibre admits a uniform
finite upper bound.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- An admissible ordered two-core is cubic when every branching vertex has
degree three.  Degree-two subdivision vertices are deliberately retained. -/
def IsCubicAdmissibleAttachmentCore (k ell : ℕ)
    (G : SimpleGraph (Fin k)) : Prop :=
  IsAdmissibleAttachmentCore k ell G ∧
    ∀ v ∈ branchingVertices G, G.degree v = 3

/-- The minimum-degree form of the full-two-core condition used by the
cubic reconstruction library. -/
theorem minDegree_two_of_isTwoCore_univ
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (hcore : IsTwoCore G Set.univ) :
    ∀ v, 2 ≤ G.degree v := by
  classical
  intro v
  obtain ⟨x, -, y, -, hxy, hvx, hvy⟩ := hcore v (Set.mem_univ v)
  have hcard : 1 < (G.neighborFinset v).card :=
    Finset.one_lt_card_iff.mpr
      ⟨x, y, (G.mem_neighborFinset v x).mpr hvx,
        (G.mem_neighborFinset v y).mpr hvy, hxy⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  omega

/-- For positive surplus, the cubic ordered cores in the exact attachment
decomposition are precisely the labelled simple graphs reconstructed from
an admissible subdivision of a connected edge-labelled cubic kernel.

The forward implication uses the actual branch vertices, suppressed edges,
path lengths, and Hamilton orders extracted from `G`.  The reverse
implication uses the already proved intrinsic recovery of branch labels; no
classification or multiplicity hypothesis is introduced here. -/
theorem isCubicAdmissibleAttachmentCore_iff_exists_reconstruction
    {k ell : ℕ} (hell : 0 < ell) (G : SimpleGraph (Fin k)) :
    IsCubicAdmissibleAttachmentCore k ell G ↔
      ∃ (K : LabelledConnectedCubicKernel ell)
        (D : CubicKernelSubdivisionDatum k ell K.graph),
        D.reconstructedGraph = G := by
  classical
  constructor
  · rintro ⟨hG, hcubic⟩
    have hconn : G.Connected := hG.1
    have hmin : ∀ v, 2 ≤ G.degree v :=
      minDegree_two_of_isTwoCore_univ hG.2.1
    have hs : G.edgeFinset.card = k + ell := hG.2.2
    obtain ⟨_eB, _eE, L, labels, _hend, _hcomponentLength,
        _hdirectLength, _hbranchLabels, _hinternalDegree, hrec⟩ :=
      exists_actual_cubic_subdivision_labels
        G hconn hmin hell hs hcubic
    let H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell) :=
      normalizedCubicFiniteMultiGraph G hconn hmin hell
        (by simpa using hs) hcubic
    let D : CubicKernelSubdivisionDatum k ell H :=
      { profile := L, labels := labels }
    have hrec' : D.reconstructedGraph = G := by
      simpa only [D, H] using hrec
    have hsupport : (finiteMultiGraphSupportGraph H).Connected := by
      apply D.kernelSupport_connected_of_reconstructed
      rw [hrec']
      exact hconn
    let K : LabelledConnectedCubicKernel ell :=
      { graph := H
        cubic := by
          intro v
          exact normalizedCubicFiniteMultiGraph_degree
            G hconn hmin hell (by simpa using hs) hcubic v
        connected := hsupport }
    refine ⟨K, ?_, ?_⟩
    · simpa only [K] using D
    · change D.reconstructedGraph = G
      exact hrec'
  · rintro ⟨K, D, hrec⟩
    have hadm := D.reconstructedGraph_admissible K
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa only [hrec] using hadm.1
    · intro v _
      have hmin := hadm.2.1 v
      rw [hrec] at hmin
      have hcard : 1 < (G.neighborFinset v).card := by
        rw [G.card_neighborFinset_eq_degree]
        omega
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp hcard
      exact ⟨x, Set.mem_univ x, y, Set.mem_univ y, hxy,
        (G.mem_neighborFinset v x).mp hx,
        (G.mem_neighborFinset v y).mp hy⟩
    · rw [← hrec]
      exact hadm.2.2
    · intro v hv
      have hv' : v ∈ branchingVertices D.reconstructedGraph := by
        simpa only [hrec] using hv
      obtain ⟨u, hu⟩ :=
        (D.mem_branchingVertices_iff_exists_branchLabel K v).mp hv'
      have hthree := D.branchVertex_degree_eq_three K u
      rw [← hrec, hu]
      exact hthree

/-- Subdivision data over one fixed normalized cubic kernel which reconstruct
a prescribed labelled graph. -/
abbrev CubicReconstructionFibreOverGraph
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (G : SimpleGraph (Fin k)) :=
  {D : CubicKernelSubdivisionDatum k ell K.graph //
    D.reconstructedGraph = G}

/-- If one point of a fixed-kernel reconstruction fibre is known, the fibre
over the target graph is equivalent to the base-point formulation used by
`CubicReconstructionFibre`. -/
noncomputable def cubicReconstructionFibreOverGraphEquiv
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (G : SimpleGraph (Fin k))
    (D₀ : CubicKernelSubdivisionDatum k ell K.graph)
    (hD₀ : D₀.reconstructedGraph = G) :
    CubicReconstructionFibreOverGraph K G ≃
      CubicReconstructionFibre K D₀ where
  toFun E := ⟨E.1, hD₀.trans E.2.symm⟩
  invFun E := ⟨E.1, E.2.symm.trans hD₀⟩
  left_inv _E := Subtype.ext rfl
  right_inv _E := Subtype.ext rfl

/-- The existing coordinate-and-loop bound, rewritten for the literal fibre
over a prescribed labelled cubic core.  This is still a fixed-kernel bound;
it intentionally does not pretend that normalized kernel coordinates have a
canonical global automorphism factor. -/
theorem cubicReconstructionFibreOverGraph_natCard_le
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (G : SimpleGraph (Fin k))
    (D₀ : CubicKernelSubdivisionDatum k ell K.graph)
    (hD₀ : D₀.reconstructedGraph = G) :
    Nat.card (CubicReconstructionFibreOverGraph K G) ≤
      (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge K.graph) := by
  let e := cubicReconstructionFibreOverGraphEquiv K G D₀ hD₀
  let _ : Finite (CubicReconstructionFibreOverGraph K G) :=
    Finite.of_equiv (CubicReconstructionFibre K D₀) e.symm
  rw [Nat.card_congr
    e]
  exact D₀.reconstructionFibre_natCard_le K

end PerronWright.GraphCore
