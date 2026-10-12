import PerronWright.Enumeration.VariableKernelCoordinateReconstruction
import PerronWright.Enumeration.VariableFixedCoordinateFibre

/-!
# Coordinate and loop symmetry of bounded-kernel presentations

This module packages the two exact symmetries already constructed: global
branch/edge coordinate relabelling and independent reversal of every loop
path.  The action is defined on the genuine sigma type of connected bounded
kernels and subdivision data, and it preserves the reconstructed labelled
simple graph literally.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A connected bounded kernel together with a labelled admissible
subdivision datum. -/
abbrev BoundedKernelPresentation (k ell : ℕ) :=
  Σ K : LabelledConnectedBoundedKernel ell,
    BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel

namespace BoundedKernelPresentation

/-- The loop set selected by a Boolean coordinate code. -/
def sourceLoopSet
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    Finset (BoundedKernelLoopEdge P.1.toLabelledBoundedKernel) :=
  Finset.univ.filter fun e ↦ c.2 e

/-- Transport the selected source loop set to the relabelled edge
coordinates. -/
def targetLoopSet
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    Finset (BoundedKernelLoopEdge
      (P.1.toLabelledBoundedKernel.coordinateRelabel c.1)) :=
  (P.sourceLoopSet c).map
    (boundedKernelLoopEdgeCoordinateRelabelEquiv
      P.1.toLabelledBoundedKernel c.1).toEmbedding

/-- Apply simultaneous coordinate relabelling and then the transported loop
orientation choices. -/
noncomputable def applySymmetry
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    BoundedKernelPresentation k ell :=
  let K' := P.1.coordinateRelabel c.1
  let D' := (P.2.coordinateRelabel c.1).reverseLoops (P.targetLoopSet c)
  ⟨K', D'⟩

@[simp] theorem applySymmetry_kernel
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    (P.applySymmetry c).1 = P.1.coordinateRelabel c.1 :=
  rfl

@[simp] theorem sourceLoopSet_mem
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel)
    (e : BoundedKernelLoopEdge P.1.toLabelledBoundedKernel) :
    e ∈ P.sourceLoopSet c ↔ c.2 e = true := by
  simp [sourceLoopSet]

@[simp] theorem targetLoopSet_mem
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel)
    (e : BoundedKernelLoopEdge P.1.toLabelledBoundedKernel) :
    boundedKernelLoopEdgeCoordinateRelabelEquiv
        P.1.toLabelledBoundedKernel c.1 e ∈ P.targetLoopSet c ↔
      c.2 e = true := by
  simp [targetLoopSet]

/-- The combined symmetry preserves the reconstructed labelled graph. -/
@[simp] theorem applySymmetry_reconstructedGraph
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    (P.applySymmetry c).2.reconstructedGraph =
      P.2.reconstructedGraph := by
  change
    (((P.2.coordinateRelabel c.1).reverseLoops
      (P.targetLoopSet c)).reconstructedGraph) = _
  rw [(P.2.coordinateRelabel c.1).reverseLoops_reconstructedGraph,
    P.2.coordinateRelabel_reconstructedGraph]

/-- The literal global reconstruction fibre of bounded-kernel
presentations over one labelled graph. -/
abbrev ReconstructionFibre
    {k ell : ℕ} (G : SimpleGraph (Fin k)) :=
  {P : BoundedKernelPresentation k ell // P.2.reconstructedGraph = G}

/-- Every coordinate code produces an element of the same global
reconstruction fibre. -/
noncomputable def symmetryFibreMap
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel →
      ReconstructionFibre (ell := ell) G :=
  fun c ↦ ⟨P.1.applySymmetry c,
    (P.1.applySymmetry_reconstructedGraph c).trans P.2⟩

@[simp] theorem symmetryFibreMap_val
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (c : BoundedKernelCoordinateCode P.1.1.toLabelledBoundedKernel) :
    (symmetryFibreMap P c).1 = P.1.applySymmetry c :=
  rfl

/-- The source of the fibre map has exactly the intended global coordinate
multiplicity.  The next decoder module identifies this map with the full
fibre rather than merely its orbit. -/
theorem symmetryCode_card
    {k ell : ℕ} (P : BoundedKernelPresentation k ell) :
    Fintype.card
        (BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) =
      P.1.toLabelledBoundedKernel.coordinateMultiplicity :=
  boundedKernelCoordinateCode_card P.1.toLabelledBoundedKernel

end BoundedKernelPresentation

end PerronWright.GraphCore
