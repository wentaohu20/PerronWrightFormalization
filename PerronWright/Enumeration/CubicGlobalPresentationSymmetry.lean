import PerronWright.Enumeration.CubicKernelCoordinateReconstruction
import PerronWright.Enumeration.CubicFixedCoordinateFibre
import Mathlib.Data.Fintype.Perm

/-!
# Coordinate and loop symmetries of global cubic presentations

A presentation consists of an edge-labelled connected cubic kernel together
with one admissible labelled subdivision datum over that kernel.  Passing to
this sigma type is essential: a coordinate permutation changes the endpoint
table, so it does not act within the datum type over one fixed kernel.

This file records the part of the global symmetry calculation which follows
from the presently proved interfaces.  Coordinate transport and subsequent
loop reversal preserve the reconstructed labelled graph.  The dependent
space of choices has cardinality

`(2 * ell)! * (3 * ell)! * 2 ^ (# loop edge labels)`.

The last statement counts *codes*, not distinct points of an orbit.  No
injectivity or global reconstruction-fibre equality is asserted here.  Those
claims require a cross-kernel recovered-coordinate converse and the action
laws for successive coordinate transports.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A globally coordinated cubic presentation: both the normalized kernel
and a fully labelled admissible subdivision datum over that kernel. -/
abbrev CubicKernelPresentation (k ell : ℕ) :=
  Σ K : LabelledConnectedCubicKernel ell,
    CubicKernelSubdivisionDatum k ell K.graph

namespace CubicKernelPresentation

/-- Simultaneously relabel the branch and kernel-edge coordinates of a
global presentation.  The datum is transported over the relabelled endpoint
table, so this map is well typed without identifying two fixed-kernel datum
types. -/
noncomputable def coordinateRelabel {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (γ : CubicKernelCoordinatePerm ell) :
    CubicKernelPresentation k ell :=
  ⟨P.1.coordinateRelabel γ, P.2.coordinateRelabel γ⟩

@[simp]
theorem coordinateRelabel_kernel {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (γ : CubicKernelCoordinatePerm ell) :
    (P.coordinateRelabel γ).1 = P.1.coordinateRelabel γ :=
  rfl

@[simp]
theorem coordinateRelabel_reconstructedGraph {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (γ : CubicKernelCoordinatePerm ell) :
    (P.coordinateRelabel γ).2.reconstructedGraph =
      P.2.reconstructedGraph :=
  P.2.coordinateRelabel_reconstructedGraph γ

/-- Presentations which reconstruct one fixed labelled simple graph. -/
abbrev ReconstructionFibre {k ell : ℕ}
    (G : SimpleGraph (Fin k)) :=
  {P : CubicKernelPresentation k ell //
    P.2.reconstructedGraph = G}

/-- Coordinate transport restricts to every global reconstruction fibre. -/
noncomputable def coordinateRelabelInFibre {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (γ : CubicKernelCoordinatePerm ell) :
    ReconstructionFibre (ell := ell) G :=
  ⟨P.1.coordinateRelabel γ, by
    rw [coordinateRelabel_reconstructedGraph]
    exact P.2⟩

/-- After choosing new kernel coordinates, choose independently which loop
paths in the transported kernel are reversed.  The loop type is deliberately
dependent on `γ`; kernels with different endpoint tables do not have one
definitionally common loop-edge type. -/
def SymmetryCode {k ell : ℕ}
    (P : CubicKernelPresentation k ell) :=
  Σ γ : CubicKernelCoordinatePerm ell,
    Finset (CubicKernelLoopEdge (P.1.coordinateRelabel γ).graph)

/-- The dependent space of coordinate and loop-reversal codes is finite. -/
noncomputable instance symmetryCodeFintype {k ell : ℕ}
    (P : CubicKernelPresentation k ell) : Fintype P.SymmetryCode := by
  unfold SymmetryCode
  infer_instance

/-- Apply a coordinate transport and then the selected loop reversals. -/
noncomputable def applySymmetry {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) :
    CubicKernelPresentation k ell :=
  ⟨P.1.coordinateRelabel c.1,
    (P.2.coordinateRelabel c.1).reverseLoops c.2⟩

/-- Every dependent coordinate-and-loop code preserves the reconstructed
labelled graph. -/
@[simp]
theorem applySymmetry_reconstructedGraph {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode) :
    (P.applySymmetry c).2.reconstructedGraph =
      P.2.reconstructedGraph := by
  rcases P with ⟨K, D⟩
  rcases c with ⟨γ, A⟩
  change
    Finset (CubicKernelLoopEdge
      (finiteMultiGraphCoordinateRelabel γ K.graph)) at A
  change
    ((D.coordinateRelabel γ).reverseLoops A).reconstructedGraph =
      D.reconstructedGraph
  rw [CubicKernelSubdivisionDatum.reverseLoops_reconstructedGraph,
    CubicKernelSubdivisionDatum.coordinateRelabel_reconstructedGraph]

/-- The two-stage symmetry map also restricts to every global reconstruction
fibre. -/
noncomputable def applySymmetryInFibre {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (c : P.1.SymmetryCode) :
    ReconstructionFibre (ell := ell) G :=
  ⟨P.1.applySymmetry c, by
    rw [applySymmetry_reconstructedGraph]
    exact P.2⟩

/-- The number of simultaneous branch and edge coordinate permutations. -/
theorem coordinatePerm_card (ell : ℕ) :
    Fintype.card (CubicKernelCoordinatePerm ell) =
      (2 * ell).factorial * (3 * ell).factorial := by
  change Fintype.card
      (Equiv.Perm (Fin (2 * ell)) × Equiv.Perm (Fin (3 * ell))) = _
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]
  simp only [Fintype.card_fin]

/-- The dependent code has the expected factorial times Boolean cardinality.
Coordinate relabelling preserves the number of loop labels, which makes the
dependent sigma sum constant.  This theorem does not identify the code with
an orbit or with a reconstruction fibre. -/
theorem symmetryCode_card {k ell : ℕ}
    (P : CubicKernelPresentation k ell) :
    Fintype.card P.SymmetryCode =
      (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge P.1.graph) := by
  classical
  have hloop (γ : CubicKernelCoordinatePerm ell) :
      Fintype.card
          (CubicKernelLoopEdge (P.1.coordinateRelabel γ).graph) =
        Fintype.card (CubicKernelLoopEdge P.1.graph) := by
    let e : CubicKernelLoopEdge P.1.graph ≃
        CubicKernelLoopEdge (P.1.coordinateRelabel γ).graph := by
      simpa only [LabelledConnectedCubicKernel.coordinateRelabel_graph] using
        cubicKernelLoopEdgeCoordinateRelabelEquiv P.1.graph γ
    exact Fintype.card_congr e.symm
  unfold SymmetryCode
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_finset, hloop]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    coordinatePerm_card]
  norm_num

end CubicKernelPresentation

end PerronWright.GraphCore
