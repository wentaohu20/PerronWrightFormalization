import PerronWright.Enumeration.ExactCubicKernelIntegral
import Mathlib.Data.Sym.Sym2.Order

/-!
# Finite cubic-kernel subdivision data

This file defines the parameter-free combinatorial data used to classify
labelled cubic cores by a finite edge-labelled kernel, internal path lengths,
and original vertex labels.  No BJR model or activity parameter occurs here.

All original labels are packaged in one equivalence from the disjoint union
of the kernel-vertex slots and the ordered internal slots of all kernel edges.
Thus injectivity, disjointness, and exhaustion of `Fin k` are built into the
datum rather than postulated separately.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The ordinary simple support of an edge-labelled multigraph.  Parallel
labels are collapsed and diagonal endpoint pairs are discarded by
`SimpleGraph.fromEdgeSet`. -/
def finiteMultiGraphSupportGraph {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e) : SimpleGraph (Fin v) :=
  SimpleGraph.fromEdgeSet (Set.range H.endpoints)

/-- The finite kernel objects over which the eventual cubic Wright sum is
taken.  Connectivity is connectivity of the non-loop support; loops and
parallel edge labels remain present in `graph`. -/
structure LabelledConnectedCubicKernel (ell : ℕ) where
  graph : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)
  cubic : ∀ v, graph.degree v = 3
  connected : (finiteMultiGraphSupportGraph graph).Connected

/-- Edge labels whose endpoint pair is diagonal, i.e. the loop labels of the
edge-labelled kernel. -/
abbrev CubicKernelLoopEdge {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :=
  {e : Fin (3 * ell) // (H.endpoints e).IsDiag}

/-- The independent orientation bits which occur when ordered internal labels
are put on loop edges.  Reversing a loop path changes exactly its bit and not
the reconstructed simple graph. -/
abbrev CubicKernelLoopOrientationBits {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :=
  CubicKernelLoopEdge H → Bool

/-- An admissible internal-length assignment for a fixed edge-labelled cubic
kernel.  Lengths count degree-two vertices, not graph edges.

The two local restrictions are exactly those forced by reconstructing a
simple graph: a loop needs at least two internal vertices, and among parallel
non-loop kernel edges at most one can have length zero.  The latter is stated
as injectivity of the endpoint table on the zero-length edge subtype. -/
structure CubicKernelLengthProfile (k ell : ℕ)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) where
  length : Fin (3 * ell) → Fin (k + 1)
  totalLength : 2 * ell + ∑ e, (length e).val = k
  loopLength : ∀ e, (H.endpoints e).IsDiag → 2 ≤ (length e).val
  directEndpointsInjective :
    Function.Injective
      (fun e : {e : Fin (3 * ell) // (length e).val = 0} ↦
        H.endpoints e.1)

/-- The original-label slots carried by one length profile: first the
`2 * ell` branch-vertex slots, then the ordered internal slots on every edge
label. -/
def CubicKernelSubdivisionSlot {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :=
  Fin (2 * ell) ⊕ Σ e : Fin (3 * ell), Fin (L.length e).val

noncomputable instance cubicKernelSubdivisionSlotFintype {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :
    Fintype (CubicKernelSubdivisionSlot L) := by
  unfold CubicKernelSubdivisionSlot
  infer_instance

/-- A raw labelled subdivision of a fixed edge-labelled cubic kernel.

`labels` simultaneously records the branch labels, the ordered internal
labels on every edge, pairwise disjointness of all these labels, and
exhaustion of the original label set `Fin k`. -/
structure CubicKernelSubdivisionDatum (k ell : ℕ)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) where
  profile : CubicKernelLengthProfile k ell H
  labels : CubicKernelSubdivisionSlot profile ≃ Fin k

/-- Original label placed on a normalized branch vertex. -/
def CubicKernelSubdivisionDatum.branchLabel {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) (v : Fin (2 * ell)) : Fin k :=
  D.labels (.inl v)

/-- Original label in the `i`-th internal slot of normalized kernel edge `e`.
For a loop this is a raw orientation, later split into a canonical
representative and one Boolean direction bit. -/
def CubicKernelSubdivisionDatum.pathLabel {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) : Fin k :=
  D.labels (.inr ⟨e, i⟩)

/-- The canonical ordered pair underlying an unordered kernel endpoint pair.
For a non-loop edge it fixes the path direction; for a loop the entries
coincide and the remaining reversal is recorded by a loop bit. -/
def cubicKernelOrderedEndpoints {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) : Fin (2 * ell) × Fin (2 * ell) :=
  (Sym2.sortEquiv (H.endpoints e)).1

end PerronWright.GraphCore
