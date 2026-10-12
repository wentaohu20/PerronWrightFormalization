import PerronWright.Enumeration.CubicKernelConnectivity

/-!
# Converse connectivity for cubic-kernel subdivisions

This file proves the converse to subdivision preserving connectivity.  The
proof collapses every internal subdivision vertex to the first endpoint of
its kernel edge.  A reconstructed edge then collapses either to equality or
to one kernel-support edge.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Collapse a subdivision slot to a kernel vertex.  Internal slots on an
edge are sent to the first endpoint in the canonical ordering. -/
def CubicKernelSubdivisionDatum.slotAnchor
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    CubicKernelSubdivisionSlot D.profile → Fin (2 * ell)
  | .inl u => u
  | .inr p => (cubicKernelOrderedEndpoints H p.1).1

/-- Collapse an original reconstructed label through the inverse labelling
equivalence and then through `slotAnchor`. -/
def CubicKernelSubdivisionDatum.vertexAnchor
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) (x : Fin k) : Fin (2 * ell) :=
  D.slotAnchor (D.labels.symm x)

@[simp]
theorem CubicKernelSubdivisionDatum.vertexAnchor_labels
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (z : CubicKernelSubdivisionSlot D.profile) :
    D.vertexAnchor (D.labels z) = D.slotAnchor z := by
  unfold CubicKernelSubdivisionDatum.vertexAnchor
  rw [D.labels.symm_apply_apply]

@[simp]
theorem CubicKernelSubdivisionDatum.vertexAnchor_branchLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) (u : Fin (2 * ell)) :
    D.vertexAnchor (D.branchLabel u) = u := by
  calc
    D.vertexAnchor (D.branchLabel u) =
        D.slotAnchor
          (show CubicKernelSubdivisionSlot D.profile from .inl u) :=
      D.vertexAnchor_labels
        (show CubicKernelSubdivisionSlot D.profile from .inl u)
    _ = u := rfl

@[simp]
theorem CubicKernelSubdivisionDatum.vertexAnchor_pathLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) :
    D.vertexAnchor (D.pathLabel e i) =
      (cubicKernelOrderedEndpoints H e).1 := by
  calc
    D.vertexAnchor (D.pathLabel e i) =
        D.slotAnchor
          (show CubicKernelSubdivisionSlot D.profile from .inr ⟨e, i⟩) :=
      D.vertexAnchor_labels
        (show CubicKernelSubdivisionSlot D.profile from .inr ⟨e, i⟩)
    _ = (cubicKernelOrderedEndpoints H e).1 := rfl

/-- The two canonically ordered endpoints of any labelled kernel edge are
reachable in its simple support.  A loop gives reflexivity; a non-loop gives
one support edge. -/
theorem finiteMultiGraphSupportGraph_orderedEndpoints_reachable
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) :
    (finiteMultiGraphSupportGraph H).Reachable
      (cubicKernelOrderedEndpoints H e).1
      (cubicKernelOrderedEndpoints H e).2 := by
  by_cases heq : (cubicKernelOrderedEndpoints H e).1 =
      (cubicKernelOrderedEndpoints H e).2
  · rw [heq]
  · apply SimpleGraph.Adj.reachable
    rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e, (cubicKernelOrderedEndpoints_mk H e).symm⟩, heq⟩

/-- Consecutive positions on one reconstructed path collapse to reachable
vertices of the kernel support. -/
theorem CubicKernelSubdivisionDatum.pathEdge_vertexAnchor_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    (finiteMultiGraphSupportGraph H).Reachable
      (D.vertexAnchor (D.pathVertex q.1 q.2.castSucc))
      (D.vertexAnchor (D.pathVertex q.1 q.2.succ)) := by
  simp only [CubicKernelSubdivisionDatum.vertexAnchor,
    CubicKernelSubdivisionDatum.pathVertex, Equiv.symm_apply_apply]
  rcases D.edgeSlot_classification q with
      ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨p, rfl⟩
  · rw [D.pathSlot_edgeZero_castSucc]
    have hlast :
        (0 : Fin ((D.profile.length e.1).val + 1)).succ =
          Fin.succ (Fin.last (D.profile.length e.1).val) := by
      apply Fin.ext
      simp [e.2]
    rw [hlast, D.pathSlot_last]
    exact finiteMultiGraphSupportGraph_orderedEndpoints_reachable H e.1
  · rw [D.pathSlot_edgeZero_castSucc,
      D.pathSlot_edgeZero_succ_of_pos e.1 e.2]
    exact SimpleGraph.Reachable.rfl
  · rw [D.pathSlot_edgeLast_castSucc_of_pos e.1 e.2,
      D.pathSlot_edgeLast_succ]
    exact finiteMultiGraphSupportGraph_orderedEndpoints_reachable H e.1
  · rcases p with ⟨e, i⟩
    let i₀ : Fin (D.profile.length e).val :=
      ⟨i.val, by have hi := i.isLt; omega⟩
    let i₁ : Fin (D.profile.length e).val :=
      ⟨i.val + 1, by have hi := i.isLt; omega⟩
    have hcast :
        (D.middleEdgeSlot
          (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)).2.castSucc =
          Fin.succ i₀.castSucc := by
      apply Fin.ext
      rfl
    have hsucc :
        (D.middleEdgeSlot
          (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)).2.succ =
          Fin.succ i₁.castSucc := by
      apply Fin.ext
      rfl
    simp only [CubicKernelSubdivisionDatum.middleEdgeSlot] at hcast hsucc ⊢
    rw [hcast, hsucc, D.pathSlot_internal e i₀,
      D.pathSlot_internal e i₁]
    exact SimpleGraph.Reachable.rfl

/-- Every reconstructed adjacency collapses to reachability in the kernel
support. -/
theorem CubicKernelSubdivisionDatum.reconstructedAdj_vertexAnchor_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {x y : Fin k} (hxy : D.reconstructedGraph.Adj x y) :
    (finiteMultiGraphSupportGraph H).Reachable
      (D.vertexAnchor x) (D.vertexAnchor y) := by
  obtain ⟨⟨q, hq⟩, -⟩ := (D.reconstructedGraph_adj_iff x y).mp hxy
  have hreach := D.pathEdge_vertexAnchor_reachable q
  change s(D.pathVertex q.1 q.2.castSucc,
      D.pathVertex q.1 q.2.succ) = s(x, y) at hq
  rcases Sym2.eq_iff.mp hq with hdir | hrev
  · simpa [hdir.1, hdir.2] using hreach
  · simpa [hrev.1, hrev.2] using hreach.symm

/-- If a reconstructed subdivision is connected, then the original
multigraph support was connected.  No positivity assumption on `ell` is
needed: connectedness of the reconstruction supplies nonemptiness of the
kernel vertex type through `vertexAnchor`. -/
theorem CubicKernelSubdivisionDatum.kernelSupport_connected_of_reconstructed
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hconn : D.reconstructedGraph.Connected) :
    (finiteMultiGraphSupportGraph H).Connected := by
  let _ : Nonempty (Fin (2 * ell)) := hconn.nonempty.map D.vertexAnchor
  refine ⟨?_⟩
  intro u v
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hpath := (SimpleGraph.reachable_iff_reflTransGen
    (D.branchLabel u) (D.branchLabel v)).mp
      (hconn (D.branchLabel u) (D.branchLabel v))
  have hcollapsed := hpath.lift' D.vertexAnchor (by
    intro x y hxy
    exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (D.reconstructedAdj_vertexAnchor_reachable hxy))
  change Relation.ReflTransGen (finiteMultiGraphSupportGraph H).Adj
      (D.vertexAnchor (D.branchLabel u))
      (D.vertexAnchor (D.branchLabel v)) at hcollapsed
  rw [D.vertexAnchor_branchLabel u,
    D.vertexAnchor_branchLabel v] at hcollapsed
  exact hcollapsed

/-- Connectivity is preserved and reflected by a cubic-kernel subdivision. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_connected_iff
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    D.reconstructedGraph.Connected ↔
      (finiteMultiGraphSupportGraph H).Connected := by
  exact ⟨D.kernelSupport_connected_of_reconstructed,
    D.reconstructedGraph_connected⟩

end PerronWright.GraphCore
