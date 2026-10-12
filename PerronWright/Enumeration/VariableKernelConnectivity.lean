import PerronWright.Enumeration.VariableKernelReconstruction
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Connectivity of variable-valence kernel subdivisions

This module proves the exact connectivity interface for the bounded-kernel
reconstruction.  Connectivity is both preserved and reflected.  The reverse
implication is obtained by collapsing every internal subdivision slot to the
first endpoint of its suppressed kernel edge.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

@[simp] theorem BoundedKernelSubdivisionDatum.pathVertex_internal_eq_pathLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) (i : Fin (D.profile.length e).val) :
    D.pathVertex e (Fin.succ i.castSucc) = D.pathLabel e i := by
  simp [BoundedKernelSubdivisionDatum.pathLabel]

/-- The canonical path graph maps to the reconstructed graph on each
suppressed edge. -/
def BoundedKernelSubdivisionDatum.pathHom
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    SimpleGraph.pathGraph ((D.profile.length e).val + 2) →g
      D.reconstructedGraph where
  toFun := D.pathVertex e
  map_rel' := by
    intro i j hij
    rw [SimpleGraph.pathGraph_adj] at hij
    rcases hij with hij | hij
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨i.val, by have := j.isLt; omega⟩
      have hi : q.castSucc = i := by
        apply Fin.ext
        rfl
      have hj : q.succ = j := by
        apply Fin.ext
        exact hij
      rw [← hi, ← hj]
      exact D.pathEdge_adj ⟨e, q⟩
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨j.val, by have := i.isLt; omega⟩
      have hj : q.castSucc = j := by
        apply Fin.ext
        rfl
      have hi : q.succ = i := by
        apply Fin.ext
        exact hij
      rw [← hi, ← hj]
      exact (D.pathEdge_adj ⟨e, q⟩).symm

/-- Any two positions on one subdivided edge are reachable. -/
theorem BoundedKernelSubdivisionDatum.pathVertex_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i j : Fin ((D.profile.length e).val + 2)) :
    D.reconstructedGraph.Reachable (D.pathVertex e i) (D.pathVertex e j) := by
  exact (SimpleGraph.pathGraph_preconnected _ i j).map (D.pathHom e)

/-- The two branch endpoints of every suppressed edge remain reachable. -/
theorem BoundedKernelSubdivisionDatum.branchEndpoints_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.reconstructedGraph.Reachable
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1)
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2) := by
  have h := D.pathVertex_reachable e
      (0 : Fin ((D.profile.length e).val + 2))
      (Fin.succ (Fin.last (D.profile.length e).val))
  rw [D.pathVertex_zero, D.pathVertex_last] at h
  exact h

/-- Every adjacency of the kernel support lifts to reachability of branch
labels in the reconstruction. -/
theorem BoundedKernelSubdivisionDatum.kernelAdj_branchLabel_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {u v : Fin K.shape.1.val}
    (huv : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Adj u v) :
    D.reconstructedGraph.Reachable (D.branchLabel u) (D.branchLabel v) := by
  rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases huv with ⟨⟨e, he⟩, _⟩
  have hord :
      s((boundedKernelOrderedEndpoints K.shape e).1,
        (boundedKernelOrderedEndpoints K.shape e).2) = s(u, v) := by
    rw [boundedKernelOrderedEndpoints_mk]
    exact he
  rcases Sym2.eq_iff.mp hord with h | h
  · simpa [h.1, h.2] using D.branchEndpoints_reachable e
  · simpa [h.1, h.2] using (D.branchEndpoints_reachable e).symm

/-- Kernel connectivity connects all reconstructed branch labels. -/
theorem BoundedKernelSubdivisionDatum.branchLabels_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected)
    (u v : Fin K.shape.1.val) :
    D.reconstructedGraph.Reachable (D.branchLabel u) (D.branchLabel v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  apply (SimpleGraph.reachable_iff_reflTransGen u v).mp (hconn u v) |>.lift'
      D.branchLabel
  intro a b hab
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (D.kernelAdj_branchLabel_reachable hab)

/-- Every subdivision slot is connected to a branch slot. -/
theorem BoundedKernelSubdivisionDatum.slot_reachable_branch
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (z : BoundedKernelSubdivisionSlot D.profile) :
    ∃ v : Fin K.shape.1.val,
      D.reconstructedGraph.Reachable (D.labels z) (D.branchLabel v) := by
  rcases z with v | ⟨e, i⟩
  · exact ⟨v, SimpleGraph.Reachable.rfl⟩
  · refine ⟨(boundedKernelOrderedEndpoints K.shape e).1, ?_⟩
    have h := D.pathVertex_reachable e
      (Fin.succ i.castSucc)
      (0 : Fin ((D.profile.length e).val + 2))
    simpa [BoundedKernelSubdivisionDatum.pathLabel,
      BoundedKernelSubdivisionDatum.branchLabel] using h

/-- Subdivision of a connected bounded kernel is connected. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_connected
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected) :
    D.reconstructedGraph.Connected := by
  let _ : Nonempty (Fin k) := hconn.nonempty.map D.branchLabel
  refine ⟨?_⟩
  intro x y
  let zx := D.labels.symm x
  let zy := D.labels.symm y
  obtain ⟨u, hxu⟩ := D.slot_reachable_branch zx
  obtain ⟨v, hyv⟩ := D.slot_reachable_branch zy
  have hx : D.labels zx = x := D.labels.apply_symm_apply x
  have hy : D.labels zy = y := D.labels.apply_symm_apply y
  rw [hx] at hxu
  rw [hy] at hyv
  exact hxu.trans (D.branchLabels_reachable hconn u v) |>.trans hyv.symm

/-! ## Converse by collapsing internal slots -/

/-- Collapse an internal slot to the first endpoint of its kernel edge. -/
def BoundedKernelSubdivisionDatum.slotAnchor
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    BoundedKernelSubdivisionSlot D.profile → Fin K.shape.1.val
  | .inl u => u
  | .inr p => (boundedKernelOrderedEndpoints K.shape p.1).1

/-- Collapse an original vertex label through the inverse slot labelling. -/
def BoundedKernelSubdivisionDatum.vertexAnchor
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) (x : Fin k) : Fin K.shape.1.val :=
  D.slotAnchor (D.labels.symm x)

@[simp] theorem BoundedKernelSubdivisionDatum.vertexAnchor_labels
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (z : BoundedKernelSubdivisionSlot D.profile) :
    D.vertexAnchor (D.labels z) = D.slotAnchor z := by
  unfold BoundedKernelSubdivisionDatum.vertexAnchor
  rw [D.labels.symm_apply_apply]

@[simp] theorem BoundedKernelSubdivisionDatum.vertexAnchor_branchLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) (u : Fin K.shape.1.val) :
    D.vertexAnchor (D.branchLabel u) = u := by
  calc
    D.vertexAnchor (D.branchLabel u) =
        D.slotAnchor
          (show BoundedKernelSubdivisionSlot D.profile from .inl u) :=
      D.vertexAnchor_labels
        (show BoundedKernelSubdivisionSlot D.profile from .inl u)
    _ = u := rfl

@[simp] theorem BoundedKernelSubdivisionDatum.vertexAnchor_pathLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) (i : Fin (D.profile.length e).val) :
    D.vertexAnchor (D.pathLabel e i) =
      (boundedKernelOrderedEndpoints K.shape e).1 := by
  calc
    D.vertexAnchor (D.pathLabel e i) =
        D.slotAnchor
          (show BoundedKernelSubdivisionSlot D.profile from .inr ⟨e, i⟩) :=
      D.vertexAnchor_labels
        (show BoundedKernelSubdivisionSlot D.profile from .inr ⟨e, i⟩)
    _ = (boundedKernelOrderedEndpoints K.shape e).1 := rfl

/-- The ordered endpoints of any bounded-kernel edge are reachable in the
kernel support; loops use reflexivity. -/
theorem boundedKernelSupport_orderedEndpoints_reachable
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Reachable
      (boundedKernelOrderedEndpoints K.shape e).1
      (boundedKernelOrderedEndpoints K.shape e).2 := by
  by_cases heq : (boundedKernelOrderedEndpoints K.shape e).1 =
      (boundedKernelOrderedEndpoints K.shape e).2
  · rw [heq]
  · apply SimpleGraph.Adj.reachable
    rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e, (boundedKernelOrderedEndpoints_mk K e).symm⟩, heq⟩

/-- Consecutive reconstructed positions collapse to reachable kernel
vertices. -/
theorem BoundedKernelSubdivisionDatum.pathEdge_vertexAnchor_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Reachable
      (D.vertexAnchor (D.pathVertex q.1 q.2.castSucc))
      (D.vertexAnchor (D.pathVertex q.1 q.2.succ)) := by
  simp only [BoundedKernelSubdivisionDatum.vertexAnchor,
    BoundedKernelSubdivisionDatum.pathVertex, Equiv.symm_apply_apply]
  rcases D.edgeSlot_classification q with
      ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨p, rfl⟩
  · rw [D.pathSlot_edgeZero_castSucc]
    have hlast :
        (0 : Fin ((D.profile.length e.1).val + 1)).succ =
          Fin.succ (Fin.last (D.profile.length e.1).val) := by
      apply Fin.ext
      simp [e.2]
    rw [hlast, D.pathSlot_last]
    exact boundedKernelSupport_orderedEndpoints_reachable K e.1
  · rw [D.pathSlot_edgeZero_castSucc,
      D.pathSlot_edgeZero_succ_of_pos e.1 e.2]
    exact SimpleGraph.Reachable.rfl
  · rw [D.pathSlot_edgeLast_castSucc_of_pos e.1 e.2,
      D.pathSlot_edgeLast_succ]
    exact boundedKernelSupport_orderedEndpoints_reachable K e.1
  · rcases p with ⟨e, i⟩
    let i₀ : Fin (D.profile.length e).val :=
      ⟨i.val, by have hi := i.isLt; omega⟩
    let i₁ : Fin (D.profile.length e).val :=
      ⟨i.val + 1, by have hi := i.isLt; omega⟩
    have hcast :
        (D.middleEdgeSlot
          (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)).2.castSucc =
          Fin.succ i₀.castSucc := by
      apply Fin.ext
      rfl
    have hsucc :
        (D.middleEdgeSlot
          (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)).2.succ =
          Fin.succ i₁.castSucc := by
      apply Fin.ext
      rfl
    simp only [BoundedKernelSubdivisionDatum.middleEdgeSlot] at hcast hsucc ⊢
    rw [hcast, hsucc, D.pathSlot_internal e i₀,
      D.pathSlot_internal e i₁]
    exact SimpleGraph.Reachable.rfl

/-- Every reconstructed adjacency collapses to kernel-support
reachability. -/
theorem BoundedKernelSubdivisionDatum.reconstructedAdj_vertexAnchor_reachable
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {x y : Fin k} (hxy : D.reconstructedGraph.Adj x y) :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Reachable
      (D.vertexAnchor x) (D.vertexAnchor y) := by
  obtain ⟨⟨q, hq⟩, -⟩ := (D.reconstructedGraph_adj_iff x y).mp hxy
  have hreach := D.pathEdge_vertexAnchor_reachable q
  change s(D.pathVertex q.1 q.2.castSucc,
      D.pathVertex q.1 q.2.succ) = s(x, y) at hq
  rcases Sym2.eq_iff.mp hq with hdir | hrev
  · simpa [hdir.1, hdir.2] using hreach
  · simpa [hrev.1, hrev.2] using hreach.symm

/-- Connectedness of a reconstructed subdivision implies connectedness of
its kernel support. -/
theorem BoundedKernelSubdivisionDatum.kernelSupport_connected_of_reconstructed
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : D.reconstructedGraph.Connected) :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected := by
  let _ : Nonempty (Fin K.shape.1.val) := hconn.nonempty.map D.vertexAnchor
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
  change Relation.ReflTransGen
      (finiteMultiGraphSupportGraph
        (boundedKernelFiniteMultiGraph K.shape)).Adj
      (D.vertexAnchor (D.branchLabel u))
      (D.vertexAnchor (D.branchLabel v)) at hcollapsed
  rw [D.vertexAnchor_branchLabel u,
    D.vertexAnchor_branchLabel v] at hcollapsed
  exact hcollapsed

/-- Connectivity is preserved and reflected by every variable-valence
bounded-kernel subdivision. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_connected_iff
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    D.reconstructedGraph.Connected ↔
      (finiteMultiGraphSupportGraph
        (boundedKernelFiniteMultiGraph K.shape)).Connected := by
  exact ⟨D.kernelSupport_connected_of_reconstructed,
    D.reconstructedGraph_connected⟩

/-! ## Minimum degree -/

/-- Every internal subdivision vertex has two distinct path neighbours. -/
theorem BoundedKernelSubdivisionDatum.internalVertex_degree_ge_two
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    2 ≤ D.reconstructedGraph.degree (D.pathLabel e i) := by
  let q₀ : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e, ⟨i.val, by have := i.isLt; omega⟩⟩
  let q₁ : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e, ⟨i.val + 1, by have := i.isLt; omega⟩⟩
  let y := D.pathVertex e q₀.2.castSucc
  let z := D.pathVertex e q₁.2.succ
  have h₀center : q₀.2.succ = Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  have h₁center : q₁.2.castSucc = Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  have hyx : D.reconstructedGraph.Adj y (D.pathLabel e i) := by
    have h := D.pathEdge_adj q₀
    rw [h₀center, D.pathVertex_internal_eq_pathLabel] at h
    exact h
  have hxz : D.reconstructedGraph.Adj (D.pathLabel e i) z := by
    have h := D.pathEdge_adj q₁
    rw [h₁center, D.pathVertex_internal_eq_pathLabel] at h
    exact h
  have hq : q₀ ≠ q₁ := by
    intro h
    have hval := congrArg
      (fun q : BoundedKernelSubdivisionEdgeSlot D ↦ q.2.val) h
    simp [q₀, q₁] at hval
  have hyz : y ≠ z := by
    intro hyz
    apply hq
    apply D.subdivisionEdge_injective
    have he₀ : D.subdivisionEdge q₀ = s(y, D.pathLabel e i) := by
      unfold BoundedKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q₀.2.castSucc,
        D.pathVertex e q₀.2.succ) = _
      rw [h₀center, D.pathVertex_internal_eq_pathLabel]
    have he₁ : D.subdivisionEdge q₁ = s(D.pathLabel e i, z) := by
      unfold BoundedKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q₁.2.castSucc,
        D.pathVertex e q₁.2.succ) = _
      rw [h₁center, D.pathVertex_internal_eq_pathLabel]
    rw [he₀, he₁, hyz]
    exact Sym2.eq_swap
  have hcard : 1 < (D.reconstructedGraph.neighborFinset
      (D.pathLabel e i)).card := by
    apply Finset.one_lt_card_iff.mpr
    exact ⟨y, z,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hyx.symm,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hxz, hyz⟩
  rw [D.reconstructedGraph.card_neighborFinset_eq_degree] at hcard
  omega

/-- An occurrence of a branch vertex in a bounded-kernel endpoint pair
supplies an actual reconstructed neighbour and remembers the emitting edge
slot. -/
theorem BoundedKernelSubdivisionDatum.kernelEndpoint_neighbor
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) (u : Fin K.shape.1.val)
    (hue : u ∈ K.shape.2.2 e) :
    ∃ (q : BoundedKernelSubdivisionEdgeSlot D) (y : Fin k),
      q.1 = e ∧
      D.reconstructedGraph.Adj (D.branchLabel u) y ∧
      D.subdivisionEdge q = s(D.branchLabel u, y) := by
  rw [← boundedKernelOrderedEndpoints_mk K e, Sym2.mem_iff] at hue
  rcases hue with hue | hue
  · let q : BoundedKernelSubdivisionEdgeSlot D :=
      ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
    let y := D.pathVertex e q.2.succ
    have hstart : D.pathVertex e q.2.castSucc = D.branchLabel u := by
      have hq0 : q.2.castSucc =
          (0 : Fin ((D.profile.length e).val + 2)) := by
        apply Fin.ext
        rfl
      rw [hq0, D.pathVertex_zero, hue]
      rfl
    refine ⟨q, y, rfl, ?_, ?_⟩
    · rw [← hstart]
      exact D.pathEdge_adj q
    · unfold BoundedKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q.2.castSucc,
        D.pathVertex e q.2.succ) = _
      rw [hstart]
  · let q : BoundedKernelSubdivisionEdgeSlot D :=
      ⟨e, Fin.last (D.profile.length e).val⟩
    let y := D.pathVertex e q.2.castSucc
    have hend : D.pathVertex e q.2.succ = D.branchLabel u := by
      have hqLast : q.2.succ =
          Fin.succ (Fin.last (D.profile.length e).val) := by
        apply Fin.ext
        rfl
      rw [hqLast, D.pathVertex_last, hue]
      rfl
    refine ⟨q, y, rfl, ?_, ?_⟩
    · rw [← hend]
      exact (D.pathEdge_adj q).symm
    · unfold BoundedKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q.2.castSucc,
        D.pathVertex e q.2.succ) = _
      rw [hend]
      exact Sym2.eq_swap

/-- A branch vertex has at least two distinct reconstructed neighbours.  A
minimum kernel degree of three forces two distinct incident kernel labels,
because one unordered endpoint pair contributes at most two incidences. -/
theorem BoundedKernelSubdivisionDatum.branchVertex_degree_ge_two
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    2 ≤ D.reconstructedGraph.degree (D.branchLabel u) := by
  let H := boundedKernelFiniteMultiGraph K.shape
  have hsumGe : 3 ≤ ∑ e : Fin K.shape.2.1.val,
      (H.endpoints e).toMultiset.count u := by
    simpa only [PerronWright.FiniteMultiGraph.degree,
      finiteMultiGraph_incidence_eq_count] using K.minDegree u
  have hsumNe : (∑ e : Fin K.shape.2.1.val,
      (H.endpoints e).toMultiset.count u) ≠ 0 := by
    omega
  obtain ⟨e, _heuniv, hecount⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  have hecountLe : (H.endpoints e).toMultiset.count u ≤ 2 := by
    calc
      (H.endpoints e).toMultiset.count u ≤
          (H.endpoints e).toMultiset.card :=
        Multiset.count_le_card _ _
      _ = 2 := by
        induction H.endpoints e using Sym2.inductionOn with
        | _ a b => simp [Sym2.toMultiset]
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin K.shape.2.1.val)))
    (f := fun f ↦ (H.endpoints f).toMultiset.count u)
    (Finset.mem_univ e)
  have hrestNe : (∑ f ∈ (Finset.univ.erase e),
      (H.endpoints f).toMultiset.count u) ≠ 0 := by
    intro hzero
    have htotal : (∑ f : Fin K.shape.2.1.val,
        (H.endpoints f).toMultiset.count u) =
          (H.endpoints e).toMultiset.count u := by
      have h := hsplit
      rw [hzero, zero_add] at h
      exact h.symm
    rw [htotal] at hsumGe
    omega
  obtain ⟨f, hfmem, hfcount⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hrestNe
  have hfe : f ≠ e := (Finset.mem_erase.mp hfmem).1
  have hue : u ∈ H.endpoints e := by
    rw [← Sym2.mem_toMultiset]
    exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hecount)
  have huf : u ∈ H.endpoints f := by
    rw [← Sym2.mem_toMultiset]
    exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hfcount)
  obtain ⟨q, y, hqe, hy, hqy⟩ := D.kernelEndpoint_neighbor e u hue
  obtain ⟨r, z, hrf, hz, hrz⟩ := D.kernelEndpoint_neighbor f u huf
  have hqr : q ≠ r := by
    intro h
    apply hfe
    calc
      f = r.1 := hrf.symm
      _ = q.1 := congrArg Sigma.fst h.symm
      _ = e := hqe
  have hyz : y ≠ z := by
    intro hyz
    apply hqr
    apply D.subdivisionEdge_injective
    rw [hqy, hrz, hyz]
  have hcard : 1 < (D.reconstructedGraph.neighborFinset
      (D.branchLabel u)).card := by
    apply Finset.one_lt_card_iff.mpr
    exact ⟨y, z,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hy,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hz, hyz⟩
  rw [D.reconstructedGraph.card_neighborFinset_eq_degree] at hcard
  omega

/-- Every reconstructed vertex has degree at least two. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_minDegree_two
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    ∀ x, 2 ≤ D.reconstructedGraph.degree x := by
  intro x
  let z := D.labels.symm x
  have hx : D.labels z = x := D.labels.apply_symm_apply x
  rcases z with v | ⟨e, i⟩
  · rw [← hx]
    exact D.branchVertex_degree_ge_two v
  · rw [← hx]
    exact D.internalVertex_degree_ge_two e i

/-- The exact graph-theoretic output of every admissible bounded-kernel
subdivision. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_admissible
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected) :
    D.reconstructedGraph.Connected ∧
      (∀ x, 2 ≤ D.reconstructedGraph.degree x) ∧
      D.reconstructedGraph.edgeFinset.card = k + ell := by
  exact ⟨D.reconstructedGraph_connected hconn,
    D.reconstructedGraph_minDegree_two,
    D.reconstructedGraph_edgeFinset_card⟩

end PerronWright.GraphCore
