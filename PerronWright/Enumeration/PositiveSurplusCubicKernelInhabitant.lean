import PerronWright.Enumeration.CubicKernelSubdivision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Translate
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# An explicit connected cubic kernel at every positive surplus

For `0 < ell`, take a cyclically ordered set of `2 * ell` vertices.  The
first `2 * ell` edge labels are the directed cyclic edges (remembered as
unordered endpoint pairs), and the remaining `ell` labels form the matching
between the two copies in

`Fin ell ⊕ Fin ell ≃ Fin (2 * ell)`.

Every vertex has two cyclic incidences and one matching incidence.  The
ordinary path graph is contained in the non-loop support, so the support is
connected.  At `ell = 1` the two directed cyclic labels and the matching
label are simply three parallel edges between the two vertices; hence no
separate exceptional object is required.
-/

open PerronWright
open scoped Classical Fin.NatCast BigOperators

noncomputable section

namespace PerronWright.GraphCore

private def positiveCubicVertexPairEquiv (ell : ℕ) :
    Fin ell ⊕ Fin ell ≃ Fin (2 * ell) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def positiveCubicCyclicNext (ell : ℕ) (hell : 0 < ell) :
    Fin (2 * ell) ≃ Fin (2 * ell) := by
  letI : NeZero (2 * ell) := ⟨by omega⟩
  exact Equiv.addRight 1

private def positiveCubicCycleEdges (ell : ℕ) (hell : 0 < ell) :
    Fin (2 * ell) → Sym2 (Fin (2 * ell)) :=
  fun i ↦ s(i, positiveCubicCyclicNext ell hell i)

private def positiveCubicMatchingEdges (ell : ℕ) :
    Fin ell → Sym2 (Fin (2 * ell)) :=
  fun i ↦ s(positiveCubicVertexPairEquiv ell (.inl i),
    positiveCubicVertexPairEquiv ell (.inr i))

/-- The explicit edge-labelled cycle-plus-matching multigraph. -/
def positiveSurplusCubicKernelGraph (ell : ℕ) (hell : 0 < ell) :
    PerronWright.FiniteMultiGraph (2 * ell) (3 * ell) where
  endpoints :=
    Fin.append (positiveCubicCycleEdges ell hell)
        (positiveCubicMatchingEdges ell) ∘
      Fin.cast (by omega : 3 * ell = 2 * ell + ell)

private def positiveCubicCycleEdgeLabel
    (ell : ℕ) (i : Fin (2 * ell)) : Fin (3 * ell) :=
  Fin.cast (by omega : 2 * ell + ell = 3 * ell) (Fin.castAdd ell i)

@[simp] private theorem positiveSurplusCubicKernelGraph_cycleEdgeLabel
    (ell : ℕ) (hell : 0 < ell) (i : Fin (2 * ell)) :
    (positiveSurplusCubicKernelGraph ell hell).endpoints
        (positiveCubicCycleEdgeLabel ell i) =
      positiveCubicCycleEdges ell hell i := by
  simp [positiveSurplusCubicKernelGraph,
    positiveCubicCycleEdgeLabel, positiveCubicCycleEdges]

private theorem positiveCubicCyclicNext_eq_of_val_succ
    (ell : ℕ) (hell : 0 < ell) {u v : Fin (2 * ell)}
    (h : u.val + 1 = v.val) :
    positiveCubicCyclicNext ell hell u = v := by
  let _ : NeZero (2 * ell) := ⟨by omega⟩
  apply Fin.ext
  change (u + (1 : Fin (2 * ell))).val = v.val
  have hone : (1 : ℕ) < 2 * ell := by omega
  have hlt : u.val + (1 : Fin (2 * ell)).val < 2 * ell := by
    rw [Fin.val_one', Nat.mod_eq_of_lt hone, h]
    exact v.isLt
  calc
    (u + (1 : Fin (2 * ell))).val =
        u.val + (1 : Fin (2 * ell)).val :=
      Fin.val_add_eq_of_add_lt hlt
    _ = u.val + 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt hone]
    _ = v.val := h

private theorem sum_over_positiveCubicKernelGraph_edges
    (ell : ℕ) (hell : 0 < ell)
    (f : Sym2 (Fin (2 * ell)) → ℕ) :
    (∑ e : Fin (3 * ell),
        f ((positiveSurplusCubicKernelGraph ell hell).endpoints e)) =
      (∑ i : Fin (2 * ell), f (positiveCubicCycleEdges ell hell i)) +
        ∑ i : Fin ell, f (positiveCubicMatchingEdges ell i) := by
  let ecount : Fin (3 * ell) ≃ Fin (2 * ell + ell) :=
    finCongr (by omega)
  let split : Fin (2 * ell) ⊕ Fin ell ≃ Fin (2 * ell + ell) :=
    finSumFinEquiv
  calc
    (∑ e : Fin (3 * ell),
        f ((positiveSurplusCubicKernelGraph ell hell).endpoints e)) =
        ∑ e : Fin (2 * ell + ell),
          f (Fin.append (positiveCubicCycleEdges ell hell)
            (positiveCubicMatchingEdges ell) e) := by
      simpa [positiveSurplusCubicKernelGraph, ecount] using
        ecount.sum_comp
          (fun e ↦ f (Fin.append (positiveCubicCycleEdges ell hell)
            (positiveCubicMatchingEdges ell) e))
    _ = ∑ z : Fin (2 * ell) ⊕ Fin ell,
        f (Fin.append (positiveCubicCycleEdges ell hell)
          (positiveCubicMatchingEdges ell) (split z)) := by
      exact (split.sum_comp fun e ↦
        f (Fin.append (positiveCubicCycleEdges ell hell)
          (positiveCubicMatchingEdges ell) e)).symm
    _ = (∑ i : Fin (2 * ell),
          f (positiveCubicCycleEdges ell hell i)) +
        ∑ i : Fin ell, f (positiveCubicMatchingEdges ell i) := by
      rw [Fintype.sum_sum_type]
      congr 1 <;> apply Fintype.sum_congr <;> intro i
      · simp [split, finSumFinEquiv]
      · simp [split, finSumFinEquiv]

private theorem positiveCubicCycleIncidenceSum
    (ell : ℕ) (hell : 0 < ell) (x : Fin (2 * ell)) :
    (∑ i : Fin (2 * ell),
        PerronWright.FiniteMultiGraph.incidence
          (positiveCubicCycleEdges ell hell i) x) = 2 := by
  simp_rw [positiveCubicCycleEdges,
    PerronWright.FiniteMultiGraph.incidence_mk]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ i : Fin (2 * ell), if i = x then 1 else 0) = 1 := by
    simp
  have hnext :
      (∑ i : Fin (2 * ell),
        if positiveCubicCyclicNext ell hell i = x then 1 else 0) = 1 := by
    exact ((positiveCubicCyclicNext ell hell).sum_comp
      (fun i ↦ if i = x then 1 else 0)).trans (by simp)
  omega

private theorem positiveCubicMatchingIncidenceSum
    (ell : ℕ) (x : Fin (2 * ell)) :
    (∑ i : Fin ell,
        PerronWright.FiniteMultiGraph.incidence
          (positiveCubicMatchingEdges ell i) x) = 1 := by
  simp_rw [positiveCubicMatchingEdges,
    PerronWright.FiniteMultiGraph.incidence_mk]
  rw [Finset.sum_add_distrib]
  have hpair :
      (∑ z : Fin ell ⊕ Fin ell,
        if positiveCubicVertexPairEquiv ell z = x then 1 else 0) = 1 := by
    exact ((positiveCubicVertexPairEquiv ell).sum_comp
      (fun z ↦ if z = x then 1 else 0)).trans (by simp)
  rw [Fintype.sum_sum_type] at hpair
  exact hpair

theorem positiveSurplusCubicKernelGraph_cubic
    (ell : ℕ) (hell : 0 < ell) (x : Fin (2 * ell)) :
    (positiveSurplusCubicKernelGraph ell hell).degree x = 3 := by
  unfold PerronWright.FiniteMultiGraph.degree
  calc
    (∑ edge,
        PerronWright.FiniteMultiGraph.incidence
          ((positiveSurplusCubicKernelGraph ell hell).endpoints edge) x) =
        (∑ i : Fin (2 * ell),
          PerronWright.FiniteMultiGraph.incidence
            (positiveCubicCycleEdges ell hell i) x) +
          ∑ i : Fin ell,
            PerronWright.FiniteMultiGraph.incidence
              (positiveCubicMatchingEdges ell i) x :=
      sum_over_positiveCubicKernelGraph_edges ell hell _
    _ = 2 + 1 := by
      rw [positiveCubicCycleIncidenceSum,
        positiveCubicMatchingIncidenceSum]
    _ = 3 := by norm_num

private theorem pathGraph_le_positiveSurplusCubicKernelSupport
    (ell : ℕ) (hell : 0 < ell) :
    SimpleGraph.pathGraph (2 * ell) ≤
      finiteMultiGraphSupportGraph
        (positiveSurplusCubicKernelGraph ell hell) := by
  intro u v huv
  have hne : u ≠ v := huv.ne
  rw [SimpleGraph.pathGraph_adj] at huv
  rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hne⟩
  rcases huv with huv | hvu
  · refine ⟨positiveCubicCycleEdgeLabel ell u, ?_⟩
    rw [positiveSurplusCubicKernelGraph_cycleEdgeLabel,
      positiveCubicCycleEdges,
      positiveCubicCyclicNext_eq_of_val_succ ell hell huv]
  · refine ⟨positiveCubicCycleEdgeLabel ell v, ?_⟩
    rw [positiveSurplusCubicKernelGraph_cycleEdgeLabel,
      positiveCubicCycleEdges,
      positiveCubicCyclicNext_eq_of_val_succ ell hell hvu]
    exact Sym2.eq_swap

theorem positiveSurplusCubicKernelGraph_connected
    (ell : ℕ) (hell : 0 < ell) :
    (finiteMultiGraphSupportGraph
      (positiveSurplusCubicKernelGraph ell hell)).Connected := by
  have hpath : (SimpleGraph.pathGraph (2 * ell)).Connected := by
    cases ell with
    | zero => omega
    | succ n =>
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using SimpleGraph.pathGraph_connected (2 * n + 1)
  exact hpath.mono
    (pathGraph_le_positiveSurplusCubicKernelSupport ell hell)

/-- A concrete labelled connected cubic kernel of every positive excess. -/
def positiveSurplusCubicKernel (ell : ℕ) (hell : 0 < ell) :
    LabelledConnectedCubicKernel ell where
  graph := positiveSurplusCubicKernelGraph ell hell
  cubic := positiveSurplusCubicKernelGraph_cubic ell hell
  connected := positiveSurplusCubicKernelGraph_connected ell hell

theorem labelledConnectedCubicKernel_nonempty
    (ell : ℕ) (hell : 0 < ell) :
    Nonempty (LabelledConnectedCubicKernel ell) :=
  ⟨positiveSurplusCubicKernel ell hell⟩

/-- Typeclass form of the explicit construction. -/
instance labelledConnectedCubicKernelNonempty
    (ell : ℕ) [NeZero ell] :
    Nonempty (LabelledConnectedCubicKernel ell) :=
  labelledConnectedCubicKernel_nonempty ell (Nat.pos_of_ne_zero (NeZero.ne ell))

end PerronWright.GraphCore
