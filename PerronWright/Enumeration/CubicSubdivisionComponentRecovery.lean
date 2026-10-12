import PerronWright.Enumeration.CubicKernelInverseGeometry
import PerronWright.Enumeration.CoreWeightFactor

/-!
# Recovering degree-two components of a cubic-kernel subdivision

This scratch module proves that the induced degree-two graph of an admissible
cubic-kernel subdivision splits exactly into the internal paths of the
positive-length kernel edges.  In particular, distinct normalized kernel
edges cannot be joined inside the degree-two graph.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Two internal labels are adjacent exactly when they lie on the same
kernel edge in consecutive internal positions. -/
theorem CubicKernelSubdivisionDatum.pathLabel_adj_iff
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e f : Fin (3 * ell))
    (i : Fin (D.profile.length e).val)
    (j : Fin (D.profile.length f).val) :
    D.reconstructedGraph.Adj (D.pathLabel e i) (D.pathLabel f j) ↔
      e = f ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  constructor
  · intro hij
    obtain ⟨⟨q, hq⟩, -⟩ :=
      (D.reconstructedGraph_adj_iff (D.pathLabel e i)
        (D.pathLabel f j)).mp hij
    have hslot :
        D.subdivisionSlotEdge q =
          s((.inr ⟨e, i⟩ : CubicKernelSubdivisionSlot D.profile),
            (.inr ⟨f, j⟩ : CubicKernelSubdivisionSlot D.profile)) := by
      change Sym2.map D.labels (D.subdivisionSlotEdge q) =
        Sym2.map D.labels
          s((.inr ⟨e, i⟩ : CubicKernelSubdivisionSlot D.profile),
            (.inr ⟨f, j⟩ : CubicKernelSubdivisionSlot D.profile)) at hq
      exact Sym2.map.injective D.labels.injective hq
    rcases D.edgeSlot_classification q with hdirect | hstart | hend | hmiddle
    · rcases hdirect with ⟨g, rfl⟩
      rw [D.subdivisionSlotEdge_direct g.1 g.2] at hslot
      rcases Sym2.eq_iff.mp hslot with hdir | hrev
      · cases hdir.1
      · cases hrev.1
    · rcases hstart with ⟨g, rfl⟩
      rw [D.subdivisionSlotEdge_start g.1 g.2] at hslot
      rcases Sym2.eq_iff.mp hslot with hdir | hrev
      · cases hdir.1
      · cases hrev.1
    · rcases hend with ⟨g, rfl⟩
      rw [D.subdivisionSlotEdge_end g.1 g.2] at hslot
      rcases Sym2.eq_iff.mp hslot with hdir | hrev
      · cases hdir.2
      · cases hrev.2
    · rcases hmiddle with ⟨⟨g, p⟩, rfl⟩
      rw [D.subdivisionSlotEdge_middle g p] at hslot
      rcases Sym2.eq_iff.mp hslot with hdir | hrev
      · have h₀ := Sum.inr.inj hdir.1
        have h₁ := Sum.inr.inj hdir.2
        have hge : g = e := congrArg Sigma.fst h₀
        have hgf : g = f := congrArg Sigma.fst h₁
        have hv₀ := congrArg
          (fun z : Σ a : Fin (3 * ell), Fin (D.profile.length a).val ↦ z.2.val) h₀
        have hv₁ := congrArg
          (fun z : Σ a : Fin (3 * ell), Fin (D.profile.length a).val ↦ z.2.val) h₁
        refine ⟨hge.symm.trans hgf, Or.inl ?_⟩
        simp only at hv₀ hv₁
        omega
      · have h₀ := Sum.inr.inj hrev.1
        have h₁ := Sum.inr.inj hrev.2
        have hgf : g = f := congrArg Sigma.fst h₀
        have hge : g = e := congrArg Sigma.fst h₁
        have hv₀ := congrArg
          (fun z : Σ a : Fin (3 * ell), Fin (D.profile.length a).val ↦ z.2.val) h₀
        have hv₁ := congrArg
          (fun z : Σ a : Fin (3 * ell), Fin (D.profile.length a).val ↦ z.2.val) h₁
        refine ⟨hge.symm.trans hgf, Or.inr ?_⟩
        simp only at hv₀ hv₁
        omega
  · rintro ⟨rfl, hij | hji⟩
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨i.val + 1, by have := j.isLt; omega⟩
      have hleft : q.castSucc = Fin.succ i.castSucc := by
        apply Fin.ext
        rfl
      have hright : q.succ = Fin.succ j.castSucc := by
        apply Fin.ext
        simp only [q, Fin.val_succ, Fin.val_castSucc]
        omega
      have h := D.pathEdge_adj_unconditional
        (⟨e, q⟩ : CubicKernelSubdivisionEdgeSlot D)
      rw [hleft, hright, D.pathVertex_internal,
        D.pathVertex_internal] at h
      exact h
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨j.val + 1, by have := i.isLt; omega⟩
      have hleft : q.castSucc = Fin.succ j.castSucc := by
        apply Fin.ext
        rfl
      have hright : q.succ = Fin.succ i.castSucc := by
        apply Fin.ext
        simp only [q, Fin.val_succ, Fin.val_castSucc]
        omega
      have h := D.pathEdge_adj_unconditional
        (⟨e, q⟩ : CubicKernelSubdivisionEdgeSlot D)
      rw [hleft, hright, D.pathVertex_internal,
        D.pathVertex_internal] at h
      exact h.symm

/-- Internal labels belonging to distinct normalized kernel edges are never
adjacent in the reconstructed graph. -/
theorem CubicKernelSubdivisionDatum.pathLabel_not_adj_of_ne
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {e f : Fin (3 * ell)} (hef : e ≠ f)
    (i : Fin (D.profile.length e).val)
    (j : Fin (D.profile.length f).val) :
    ¬D.reconstructedGraph.Adj (D.pathLabel e i) (D.pathLabel f j) := by
  intro hij
  exact hef ((D.pathLabel_adj_iff e f i j).mp hij).1

/-- The ordered internal labels of one kernel edge form a graph homomorphism
from the standard path into the induced degree-two graph. -/
def CubicKernelSubdivisionDatum.internalPathHom
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : Fin (3 * ell)) :
    SimpleGraph.pathGraph (D.profile.length e).val →g
      twoGraph D.reconstructedGraph where
  toFun i := ⟨D.pathLabel e i, D.internalVertex_degree_eq_two K e i⟩
  map_rel' := by
    intro i j hij
    change D.reconstructedGraph.Adj (D.pathLabel e i) (D.pathLabel e j)
    exact (D.pathLabel_adj_iff e e i j).mpr
      ⟨rfl, SimpleGraph.pathGraph_adj.mp hij⟩

/-- All internal labels of one positive-length kernel edge lie in one
connected component of the induced degree-two graph. -/
theorem CubicKernelSubdivisionDatum.internalPath_reachable_twoGraph
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : Fin (3 * ell))
    (i j : Fin (D.profile.length e).val) :
    (twoGraph D.reconstructedGraph).Reachable
      ⟨D.pathLabel e i, D.internalVertex_degree_eq_two K e i⟩
      ⟨D.pathLabel e j, D.internalVertex_degree_eq_two K e j⟩ := by
  exact (SimpleGraph.pathGraph_preconnected _ i j).map
    (D.internalPathHom K e)

/-- The normalized kernel edge carrying a degree-two reconstructed vertex. -/
noncomputable def CubicKernelSubdivisionDatum.degreeTwoKernelEdge
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : {v : Fin k // D.reconstructedGraph.degree v = 2}) :
    Fin (3 * ell) :=
  Classical.choose
    ((D.degree_eq_two_iff_exists_pathLabel K x.1).mp x.2)

/-- The internal position accompanying `degreeTwoKernelEdge`. -/
noncomputable def CubicKernelSubdivisionDatum.degreeTwoKernelIndex
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : {v : Fin k // D.reconstructedGraph.degree v = 2}) :
    Fin (D.profile.length (D.degreeTwoKernelEdge K x)).val :=
  Classical.choose (Classical.choose_spec
    ((D.degree_eq_two_iff_exists_pathLabel K x.1).mp x.2))

theorem CubicKernelSubdivisionDatum.degreeTwoKernelSlot_spec
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : {v : Fin k // D.reconstructedGraph.degree v = 2}) :
    x.1 = D.pathLabel (D.degreeTwoKernelEdge K x)
      (D.degreeTwoKernelIndex K x) :=
  Classical.choose_spec (Classical.choose_spec
    ((D.degree_eq_two_iff_exists_pathLabel K x.1).mp x.2))

/-- Adjacency inside the degree-two graph preserves the recovered normalized
kernel edge. -/
theorem CubicKernelSubdivisionDatum.degreeTwoKernelEdge_eq_of_adj
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    {x y : {v : Fin k // D.reconstructedGraph.degree v = 2}}
    (hxy : (twoGraph D.reconstructedGraph).Adj x y) :
    D.degreeTwoKernelEdge K x = D.degreeTwoKernelEdge K y := by
  have hxy' : D.reconstructedGraph.Adj x.1 y.1 := hxy
  rw [D.degreeTwoKernelSlot_spec K x,
    D.degreeTwoKernelSlot_spec K y] at hxy'
  exact ((D.pathLabel_adj_iff _ _ _ _).mp hxy').1

/-- Reachability inside the induced degree-two graph preserves the recovered
normalized kernel edge. -/
theorem CubicKernelSubdivisionDatum.degreeTwoKernelEdge_eq_of_reachable
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    {x y : {v : Fin k // D.reconstructedGraph.degree v = 2}}
    (hxy : (twoGraph D.reconstructedGraph).Reachable x y) :
    D.degreeTwoKernelEdge K x = D.degreeTwoKernelEdge K y := by
  exact hxy.elim fun p ↦ by
    induction p with
    | nil => rfl
    | cons hadj p ih =>
        exact (D.degreeTwoKernelEdge_eq_of_adj K hadj).trans (ih p.reachable)

/-- A positive-length normalized kernel edge determines the degree-two
component containing its first internal label. -/
noncomputable def CubicKernelSubdivisionDatum.positiveEdgeComponent
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    (twoGraph D.reconstructedGraph).ConnectedComponent :=
  (twoGraph D.reconstructedGraph).connectedComponentMk
    ⟨D.pathLabel e.1 ⟨0, e.2⟩,
      D.internalVertex_degree_eq_two K e.1 ⟨0, e.2⟩⟩

theorem CubicKernelSubdivisionDatum.degreeTwoKernelEdge_pathLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) :
    D.degreeTwoKernelEdge K
        ⟨D.pathLabel e i, D.internalVertex_degree_eq_two K e i⟩ = e := by
  have hs := D.degreeTwoKernelSlot_spec K
    ⟨D.pathLabel e i, D.internalVertex_degree_eq_two K e i⟩
  unfold CubicKernelSubdivisionDatum.pathLabel at hs
  have hslots := D.labels.injective hs
  have hsigma := Sum.inr.inj hslots
  exact (congrArg Sigma.fst hsigma).symm

/-- Distinct positive-length kernel edges give distinct degree-two
components. -/
theorem CubicKernelSubdivisionDatum.positiveEdgeComponent_injective
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    Function.Injective (D.positiveEdgeComponent K) := by
  intro e f hef
  have hreach : (twoGraph D.reconstructedGraph).Reachable
      ⟨D.pathLabel e.1 ⟨0, e.2⟩,
        D.internalVertex_degree_eq_two K e.1 ⟨0, e.2⟩⟩
      ⟨D.pathLabel f.1 ⟨0, f.2⟩,
        D.internalVertex_degree_eq_two K f.1 ⟨0, f.2⟩⟩ := by
    exact SimpleGraph.ConnectedComponent.eq.mp hef
  have hedge := D.degreeTwoKernelEdge_eq_of_reachable K hreach
  rw [D.degreeTwoKernelEdge_pathLabel K,
    D.degreeTwoKernelEdge_pathLabel K] at hedge
  exact Subtype.ext hedge

/-- Every degree-two connected component comes from a positive-length
normalized kernel edge. -/
theorem CubicKernelSubdivisionDatum.positiveEdgeComponent_surjective
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    Function.Surjective (D.positiveEdgeComponent K) := by
  intro C
  refine C.ind fun x ↦ ?_
  let e := D.degreeTwoKernelEdge K x
  let i := D.degreeTwoKernelIndex K x
  have hepos : 0 < (D.profile.length e).val := Nat.zero_lt_of_lt i.isLt
  refine ⟨⟨e, hepos⟩, ?_⟩
  apply SimpleGraph.ConnectedComponent.eq.mpr
  have hreach := D.internalPath_reachable_twoGraph K e ⟨0, hepos⟩ i
  have hx :
      (⟨D.pathLabel e i, D.internalVertex_degree_eq_two K e i⟩ :
        {v : Fin k // D.reconstructedGraph.degree v = 2}) = x := by
    apply Subtype.ext
    exact (D.degreeTwoKernelSlot_spec K x).symm
  simpa only [CubicKernelSubdivisionDatum.positiveEdgeComponent,
    e, i, hx] using hreach

/-- Positive-length normalized kernel edges are canonically equivalent to
the connected components of the reconstructed degree-two graph. -/
noncomputable def CubicKernelSubdivisionDatum.positiveKernelEdgeEquivTwoComponent
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    {e : Fin (3 * ell) // 0 < (D.profile.length e).val} ≃
      (twoGraph D.reconstructedGraph).ConnectedComponent :=
  Equiv.ofBijective (D.positiveEdgeComponent K)
    ⟨D.positiveEdgeComponent_injective K,
      D.positiveEdgeComponent_surjective K⟩

end PerronWright.GraphCore
