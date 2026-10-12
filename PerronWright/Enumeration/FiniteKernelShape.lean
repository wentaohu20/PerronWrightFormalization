import PerronWright.Enumeration.KernelTotalEdges

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Finite, edge-labelled multigraph endpoint tables on the extremal
numbers of branch vertices and edges at surplus `ell`.  Loops and
parallel edges are retained by `Sym2` and the edge-label function. -/
abbrev CubicKernelShape (ell : ℕ) :=
  Fin (3 * ell) → Sym2 (Fin (2 * ell))

theorem cubicKernelShape_finite (ell : ℕ) :
    Finite (CubicKernelShape ell) := inferInstance

/-- Lift an unordered endpoint pair to a vertex subset when both
endpoints lie in that subset. -/
def sym2ToSubtype {V : Type*} (s : Set V) (p : Sym2 V)
    (h : ∀ v ∈ p, v ∈ s) : Sym2 s := by
  let ab : V × V := Classical.choose (Sym2.mk_surjective p)
  have hab : s(ab.1, ab.2) = p :=
    Classical.choose_spec (Sym2.mk_surjective p)
  have ha : ab.1 ∈ s := h ab.1 (hab ▸ (by simp))
  have hb : ab.2 ∈ s := h ab.2 (hab ▸ (by simp))
  exact s(⟨ab.1, ha⟩, ⟨ab.2, hb⟩)

theorem sym2ToSubtype_map_val {V : Type*} (s : Set V)
    (p : Sym2 V) (h : ∀ v ∈ p, v ∈ s) :
    Sym2.map Subtype.val (sym2ToSubtype s p h) = p := by
  unfold sym2ToSubtype
  simp only [Sym2.map_mk]
  exact Classical.choose_spec (Sym2.mk_surjective p)

/-- Every actual suppressed-kernel endpoint pair lifts to the
subtype of original branch vertices, including both ends of a loop. -/
def kernelBranchEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (e : KernelEdgeLabel G) : Sym2 (branchingVertices G : Set V) :=
  sym2ToSubtype (branchingVertices G : Set V)
    (kernelEdgeEndpoints G hacyc e)
    (fun _v hv => kernelEdgeEndpoints_mem_branchingVertices G hmin hacyc e hv)

theorem kernelBranchEndpoints_map_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (e : KernelEdgeLabel G) :
    Sym2.map Subtype.val (kernelBranchEndpoints G hmin hacyc e) =
      kernelEdgeEndpoints G hacyc e :=
  sym2ToSubtype_map_val _ _ _

/-- A cubic core with surplus `ell` yields an honest finite endpoint
table after independently relabelling its original branch vertices
and its original kernel-edge labels. -/
def normalizedCubicKernelShape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3) :
    CubicKernelShape ell := by
  let B := branchingVertices G
  let hacyc := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hB : B.card = 2 * ell :=
    (branchingVertices_card_eq_two_surplus_iff_cubic G hmin hs).mpr hcubic
  have hE : Nat.card (KernelEdgeLabel G) = 3 * ell :=
    (kernelEdgeLabel_card_eq_three_surplus_iff_cubic G hconn hmin hell hs).mpr hcubic
  letI : Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent :=
    Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  let eB : B ≃ Fin (2 * ell) := Finset.equivFinOfCardEq hB
  let eE : KernelEdgeLabel G ≃ Fin (3 * ell) := by
    apply Fintype.equivFinOfCardEq
    simpa only [Nat.card_eq_fintype_card] using hE
  exact fun i => Sym2.map eB
    (kernelBranchEndpoints G hmin hacyc (eE.symm i))

#print axioms PerronWright.GraphCore.sym2ToSubtype_map_val
#print axioms PerronWright.GraphCore.kernelBranchEndpoints_map_val
#print axioms PerronWright.GraphCore.cubicKernelShape_finite
#print axioms PerronWright.GraphCore.normalizedCubicKernelShape

end PerronWright.GraphCore

