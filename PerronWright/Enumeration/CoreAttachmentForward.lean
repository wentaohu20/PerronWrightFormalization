import PerronWright.Enumeration.CoreAttachmentAssembly
import PerronWright.Enumeration.KernelEdgeCount

/-!
# The forward greatest-two-core attachment classification

This file proves the remaining structural input needed to recover a
`LabelledCoreForestAttachment` from an arbitrary connected graph of positive
paper surplus: every component outside the canonical greatest two-core has
exactly one boundary edge to that core.  The proof uses the actual finite
edge sets and connected components, not an assumed classification fibre.
-/

open scoped Classical
noncomputable section

namespace PerronWright.GraphCore

/-- The edge sets of the connected components partition the edge set of a
finite graph.  This numerical form is useful independently of the core
application below. -/
theorem sum_connectedComponent_edgeFinset_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [Fintype H.ConnectedComponent] :
    (∑ C : H.ConnectedComponent, C.toSimpleGraph.edgeFinset.card) =
      H.edgeFinset.card := by
  have htwice :
      2 * (∑ C : H.ConnectedComponent,
          C.toSimpleGraph.edgeFinset.card) =
        2 * H.edgeFinset.card := by
    calc
      2 * (∑ C : H.ConnectedComponent,
          C.toSimpleGraph.edgeFinset.card) =
          ∑ C : H.ConnectedComponent,
            2 * C.toSimpleGraph.edgeFinset.card := by
              rw [Finset.mul_sum]
      _ = ∑ C : H.ConnectedComponent,
            ∑ x : C, C.toSimpleGraph.degree x := by
              apply Finset.sum_congr rfl
              intro C _
              rw [C.toSimpleGraph.sum_degrees_eq_twice_card_edges]
      _ = ∑ C : H.ConnectedComponent,
            ∑ x : C, H.degree x.val := by
              apply Finset.sum_congr rfl
              intro C _
              apply Finset.sum_congr rfl
              intro x _
              exact connectedComponent_degree_eq H C x
      _ = ∑ v : V, H.degree v :=
            sum_over_connected_components H (fun v => H.degree v)
      _ = 2 * H.edgeFinset.card :=
            H.sum_degrees_eq_twice_card_edges
  exact Nat.mul_left_cancel (n := 2) (by omega) htwice

/-- Euler's formula for an arbitrary finite forest, stated using the actual
connected-component type. -/
theorem acyclic_components_add_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [Fintype H.ConnectedComponent]
    (hacyc : H.IsAcyclic) :
    Nat.card H.ConnectedComponent + H.edgeFinset.card = Fintype.card V := by
  have hedge := sum_connectedComponent_edgeFinset_card_eq H
  have hcomponent (C : H.ConnectedComponent) :
      C.toSimpleGraph.edgeFinset.card + 1 = Fintype.card C :=
    (hacyc.isTree_connectedComponent C).card_edgeFinset
  have hvertices :
      (∑ C : H.ConnectedComponent, Fintype.card C) = Fintype.card V := by
    calc
      (∑ C : H.ConnectedComponent, Fintype.card C) =
          ∑ C : H.ConnectedComponent, ∑ _x : C, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro C _
            simp
      _ = ∑ _v : V, (1 : ℕ) :=
            sum_over_connected_components H (fun _ => 1)
      _ = Fintype.card V := by simp
  have hsum := congrArg (fun f : H.ConnectedComponent → ℕ =>
      ∑ C : H.ConnectedComponent, f C) (funext hcomponent)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  have hresult : Fintype.card H.ConnectedComponent + H.edgeFinset.card =
      Fintype.card V := by
    calc
      Fintype.card H.ConnectedComponent + H.edgeFinset.card =
          (∑ C : H.ConnectedComponent,
            C.toSimpleGraph.edgeFinset.card) +
              Fintype.card H.ConnectedComponent := by
            rw [hedge, Nat.add_comm]
      _ = ∑ C : H.ConnectedComponent, Fintype.card C := hsum
      _ = Fintype.card V := hvertices
  calc
    Nat.card H.ConnectedComponent + H.edgeFinset.card =
        Fintype.card H.ConnectedComponent + H.edgeFinset.card := by
          congr 1
          exact Nat.card_eq_fintype_card
    _ = Fintype.card V := hresult

/-- The labels surviving a maximal leaf pruning are canonically equivalent
to the vertices of the greatest two-core. -/
def LeafPruning.terminalCoreEquiv
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    Fin p.terminalCount ≃ (greatestTwoCore G : Set (Fin k)) :=
  Equiv.ofBijective
    (fun i =>
      (⟨p.terminalLabels i, by
        rw [← p.terminalLabels_range_eq_greatestTwoCore hconn hell hs]
        exact ⟨i, rfl⟩⟩ : (greatestTwoCore G : Set (Fin k))))
    ⟨by
      intro i j hij
      exact p.terminalLabels.injective (congrArg Subtype.val hij),
     by
      intro x
      have hx : x.1 ∈ Set.range p.terminalLabels := by
        rw [p.terminalLabels_range_eq_greatestTwoCore hconn hell hs]
        exact x.2
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Leaf pruning does not merely preserve surplus abstractly: the terminal
graph is canonically isomorphic to the graph induced by the original graph on
its greatest two-core. -/
def LeafPruning.terminalCoreIso
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    p.terminalGraph ≃g G.induce (greatestTwoCore G) := by
  let e := p.terminalCoreEquiv hconn hell hs
  refine { e with map_rel_iff' := ?_ }
  intro i j
  rw [p.terminalGraph_eq_comap]
  rfl

/-- The literal induced greatest two-core has the same paper surplus as the
ambient connected graph. -/
theorem greatestTwoCore_surplus
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    (G.induce (greatestTwoCore G)).edgeFinset.card + 1 =
      Fintype.card (greatestTwoCore G) + ell := by
  let p := LeafPruning.pruneAll k G
  have hterminal := p.terminal_surplus hs
  have hiso := p.terminalCoreIso hconn hell hs
  rw [hiso.card_edgeFinset_eq] at hterminal
  have hcard : Fintype.card (Fin p.terminalCount) =
      Fintype.card (greatestTwoCore G) :=
    Fintype.card_congr (p.terminalCoreEquiv hconn hell hs)
  simpa only [hcard] using hterminal

/-- Removing the greatest two-core from a connected positive-surplus graph
removes exactly one edge for every removed vertex. -/
theorem edge_deficit_greatestTwoCore
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    G.edgeFinset.card =
      (G.induce (greatestTwoCore G)).edgeFinset.card +
        Fintype.card ((greatestTwoCore G)ᶜ : Set (Fin k)) := by
  have hcore := greatestTwoCore_surplus G hconn hell hs
  have hsplit : Fintype.card (Fin k) =
      Fintype.card (greatestTwoCore G) +
        Fintype.card ((greatestTwoCore G)ᶜ : Set (Fin k)) := by
    have hcompl := Fintype.card_compl_set (greatestTwoCore G)
    have hle : Fintype.card (greatestTwoCore G) ≤ Fintype.card (Fin k) :=
      Fintype.card_subtype_le _
    omega
  omega

/-- The actual ambient edges crossing a vertex set.  It is convenient to
define this as the part remaining after deleting the two internal induced
edge sets; this avoids orienting an unordered edge prematurely. -/
def crossingEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) : Finset (Sym2 V) :=
  (G.edgeFinset.filter
      (fun e => ¬e.toFinset ⊆ s.toFinset)).filter
    (fun e => ¬e.toFinset ⊆ s.toFinsetᶜ)

/-- The subtype cut out by a finite set and the subtype cut out by its
underlying set carry literally the same induced graph, up to the canonical
set-congruence equivalence. -/
def induceToFinsetIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) :
    G.induce (↑s.toFinset : Set V) ≃g G.induce s := by
  let e : (↑s.toFinset : Set V) ≃ s :=
    Equiv.setCongr (Set.coe_toFinset s)
  refine { e with map_rel_iff' := ?_ }
  intro x y
  rfl

/-- The finite-set complement of `s.toFinset` and the set complement of `s`
give canonically isomorphic induced graphs.  Using the former consistently
avoids introducing a second decidability instance for membership in `sᶜ`. -/
def induceToFinsetComplIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Set V) :
    G.induce (↑s.toFinsetᶜ : Set V) ≃g G.induce sᶜ := by
  let e : (↑s.toFinsetᶜ : Set V) ≃ (sᶜ : Set V) :=
    Equiv.setCongr (by
      ext v
      simp only [Finset.coe_compl, Set.coe_toFinset])
  refine { e with map_rel_iff' := ?_ }
  intro x y
  rfl

/-- Every finite graph's edges split disjointly into the edges internal to a
set, those internal to its complement, and the crossing edges. -/
theorem edgeFinset_card_eq_induce_add_induce_compl_add_crossing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) :
    G.edgeFinset.card =
      (G.induce s).edgeFinset.card +
        (G.induce sᶜ).edgeFinset.card +
          (crossingEdgeFinset G s).card := by
  let p : Sym2 V → Prop := fun e => e.toFinset ⊆ s.toFinset
  let q : Sym2 V → Prop := fun e => e.toFinset ⊆ s.toFinsetᶜ
  have hpSplit := G.edgeFinset.card_filter_add_card_filter_not p
  have hqSplit :=
    (G.edgeFinset.filter (fun e => ¬p e)).card_filter_add_card_filter_not q
  have hqInternal :
      (G.edgeFinset.filter (fun e => ¬p e)).filter q =
        G.edgeFinset.filter q := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨he, _⟩, hq⟩
      exact ⟨he, hq⟩
    · rintro ⟨he, hq⟩
      refine ⟨⟨he, ?_⟩, hq⟩
      intro hp
      obtain ⟨v, hv⟩ : e.toFinset.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
      have hvs : v ∈ s := by
        simpa only [Set.mem_toFinset] using hp hv
      have hvnot : v ∉ s := by
        simpa only [Finset.mem_compl, Set.mem_toFinset] using hq hv
      exact hvnot hvs
  have hcore := G.card_filter_edgeFinset_toFinset_subset s.toFinset
  have hoff := G.card_filter_edgeFinset_toFinset_subset s.toFinsetᶜ
  change (G.edgeFinset.filter p).card +
      (G.edgeFinset.filter fun e => ¬p e).card = G.edgeFinset.card at hpSplit
  change ((G.edgeFinset.filter fun e => ¬p e).filter q).card +
      ((G.edgeFinset.filter fun e => ¬p e).filter fun e => ¬q e).card =
        (G.edgeFinset.filter fun e => ¬p e).card at hqSplit
  have hcross :
      (G.edgeFinset.filter (fun e => ¬p e)).filter (fun e => ¬q e) =
        crossingEdgeFinset G s := rfl
  have hcore' : (G.edgeFinset.filter p).card =
      (G.induce s).edgeFinset.card := by
    calc
      (G.edgeFinset.filter p).card =
          (G.induce (↑s.toFinset : Set V)).edgeFinset.card := by
            simpa only [p] using hcore
      _ = (G.induce s).edgeFinset.card :=
            (induceToFinsetIso G s).card_edgeFinset_eq
  have hoff' : (G.edgeFinset.filter q).card =
      (G.induce sᶜ).edgeFinset.card := by
    calc
      (G.edgeFinset.filter q).card =
          (G.induce (↑s.toFinsetᶜ : Set V)).edgeFinset.card := by
            simpa only [q] using hoff
      _ = (G.induce sᶜ).edgeFinset.card :=
            (induceToFinsetComplIso G s).card_edgeFinset_eq
  rw [hcore'] at hpSplit
  rw [hqInternal, hcross, hoff'] at hqSplit
  omega

/-- The number of crossing edges from the complement of the greatest
two-core is exactly the number of components of that complement. -/
theorem greatestTwoCore_crossingEdges_card
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    (crossingEdgeFinset G (greatestTwoCore G)).card =
      Nat.card (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent := by
  let H := G.induce (greatestTwoCore G)ᶜ
  have hforest := acyclic_components_add_edges H
    (greatestTwoCore_compl_isAcyclic G)
  have hdecomp :=
    edgeFinset_card_eq_induce_add_induce_compl_add_crossing G
      (greatestTwoCore G)
  have hdeficit := edge_deficit_greatestTwoCore G hconn hell hs
  change Nat.card H.ConnectedComponent + H.edgeFinset.card =
    Fintype.card ((greatestTwoCore G)ᶜ : Set (Fin k)) at hforest
  change G.edgeFinset.card =
    (G.induce (greatestTwoCore G)).edgeFinset.card +
      H.edgeFinset.card +
        (crossingEdgeFinset G (greatestTwoCore G)).card at hdecomp
  have hremaining : H.edgeFinset.card +
      (crossingEdgeFinset G (greatestTwoCore G)).card =
        Fintype.card ((greatestTwoCore G)ᶜ : Set (Fin k)) := by
    omega
  have heq : H.edgeFinset.card +
      (crossingEdgeFinset G (greatestTwoCore G)).card =
        H.edgeFinset.card + Nat.card H.ConnectedComponent := by
    calc
      H.edgeFinset.card +
          (crossingEdgeFinset G (greatestTwoCore G)).card =
          Fintype.card ((greatestTwoCore G)ᶜ : Set (Fin k)) := hremaining
      _ = Nat.card H.ConnectedComponent + H.edgeFinset.card := hforest.symm
      _ = H.edgeFinset.card + Nat.card H.ConnectedComponent := Nat.add_comm _ _
  exact Nat.add_left_cancel heq

/-- An oriented boundary edge, with the endpoint outside the greatest
two-core listed first.  The orientation is canonical because the two endpoint
types are disjoint. -/
@[ext] structure GreatestCoreBoundaryEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  outside : ((greatestTwoCore G)ᶜ : Set V)
  inside : (greatestTwoCore G : Set V)
  adj : G.Adj outside.1 inside.1

/-- Forget the canonical orientation and regard a core-boundary incidence as
an unordered crossing edge. -/
def GreatestCoreBoundaryEdge.toCrossingEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : GreatestCoreBoundaryEdge G) :
    crossingEdgeFinset G (greatestTwoCore G) := by
  refine ⟨s(b.outside.1, b.inside.1), ?_⟩
  simp only [crossingEdgeFinset, Finset.mem_filter]
  refine ⟨⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr b.adj), ?_⟩, ?_⟩
  · intro hsub
    have houtFin : b.outside.1 ∈ (greatestTwoCore G).toFinset := by
      apply hsub
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton,
        true_or]
    have hout : b.outside.1 ∈ greatestTwoCore G := by
      simpa only [Set.mem_toFinset] using houtFin
    exact b.outside.2 hout
  · intro hsub
    have hinFin : b.inside.1 ∈ (greatestTwoCore G).toFinsetᶜ := by
      apply hsub
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton,
        or_true]
    have hin : b.inside.1 ∉ greatestTwoCore G := by
      simpa only [Finset.mem_compl, Set.mem_toFinset] using hinFin
    exact hin b.inside.2

theorem GreatestCoreBoundaryEdge.toCrossingEdge_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (GreatestCoreBoundaryEdge.toCrossingEdge G) := by
  intro a b hab
  have hpair := congrArg Subtype.val hab
  change s(a.outside.1, a.inside.1) =
    s(b.outside.1, b.inside.1) at hpair
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hdirect | hswap
  · apply GreatestCoreBoundaryEdge.ext
    · exact Subtype.ext hdirect.1
    · exact Subtype.ext hdirect.2
  · exfalso
    apply a.outside.2
    rw [hswap.1]
    exact b.inside.2

theorem GreatestCoreBoundaryEdge.toCrossingEdge_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Surjective (GreatestCoreBoundaryEdge.toCrossingEdge G) := by
  rintro ⟨e, he⟩
  simp only [crossingEdgeFinset, Finset.mem_filter] at he
  rcases he with ⟨⟨heEdge, hnotCore⟩, hnotCompl⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj : G.Adj u v :=
        G.mem_edgeSet.mp (G.mem_edgeFinset.mp heEdge)
      by_cases hu : u ∈ greatestTwoCore G
      · have hv : v ∉ greatestTwoCore G := by
          intro hv
          apply hnotCore
          intro z hz
          rw [Sym2.toFinset_mk_eq] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simpa only [Set.mem_toFinset] using hu
          · simpa only [Set.mem_toFinset] using hv
        let b : GreatestCoreBoundaryEdge G :=
          { outside := ⟨v, by simpa only [Set.mem_compl_iff] using hv⟩
            inside := ⟨u, hu⟩
            adj := hadj.symm }
        refine ⟨b, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap
      · have hv : v ∈ greatestTwoCore G := by
          by_contra hv
          apply hnotCompl
          intro z hz
          rw [Sym2.toFinset_mk_eq] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simpa only [Finset.mem_compl, Set.mem_toFinset] using hu
          · simpa only [Finset.mem_compl, Set.mem_toFinset] using hv
        let b : GreatestCoreBoundaryEdge G :=
          { outside := ⟨u, by simpa only [Set.mem_compl_iff] using hu⟩
            inside := ⟨v, hv⟩
            adj := hadj }
        exact ⟨b, rfl⟩

/-- Boundary incidences and unordered crossing edges are canonically
equivalent; no representative or fibre is chosen. -/
def greatestCoreBoundaryEdgeEquivCrossing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    GreatestCoreBoundaryEdge G ≃
      crossingEdgeFinset G (greatestTwoCore G) :=
  Equiv.ofBijective (GreatestCoreBoundaryEdge.toCrossingEdge G)
    ⟨GreatestCoreBoundaryEdge.toCrossingEdge_injective G,
      GreatestCoreBoundaryEdge.toCrossingEdge_surjective G⟩

noncomputable instance greatestCoreBoundaryEdgeFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype (GreatestCoreBoundaryEdge G) :=
  Fintype.ofEquiv (crossingEdgeFinset G (greatestTwoCore G))
    (greatestCoreBoundaryEdgeEquivCrossing G).symm

/-- Send a boundary edge to the outside connected component containing its
outside endpoint. -/
def GreatestCoreBoundaryEdge.component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : GreatestCoreBoundaryEdge G) :
    (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent :=
  (G.induce (greatestTwoCore G)ᶜ).connectedComponentMk b.outside

/-- Connectedness and nonemptiness of the core make the boundary-to-component
map surjective. -/
theorem GreatestCoreBoundaryEdge.component_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : (greatestTwoCore G).Nonempty) :
    Function.Surjective (GreatestCoreBoundaryEdge.component G) := by
  intro C
  obtain ⟨x, y, hy, hxC, hxy⟩ :=
    greatestTwoCore_compl_component_exists_core_edge G hconn hcore C
  exact ⟨{ outside := x, inside := ⟨y, hy⟩, adj := hxy }, hxC⟩

/-- In a connected positive-surplus graph, the boundary-to-component map is
bijective.  Numerically, the forest Euler deficit says that the number of
crossing edges equals the number of outside components; the preceding
surjectivity then supplies injectivity for free. -/
theorem GreatestCoreBoundaryEdge.component_bijective
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    Function.Bijective (GreatestCoreBoundaryEdge.component G) := by
  have hcore : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn hell hs
  have hsurj := GreatestCoreBoundaryEdge.component_surjective G hconn hcore
  have hcross := greatestTwoCore_crossingEdges_card G hconn hell hs
  have hboundary : Fintype.card (GreatestCoreBoundaryEdge G) =
      (crossingEdgeFinset G (greatestTwoCore G)).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_congr (greatestCoreBoundaryEdgeEquivCrossing G)
  have hcard : Fintype.card (GreatestCoreBoundaryEdge G) =
      Fintype.card (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent := by
    rw [Nat.card_eq_fintype_card] at hcross
    rw [hboundary, hcross]
  exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩

/-- Every outside component has exactly one edge to the greatest two-core.
This is the missing structural theorem needed by the genuine forward
attachment construction. -/
theorem greatestTwoCore_compl_component_existsUnique_core_boundary
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell)
    (C : (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent) :
    ∃! b : GreatestCoreBoundaryEdge G, b.component G = C :=
  (GreatestCoreBoundaryEdge.component_bijective G hconn hell hs).existsUnique C

end PerronWright.GraphCore
