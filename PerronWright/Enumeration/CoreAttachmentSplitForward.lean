import PerronWright.Enumeration.CoreAttachmentForward

/-!
# Forward rooted-forest attachment data for an already split core

This module constructs the genuine forward attachment datum for a
connected positive-surplus graph whose labels have already been split as
`Fin q ⊕ Fin n`, with the left labels equal to the greatest two-core.
The construction uses the actual reachable-component partition of the
right labels and the unique genuine core-boundary edge of each component.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-! ## Relabelling the positive-surplus boundary theorem -/

/-- Membership in the greatest two-core is invariant under relabelling by
an equivalence, in pointwise form. -/
theorem mem_greatestTwoCore_comap_equiv_iff
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (G : SimpleGraph B) [DecidableRel G.Adj] (x : A) :
    x ∈ greatestTwoCore (G.comap e) ↔ e x ∈ greatestTwoCore G := by
  have himage := greatestTwoCore_image_equiv e G
  constructor
  · intro hx
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  · intro hx
    have hx' : e x ∈ e '' greatestTwoCore (G.comap e) := by
      rw [himage]
      exact hx
    obtain ⟨y, hy, hey⟩ := hx'
    exact (e.injective hey) ▸ hy

/-- Relabelling restricts to an isomorphism between the two literal induced
greatest two-cores. -/
def greatestTwoCoreInduceIsoEquiv
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (G : SimpleGraph B) [DecidableRel G.Adj] :
    (G.comap e).induce (greatestTwoCore (G.comap e)) ≃g
      G.induce (greatestTwoCore G) := by
  let eCore : (greatestTwoCore (G.comap e) : Set A) ≃
      (greatestTwoCore G : Set B) :=
    e.subtypeEquiv (fun x ↦ mem_greatestTwoCore_comap_equiv_iff e G x)
  refine { eCore with map_rel_iff' := ?_ }
  intro x y
  rfl

set_option linter.style.haveILetI false in
/-- The literal greatest two-core has the same positive paper surplus for a
connected graph on an arbitrary finite vertex type.  This is the relabelled
form of `greatestTwoCore_surplus`. -/
theorem greatestTwoCore_surplus_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    (G.induce (greatestTwoCore G)).edgeFinset.card + 1 =
      Fintype.card (greatestTwoCore G) + ell := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let K : SimpleGraph (Fin (Fintype.card V)) := G.comap e
  letI : DecidableRel K.Adj := fun i j ↦
    Classical.propDecidable (K.Adj i j)
  let φ : K ≃g G := SimpleGraph.Iso.comap e G
  have hconnK : K.Connected := φ.connected_iff.mpr hconn
  have hsK : K.edgeFinset.card + 1 =
      Fintype.card (Fin (Fintype.card V)) + ell := by
    rw [φ.card_edgeFinset_eq, Fintype.card_fin]
    exact hs
  have hK := greatestTwoCore_surplus K hconnK hell hsK
  let φCore : K.induce (greatestTwoCore K) ≃g
      G.induce (greatestTwoCore G) := by
    simpa only [K] using greatestTwoCoreInduceIsoEquiv e G
  have hcoreCard : Fintype.card (greatestTwoCore K) =
      Fintype.card (greatestTwoCore G) :=
    Fintype.card_congr φCore.toEquiv
  rw [φCore.card_edgeFinset_eq, hcoreCard] at hK
  exact hK

/-- Removing the greatest two-core removes exactly one edge for every
removed vertex, for any finite vertex type. -/
theorem edge_deficit_greatestTwoCore_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    G.edgeFinset.card =
      (G.induce (greatestTwoCore G)).edgeFinset.card +
        Fintype.card ((greatestTwoCore G)ᶜ : Set V) := by
  have hcore := greatestTwoCore_surplus_finite G hconn hell hs
  have hsplit : Fintype.card V =
      Fintype.card (greatestTwoCore G) +
        Fintype.card ((greatestTwoCore G)ᶜ : Set V) := by
    have hcompl := Fintype.card_compl_set (greatestTwoCore G)
    have hle : Fintype.card (greatestTwoCore G) ≤ Fintype.card V :=
      Fintype.card_subtype_le _
    omega
  omega

/-- The number of edges crossing the greatest two-core is the number of
off-core components, for an arbitrary finite vertex type. -/
theorem greatestTwoCore_crossingEdges_card_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    (crossingEdgeFinset G (greatestTwoCore G)).card =
      Nat.card (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent := by
  let H := G.induce (greatestTwoCore G)ᶜ
  have hforest := acyclic_components_add_edges H
    (greatestTwoCore_compl_isAcyclic G)
  have hdecomp :=
    edgeFinset_card_eq_induce_add_induce_compl_add_crossing G
      (greatestTwoCore G)
  have hdeficit := edge_deficit_greatestTwoCore_finite G hconn hell hs
  change Nat.card H.ConnectedComponent + H.edgeFinset.card =
    Fintype.card ((greatestTwoCore G)ᶜ : Set V) at hforest
  change G.edgeFinset.card =
    (G.induce (greatestTwoCore G)).edgeFinset.card +
      H.edgeFinset.card +
        (crossingEdgeFinset G (greatestTwoCore G)).card at hdecomp
  have hremaining : H.edgeFinset.card +
      (crossingEdgeFinset G (greatestTwoCore G)).card =
        Fintype.card ((greatestTwoCore G)ᶜ : Set V) := by
    omega
  have heq : H.edgeFinset.card +
      (crossingEdgeFinset G (greatestTwoCore G)).card =
        H.edgeFinset.card + Nat.card H.ConnectedComponent := by
    calc
      H.edgeFinset.card +
          (crossingEdgeFinset G (greatestTwoCore G)).card =
          Fintype.card ((greatestTwoCore G)ᶜ : Set V) := hremaining
      _ = Nat.card H.ConnectedComponent + H.edgeFinset.card := hforest.symm
      _ = H.edgeFinset.card + Nat.card H.ConnectedComponent := Nat.add_comm _ _
  exact Nat.add_left_cancel heq

/-- The actual boundary-edge-to-component map is bijective on an arbitrary
finite vertex type. -/
theorem GreatestCoreBoundaryEdge.component_bijective_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    Function.Bijective (GreatestCoreBoundaryEdge.component G) := by
  have hcore : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn hell hs
  have hsurj := GreatestCoreBoundaryEdge.component_surjective G hconn hcore
  have hcross := greatestTwoCore_crossingEdges_card_finite G hconn hell hs
  have hboundary : Fintype.card (GreatestCoreBoundaryEdge G) =
      (crossingEdgeFinset G (greatestTwoCore G)).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_congr (greatestCoreBoundaryEdgeEquivCrossing G)
  have hcard : Fintype.card (GreatestCoreBoundaryEdge G) =
      Fintype.card (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent := by
    rw [Nat.card_eq_fintype_card] at hcross
    rw [hboundary, hcross]
  exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩

/-- Boundary edges are canonically equivalent to off-core connected
components. -/
def greatestCoreBoundaryEdgeEquivComponentFinite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    GreatestCoreBoundaryEdge G ≃
      (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent :=
  Equiv.ofBijective (GreatestCoreBoundaryEdge.component G)
    (GreatestCoreBoundaryEdge.component_bijective_finite G hconn hell hs)

/-! ## The split core and off-core graphs -/

/-- The ordered left labels are canonically the vertices of the greatest
two-core. -/
def splitCoreEquiv {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    Fin q ≃ (greatestTwoCore G : Set (Fin q ⊕ Fin n)) :=
  Equiv.ofBijective
    (fun i ↦ ⟨Sum.inl i, by rw [hcore]; exact ⟨i, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact Sum.inl_injective (congrArg Subtype.val hij),
     by
      intro x
      have hx : x.1 ∈ Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n) := by
        rw [← hcore]
        exact x.2
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, Subtype.ext hi⟩⟩

/-- The ordered right labels are canonically the complement of the greatest
two-core. -/
def splitOffEquiv {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    Fin n ≃ ((greatestTwoCore G)ᶜ : Set (Fin q ⊕ Fin n)) :=
  Equiv.ofBijective
    (fun i ↦ ⟨Sum.inr i, by
      rw [Set.mem_compl_iff, hcore]
      rintro ⟨j, h⟩
      exact Sum.inl_ne_inr h⟩)
    ⟨by
      intro i j hij
      exact Sum.inr_injective (congrArg Subtype.val hij),
     by
      rintro ⟨x, hx⟩
      rcases x with i | j
      · exfalso
        apply hx
        rw [hcore]
        exact ⟨i, rfl⟩
      · exact ⟨j, rfl⟩⟩

/-- The graph on the left labels is the induced greatest two-core. -/
def splitCoreIso {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    G.comap (Sum.inl : Fin q → Fin q ⊕ Fin n) ≃g
      G.induce (greatestTwoCore G) := by
  refine { splitCoreEquiv G hcore with map_rel_iff' := ?_ }
  intro i j
  rfl

/-- The graph on the right labels is the graph induced on the complement of
the greatest two-core. -/
def splitOffIso {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n) ≃g
      G.induce (greatestTwoCore G)ᶜ := by
  refine { splitOffEquiv G hcore with map_rel_iff' := ?_ }
  intro i j
  rfl

/-- The right-labelled graph is a forest. -/
theorem splitOffGraph_isAcyclic
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).IsAcyclic :=
  (splitOffIso G hcore).isAcyclic_iff.mpr
    (greatestTwoCore_compl_isAcyclic G)

/-! ## The actual right-component partition and its tree blocks -/

/-- The partition of the right labels into the actual connected components
of the off-core graph. -/
def splitAttachmentPartition {q n : ℕ}
    (G : SimpleGraph (Fin q ⊕ Fin n)) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.ofSetoid
    (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).reachableSetoid

theorem splitAttachmentPartition_mem_part_iff_reachable
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n)) (i j : Fin n) :
    j ∈ (splitAttachmentPartition G).part i ↔
      (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).Reachable i j := by
  rw [splitAttachmentPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- A deterministic representative of an actual off-core block. -/
def splitAttachmentBlockRep
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) : Fin n :=
  B.1.min' ((splitAttachmentPartition G).nonempty_of_mem_parts B.2)

theorem splitAttachmentBlockRep_mem
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    splitAttachmentBlockRep G B ∈ B.1 := by
  exact Finset.min'_mem B.1
    ((splitAttachmentPartition G).nonempty_of_mem_parts B.2)

/-- The right-label component represented by a partition block, transported
to the literal complement of the greatest two-core. -/
def splitAttachmentBlockComponent
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent :=
  (splitOffIso G hcore).connectedComponentEquiv
    ((G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).connectedComponentMk
      (splitAttachmentBlockRep G B))

/-- Every label in a block maps to that block's literal off-core connected
component. -/
theorem splitOff_component_eq_blockComponent
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) (i : Fin n)
    (hi : i ∈ B.1) :
    (G.induce (greatestTwoCore G)ᶜ).connectedComponentMk
        (splitOffEquiv G hcore i) =
      splitAttachmentBlockComponent G hcore B := by
  let H := G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)
  have hrep : splitAttachmentBlockRep G B ∈ B.1 :=
    splitAttachmentBlockRep_mem G B
  have hpart : (splitAttachmentPartition G).part
      (splitAttachmentBlockRep G B) = B.1 :=
    (splitAttachmentPartition G).part_eq_of_mem B.2 hrep
  have hreach : H.Reachable (splitAttachmentBlockRep G B) i := by
    rw [← splitAttachmentPartition_mem_part_iff_reachable]
    rw [hpart]
    exact hi
  have hcomponent : H.connectedComponentMk i =
      H.connectedComponentMk (splitAttachmentBlockRep G B) :=
    (SimpleGraph.ConnectedComponent.sound hreach).symm
  change (splitOffIso G hcore).connectedComponentEquiv
      (H.connectedComponentMk i) =
    (splitOffIso G hcore).connectedComponentEquiv
      (H.connectedComponentMk (splitAttachmentBlockRep G B))
  exact congrArg (splitOffIso G hcore).connectedComponentEquiv hcomponent

/-- Each actual right-label block carries the induced off-core tree. -/
theorem splitAttachmentBlock_isTree
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    ((G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).induce
      (B.1 : Set (Fin n))).IsTree := by
  let H := G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)
  let b := splitAttachmentBlockRep G B
  let C : H.ConnectedComponent := H.connectedComponentMk b
  have hb : b ∈ B.1 := splitAttachmentBlockRep_mem G B
  have hpart : (splitAttachmentPartition G).part b = B.1 :=
    (splitAttachmentPartition G).part_eq_of_mem B.2 hb
  have hset : (B.1 : Set (Fin n)) = C.supp := by
    ext i
    change i ∈ B.1 ↔ H.connectedComponentMk i = C
    rw [← hpart, splitAttachmentPartition_mem_part_iff_reachable]
    change H.Reachable b i ↔
      H.connectedComponentMk i = H.connectedComponentMk b
    rw [SimpleGraph.ConnectedComponent.eq]
    exact H.reachable_comm
  rw [hset]
  exact (splitOffGraph_isAcyclic G hcore).isTree_connectedComponent C

/-! ## The genuine forward attachment and exact recovery -/

/-- The unique actual boundary edge of an off-core block. -/
def splitAttachmentBoundary
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    GreatestCoreBoundaryEdge G :=
  (greatestCoreBoundaryEdgeEquivComponentFinite G hconn hell hs).symm
    (splitAttachmentBlockComponent G hcore B)

theorem splitAttachmentBoundary_component
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    (splitAttachmentBoundary G hconn hell hs hcore B).component G =
      splitAttachmentBlockComponent G hcore B := by
  exact (greatestCoreBoundaryEdgeEquivComponentFinite G hconn hell hs).apply_symm_apply _

/-- Core label incident with a block's unique boundary edge. -/
def splitAttachmentCoreIndex
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) : Fin q :=
  (splitCoreEquiv G hcore).symm
    (splitAttachmentBoundary G hconn hell hs hcore B).inside

/-- Off-core label incident with a block's unique boundary edge. -/
def splitAttachmentRootIndex
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) : Fin n :=
  (splitOffEquiv G hcore).symm
    (splitAttachmentBoundary G hconn hell hs hcore B).outside

theorem splitAttachmentRootIndex_mem
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    splitAttachmentRootIndex G hconn hell hs hcore B ∈ B.1 := by
  let b := splitAttachmentBoundary G hconn hell hs hcore B
  let i := splitAttachmentRootIndex G hconn hell hs hcore B
  have hbcomp : b.component G = splitAttachmentBlockComponent G hcore B :=
    splitAttachmentBoundary_component G hconn hell hs hcore B
  have hiapply : splitOffEquiv G hcore i = b.outside := by
    exact (splitOffEquiv G hcore).apply_symm_apply b.outside
  have hcomponent :
      (G.induce (greatestTwoCore G)ᶜ).connectedComponentMk
          (splitOffEquiv G hcore i) =
        splitAttachmentBlockComponent G hcore B := by
    rw [hiapply]
    exact hbcomp
  have hrep : splitAttachmentBlockRep G B ∈ B.1 :=
    splitAttachmentBlockRep_mem G B
  have hrepComponent :=
    splitOff_component_eq_blockComponent G hcore B
      (splitAttachmentBlockRep G B) hrep
  have hoffComponent :
      (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).connectedComponentMk i =
        (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).connectedComponentMk
          (splitAttachmentBlockRep G B) := by
    apply (splitOffIso G hcore).connectedComponentEquiv.injective
    exact hcomponent.trans hrepComponent.symm
  have hreach :
      (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).Reachable
        (splitAttachmentBlockRep G B) i :=
    SimpleGraph.ConnectedComponent.exact hoffComponent.symm
  have himem : i ∈ (splitAttachmentPartition G).part
      (splitAttachmentBlockRep G B) :=
    (splitAttachmentPartition_mem_part_iff_reachable G _ _).2 hreach
  have hpart : (splitAttachmentPartition G).part
      (splitAttachmentBlockRep G B) = B.1 :=
    (splitAttachmentPartition G).part_eq_of_mem B.2 hrep
  rwa [hpart] at himem

/-- The rooted tree carried by an actual off-core block. -/
def splitAttachmentBranch
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) : LabelledRootBranch B.1 where
  graph :=
    (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).induce
      (B.1 : Set (Fin n))
  isTree := splitAttachmentBlock_isTree G hcore B
  root := ⟨splitAttachmentRootIndex G hconn hell hs hcore B,
    splitAttachmentRootIndex_mem G hconn hell hs hcore B⟩

/-- Genuine rooted-forest attachment data extracted from a graph whose core
and off-core labels have already been split. -/
def forwardSplitCoreAttachment
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    LabelledCoreForestAttachment q n :=
  ⟨splitAttachmentPartition G, fun B ↦
    (splitAttachmentCoreIndex G hconn hell hs hcore B,
      splitAttachmentBranch G hconn hell hs hcore B)⟩

/-- An ambient core--off-core edge is exactly the boundary selected for the
block containing its off-core endpoint. -/
theorem splitAttachmentBoundary_eq_of_adj
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) (c : Fin q) (i : Fin n)
    (hi : i ∈ B.1) (hci : G.Adj (Sum.inl c) (Sum.inr i)) :
    splitAttachmentBoundary G hconn hell hs hcore B =
      { outside := splitOffEquiv G hcore i
        inside := splitCoreEquiv G hcore c
        adj := hci.symm } := by
  let b : GreatestCoreBoundaryEdge G :=
    { outside := splitOffEquiv G hcore i
      inside := splitCoreEquiv G hcore c
      adj := hci.symm }
  apply (GreatestCoreBoundaryEdge.component_bijective_finite
    G hconn hell hs).1
  rw [splitAttachmentBoundary_component]
  exact (splitOff_component_eq_blockComponent G hcore B i hi).symm

theorem forwardSplitCoreAttachment_adj_off_off
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (i j : Fin n) :
    ((forwardSplitCoreAttachment G hconn hell hs hcore).assembleGraph
      (G.comap (Sum.inl : Fin q → Fin q ⊕ Fin n))).Adj
        (Sum.inr i) (Sum.inr j) ↔ G.Adj (Sum.inr i) (Sum.inr j) := by
  rw [LabelledCoreForestAttachment.assembleGraph_adj_off_off]
  constructor
  · rintro ⟨B, x, y, hxy, rfl, rfl⟩
    change
      ((G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).induce
        (B.1 : Set (Fin n))).Adj x y at hxy
    exact hxy
  · intro hij
    let P := splitAttachmentPartition G
    let B : P.parts :=
      ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩
    have hi : i ∈ B.1 := P.mem_part_self.mpr (Finset.mem_univ i)
    have hj : j ∈ B.1 := by
      have hreach :
          (G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)).Reachable i j :=
        SimpleGraph.Adj.reachable hij
      change j ∈ P.part i
      exact (splitAttachmentPartition_mem_part_iff_reachable G i j).2 hreach
    exact ⟨B, ⟨i, hi⟩, ⟨j, hj⟩, hij, rfl, rfl⟩

theorem forwardSplitCoreAttachment_adj_core_off
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (c : Fin q) (i : Fin n) :
    ((forwardSplitCoreAttachment G hconn hell hs hcore).assembleGraph
      (G.comap (Sum.inl : Fin q → Fin q ⊕ Fin n))).Adj
        (Sum.inl c) (Sum.inr i) ↔ G.Adj (Sum.inl c) (Sum.inr i) := by
  rw [LabelledCoreForestAttachment.assembleGraph_adj_core_off]
  constructor
  · rintro ⟨B, hc, hi⟩
    change splitAttachmentCoreIndex G hconn hell hs hcore B = c at hc
    change splitAttachmentRootIndex G hconn hell hs hcore B = i at hi
    let b := splitAttachmentBoundary G hconn hell hs hcore B
    have hout : b.outside.1 =
        Sum.inr (splitAttachmentRootIndex G hconn hell hs hcore B) := by
      have h := congrArg Subtype.val
        ((splitOffEquiv G hcore).apply_symm_apply b.outside)
      exact h.symm
    have hin : b.inside.1 =
        Sum.inl (splitAttachmentCoreIndex G hconn hell hs hcore B) := by
      have h := congrArg Subtype.val
        ((splitCoreEquiv G hcore).apply_symm_apply b.inside)
      exact h.symm
    rw [← hc, ← hi]
    simpa only [hout, hin] using b.adj.symm
  · intro hci
    let P := splitAttachmentPartition G
    let B : P.parts :=
      ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩
    have hiB : i ∈ B.1 := P.mem_part_self.mpr (Finset.mem_univ i)
    have hboundary :=
      splitAttachmentBoundary_eq_of_adj G hconn hell hs hcore B c i hiB hci
    refine ⟨B, ?_, ?_⟩
    · change splitAttachmentCoreIndex G hconn hell hs hcore B = c
      unfold splitAttachmentCoreIndex
      rw [hboundary]
      exact (splitCoreEquiv G hcore).symm_apply_apply c
    · change splitAttachmentRootIndex G hconn hell hs hcore B = i
      unfold splitAttachmentRootIndex
      rw [hboundary]
      exact (splitOffEquiv G hcore).symm_apply_apply i

/-- Within each actual off-core block there is exactly one incident
core--off-core edge.  Its endpoints are precisely the stored core colour and
the stored branch root. -/
theorem splitAttachmentBlock_existsUnique_core_edge
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n))
    (B : (splitAttachmentPartition G).parts) :
    ∃! z : Fin q × B.1,
      G.Adj (Sum.inl z.1) (Sum.inr z.2.1) := by
  let c := splitAttachmentCoreIndex G hconn hell hs hcore B
  let r : B.1 :=
    ⟨splitAttachmentRootIndex G hconn hell hs hcore B,
      splitAttachmentRootIndex_mem G hconn hell hs hcore B⟩
  refine ⟨(c, r), ?_, ?_⟩
  · apply (forwardSplitCoreAttachment_adj_core_off
      G hconn hell hs hcore c r.1).mp
    exact ⟨B, rfl, rfl⟩
  · intro z hz
    have hboundary := splitAttachmentBoundary_eq_of_adj
      G hconn hell hs hcore B z.1 z.2.1 z.2.2 hz
    apply Prod.ext
    · have hin := congrArg
          (fun b : GreatestCoreBoundaryEdge G ↦
            (splitCoreEquiv G hcore).symm b.inside) hboundary
      simpa only [c, splitAttachmentCoreIndex,
        Equiv.symm_apply_apply] using hin.symm
    · apply Subtype.ext
      have hout := congrArg
        (fun b : GreatestCoreBoundaryEdge G ↦
          (splitOffEquiv G hcore).symm b.outside) hboundary
      simpa only [r, splitAttachmentRootIndex,
        Equiv.symm_apply_apply] using hout.symm

/-- Exact recovery: assembling the genuine forward attachment over the
induced ordered core returns the original split graph literally. -/
theorem assembleGraph_forwardSplitCoreAttachment
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hconn : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin q ⊕ Fin n) + ell)
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    (forwardSplitCoreAttachment G hconn hell hs hcore).assembleGraph
      (G.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)) = G := by
  ext u v
  rcases u with c | i <;> rcases v with d | j
  · rfl
  · exact forwardSplitCoreAttachment_adj_core_off
      G hconn hell hs hcore c j
  · simpa only [SimpleGraph.adj_comm] using
      forwardSplitCoreAttachment_adj_core_off
        G hconn hell hs hcore d i
  · exact forwardSplitCoreAttachment_adj_off_off
      G hconn hell hs hcore i j

end GraphCore
end PerronWright
