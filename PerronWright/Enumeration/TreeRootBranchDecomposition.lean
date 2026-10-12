import PerronWright.Enumeration.FixedRootedGraphProfile

/-!
# Actual all-size rooted-tree decomposition

This file isolates the part of the all-size recursion which is already
forced by the proved analytic interfaces.  For every fixed labelled tree,
its root-fixed integral is the root vertex factor times the product of the
kernel actions of its genuine root-deleted branches.

The finite combinatorial core is an explicit equivalence between labelled
trees and a partition of the non-root labels carrying one independently
rooted labelled tree on every block.  The graph assembly, both inverse
laws, and the fixed-tree analytic factorization are all proved below.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The unique vertex of a root-deleted block which was adjacent to the
deleted root.  This is only a local proof device: subsequent coefficient
formulas should eliminate it by summing over all rooted block trees. -/
noncomputable def finRootlessBranchRoot
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) : Fin n :=
  Classical.choose
    (finRootlessPartition_part_existsUnique_root_neighbor
      H hT B.1 B.2)

theorem finRootlessBranchRoot_mem
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    finRootlessBranchRoot H hT B ∈ B.1 := by
  exact (Classical.choose_spec
    (finRootlessPartition_part_existsUnique_root_neighbor
      H hT B.1 B.2)).1.1

theorem finRootlessBranchRoot_adj
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    H.Adj 0 (finRootlessBranchRoot H hT B).succ := by
  exact (Classical.choose_spec
    (finRootlessPartition_part_existsUnique_root_neighbor
      H hT B.1 B.2)).1.2

theorem finRootlessPartition_part_branchRoot
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    (finRootlessPartition n H).part (finRootlessBranchRoot H hT B) = B.1 := by
  exact (finRootlessPartition n H).part_eq_of_mem B.2
    (finRootlessBranchRoot_mem H hT B)

/-- One independently labelled branch above a block of non-root labels. -/
@[ext] structure LabelledRootBranch {n : ℕ} (B : Finset (Fin n)) where
  graph : SimpleGraph B
  isTree : graph.IsTree
  root : B

/-- The exact finite combinatorial target of root deletion: a partition of
the non-root labels and, over every block, a tree with the unique vertex
which was adjacent to the deleted root distinguished. -/
def LabelledRootBranchDecomposition (n : ℕ) :=
  Σ P : Finpartition (Finset.univ : Finset (Fin n)),
    (B : P.parts) → LabelledRootBranch B.1

/-- Assemble independent rooted branch trees on `Fin n` into a graph on
`Fin (n+1)`: retain every internal branch edge and join the new vertex `0`
to the distinguished root of every block. -/
def LabelledRootBranchDecomposition.assembleGraph
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    SimpleGraph (Fin (n + 1)) where
  Adj u v :=
    (∃ (B : D.1.parts) (x y : B.1),
      (D.2 B).graph.Adj x y ∧ u = x.1.succ ∧ v = y.1.succ) ∨
    (∃ B : D.1.parts,
      u = 0 ∧ v = (D.2 B).root.1.succ) ∨
    (∃ B : D.1.parts,
      v = 0 ∧ u = (D.2 B).root.1.succ)
  symm := ⟨by
    intro u v
    rintro (⟨B, x, y, hxy, rfl, rfl⟩ | ⟨B, rfl, rfl⟩ | ⟨B, rfl, rfl⟩)
    · exact Or.inl ⟨B, y, x, hxy.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨B, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨B, rfl, rfl⟩)⟩
  loopless := ⟨by
    intro u
    rintro (⟨B, x, y, hxy, hx, hy⟩ | ⟨B, hu, hs⟩ | ⟨B, hu, hs⟩)
    · have hval : x.1 = y.1 := Fin.succ_injective n (hx.symm.trans hy)
      have hxy' : x = y := Subtype.ext hval
      exact (D.2 B).graph.loopless.irrefl x (hxy' ▸ hxy)
    · exact (D.2 B).root.1.succ_ne_zero (hs.symm.trans hu)
    · exact (D.2 B).root.1.succ_ne_zero (hs.symm.trans hu)⟩

theorem LabelledRootBranchDecomposition.assembleGraph_adj_zero_succ
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (i : Fin n) :
    D.assembleGraph.Adj 0 i.succ ↔
      ∃ B : D.1.parts, (D.2 B).root.1 = i := by
  constructor
  · rintro (⟨B, x, y, _, hx, _⟩ | ⟨B, _, hi⟩ | ⟨B, hi, _⟩)
    · exact False.elim (x.1.succ_ne_zero hx.symm)
    · exact ⟨B, Fin.succ_injective n hi.symm⟩
    · exact False.elim (Fin.succ_ne_zero i hi)
  · rintro ⟨B, hBi⟩
    exact Or.inr (Or.inl ⟨B, rfl, (congrArg Fin.succ hBi).symm⟩)

theorem LabelledRootBranchDecomposition.assembleGraph_adj_succ_succ
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (i j : Fin n) :
    D.assembleGraph.Adj i.succ j.succ ↔
      ∃ (B : D.1.parts) (x y : B.1),
        (D.2 B).graph.Adj x y ∧ x.1 = i ∧ y.1 = j := by
  constructor
  · rintro (⟨B, x, y, hxy, hi, hj⟩ | ⟨B, hi, _⟩ | ⟨B, hj, _⟩)
    · exact ⟨B, x, y, hxy, Fin.succ_injective n hi.symm,
        Fin.succ_injective n hj.symm⟩
    · exact False.elim (Fin.succ_ne_zero i hi)
    · exact False.elim (Fin.succ_ne_zero j hj)
  · rintro ⟨B, x, y, hxy, rfl, rfl⟩
    exact Or.inl ⟨B, x, y, hxy, rfl, rfl⟩

/-- Every branch embeds into the assembled graph by shifting its original
non-root labels by one. -/
def LabelledRootBranchDecomposition.branchHom
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (B : D.1.parts) :
    (D.2 B).graph →g D.assembleGraph where
  toFun x := x.1.succ
  map_rel' hxy := Or.inl ⟨B, _, _, hxy, rfl, rfl⟩

/-- The same branch embedding before shifting the non-root labels. -/
def LabelledRootBranchDecomposition.branchRootlessHom
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (B : D.1.parts) :
    (D.2 B).graph →g D.assembleGraph.comap (Fin.succ : Fin n → Fin (n + 1)) where
  toFun x := x.1
  map_rel' hxy := Or.inl ⟨B, _, _, hxy, rfl, rfl⟩

theorem LabelledRootBranchDecomposition.internal_adj_part_eq
    {n : ℕ} (D : LabelledRootBranchDecomposition n) {i j : Fin n}
    (hij : D.assembleGraph.Adj i.succ j.succ) :
    D.1.part i = D.1.part j := by
  rw [D.assembleGraph_adj_succ_succ] at hij
  obtain ⟨B, x, y, _, hx, hy⟩ := hij
  subst i
  subst j
  exact (D.1.part_eq_of_mem B.2 x.2).trans
    (D.1.part_eq_of_mem B.2 y.2).symm

/-- Reachability after deleting the assembled root is exactly membership in
one original partition block. -/
theorem LabelledRootBranchDecomposition.rootless_reachable_iff_part_eq
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (i j : Fin n) :
    (D.assembleGraph.comap (Fin.succ : Fin n → Fin (n + 1))).Reachable i j ↔
      D.1.part i = D.1.part j := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
        exact (D.internal_adj_part_eq huv).trans ih
  · intro hij
    let B : D.1.parts :=
      ⟨D.1.part i, D.1.part_mem.mpr (Finset.mem_univ i)⟩
    have hiB : i ∈ B.1 := D.1.mem_part_self.mpr (Finset.mem_univ i)
    have hjB : j ∈ B.1 := by
      change j ∈ D.1.part i
      rw [hij]
      exact D.1.mem_part_self.mpr (Finset.mem_univ j)
    have hbranch : (D.2 B).graph.Reachable ⟨i, hiB⟩ ⟨j, hjB⟩ :=
      (D.2 B).isTree.connected _ _
    exact hbranch.map (D.branchRootlessHom B)

/-- The connected-component partition obtained after deleting the newly
assembled root is exactly the partition supplied by the branch data. -/
theorem LabelledRootBranchDecomposition.finRootlessPartition_assembleGraph
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    finRootlessPartition n D.assembleGraph = D.1 := by
  let Q := finRootlessPartition n D.assembleGraph
  have hpart (i : Fin n) : Q.part i = D.1.part i := by
    ext j
    change j ∈ (finRootlessPartition n D.assembleGraph).part i ↔
      j ∈ D.1.part i
    rw [finRootlessPartition, Finpartition.mem_part_ofSetoid_iff_rel]
    change
      (D.assembleGraph.comap (Fin.succ : Fin n → Fin (n + 1))).Reachable i j ↔
        j ∈ D.1.part i
    rw [D.1.mem_part_iff_part_eq_part
      (Finset.mem_univ j) (Finset.mem_univ i)]
    simpa only [eq_comm] using D.rootless_reachable_iff_part_eq i j
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hiB⟩ := Q.nonempty_of_mem_parts hB
    have hQi : Q.part i = B := Q.part_eq_of_mem hB hiB
    rw [← hQi, hpart]
    exact D.1.part_mem.mpr (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hiB⟩ := D.1.nonempty_of_mem_parts hB
    have hDi : D.1.part i = B := D.1.part_eq_of_mem hB hiB
    rw [← hDi, ← hpart]
    exact Q.part_mem.mpr (Finset.mem_univ i)

/-- Restricting the assembled rootless graph to one original block recovers
exactly that block's supplied tree. -/
theorem LabelledRootBranchDecomposition.induce_assembleGraph_block
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (B : D.1.parts) :
    (D.assembleGraph.comap (Fin.succ : Fin n → Fin (n + 1))).induce
        (B.1 : Set (Fin n)) =
      (D.2 B).graph := by
  ext x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  rw [D.assembleGraph_adj_succ_succ]
  constructor
  · rintro ⟨C, a, b, hab, ha, hb⟩
    have hCB : C = B := by
      apply Subtype.ext
      calc
        C.1 = D.1.part a.1 := (D.1.part_eq_of_mem C.2 a.2).symm
        _ = D.1.part x.1 := congrArg D.1.part ha
        _ = B.1 := D.1.part_eq_of_mem B.2 x.2
    subst C
    have hax : a = x := Subtype.ext ha
    have hby : b = y := Subtype.ext hb
    simpa only [hax, hby] using hab
  · intro hxy
    exact ⟨B, x, y, hxy, rfl, rfl⟩

/-- In the assembled graph, the distinguished root of a block is exactly
the unique vertex of that block adjacent to the new global root. -/
theorem LabelledRootBranchDecomposition.existsUnique_root_neighbor_in_block
    {n : ℕ} (D : LabelledRootBranchDecomposition n) (B : D.1.parts) :
    ∃! i : Fin n, i ∈ B.1 ∧ D.assembleGraph.Adj 0 i.succ := by
  refine ⟨(D.2 B).root.1, ⟨(D.2 B).root.2, ?_⟩, ?_⟩
  · exact Or.inr (Or.inl ⟨B, rfl, rfl⟩)
  · intro j hj
    rw [D.assembleGraph_adj_zero_succ] at hj
    obtain ⟨C, hCj⟩ := hj.2
    have hCB : C = B := by
      apply Subtype.ext
      calc
        C.1 = D.1.part (D.2 C).root.1 :=
          (D.1.part_eq_of_mem C.2 (D.2 C).root.2).symm
        _ = D.1.part j := congrArg D.1.part hCj
        _ = B.1 := D.1.part_eq_of_mem B.2 hj.1
    subst C
    exact hCj.symm

/-- The graph assembled from arbitrary independent rooted branch trees is
connected: each branch is internally connected and its distinguished root
has one edge to the new global root. -/
theorem LabelledRootBranchDecomposition.assembleGraph_connected
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    D.assembleGraph.Connected := by
  rw [D.assembleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  cases v using Fin.cases with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ i =>
      let B : D.1.parts :=
        ⟨D.1.part i, D.1.part_mem.mpr (Finset.mem_univ i)⟩
      have hiB : i ∈ B.1 :=
        D.1.mem_part_self.mpr (Finset.mem_univ i)
      let x : B.1 := ⟨i, hiB⟩
      have hbranch : (D.2 B).graph.Reachable (D.2 B).root x :=
        (D.2 B).isTree.connected _ _
      have hmapped := hbranch.map (D.branchHom B)
      have hroot : D.assembleGraph.Adj 0 (D.2 B).root.1.succ :=
        Or.inr (Or.inl ⟨B, rfl, rfl⟩)
      exact (SimpleGraph.Adj.reachable hroot).trans hmapped

/-- For every block, index its one new root edge by `Unit` and its internal
edges by the genuine edge set of the branch tree. -/
def LabelledRootBranchDecomposition.augmentedEdgeIndex
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :=
  Σ B : D.1.parts, Unit ⊕ (D.2 B).graph.edgeSet

instance LabelledRootBranchDecomposition.augmentedEdgeIndex_finite
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    Finite D.augmentedEdgeIndex := by
  classical
  unfold LabelledRootBranchDecomposition.augmentedEdgeIndex
  infer_instance

/-- The evident finite map from blockwise root/internal edge indices to the
edge set of the assembled graph. -/
def LabelledRootBranchDecomposition.augmentedEdgeIndexToEdge
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    D.augmentedEdgeIndex → D.assembleGraph.edgeSet
  | ⟨B, Sum.inl _⟩ =>
      ⟨s(0, (D.2 B).root.1.succ), Or.inr (Or.inl ⟨B, rfl, rfl⟩)⟩
  | ⟨B, Sum.inr e⟩ => (D.branchHom B).mapEdgeSet e

/-- Every assembled edge is either the one root edge of a block or the image
of one of that block's internal tree edges. -/
theorem LabelledRootBranchDecomposition.augmentedEdgeIndexToEdge_surjective
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    Function.Surjective D.augmentedEdgeIndexToEdge := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      change D.assembleGraph.Adj u v at he
      rcases he with
        ⟨B, x, y, hxy, rfl, rfl⟩ | ⟨B, rfl, rfl⟩ | ⟨B, rfl, rfl⟩
      · refine ⟨⟨B, Sum.inr ⟨s(x, y), hxy⟩⟩, ?_⟩
        rfl
      · refine ⟨⟨B, Sum.inl Unit.unit⟩, ?_⟩
        rfl
      · refine ⟨⟨B, Sum.inl Unit.unit⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap

/-- The augmented edge index has exactly `n` elements.  This is the finite
partition identity `sum |B| = n`, with each tree contributing `|B|-1`
internal edges and one new root edge. -/
theorem LabelledRootBranchDecomposition.card_augmentedEdgeIndex
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    Nat.card D.augmentedEdgeIndex = n := by
  classical
  have hblock (B : D.1.parts) :
      Nat.card (Unit ⊕ (D.2 B).graph.edgeSet) = B.1.card := by
    rw [Nat.card_sum, Nat.card_unique]
    have htree := (D.2 B).isTree.card_edgeFinset
    rw [SimpleGraph.edgeFinset_card] at htree
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, add_comm] using htree
  change Nat.card
      (Σ B : D.1.parts, Unit ⊕ (D.2 B).graph.edgeSet) = n
  rw [Nat.card_sigma]
  simp_rw [hblock]
  simpa only [Finset.sum_coe_sort, Finset.card_univ,
    Fintype.card_fin] using D.1.sum_card_parts

/-- The assembled graph is a tree.  Connectedness is explicit above; the
surjective `n`-element edge index bounds the edge set from above, while
connectedness bounds it from below. -/
theorem LabelledRootBranchDecomposition.assembleGraph_isTree
    {n : ℕ} (D : LabelledRootBranchDecomposition n) :
    D.assembleGraph.IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨D.assembleGraph_connected, ?_⟩
  have hu₀ : Nat.card D.assembleGraph.edgeSet ≤
      Nat.card D.augmentedEdgeIndex :=
    Nat.card_le_card_of_surjective D.augmentedEdgeIndexToEdge
      D.augmentedEdgeIndexToEdge_surjective
  have hu : Nat.card D.assembleGraph.edgeSet ≤ n :=
    hu₀.trans_eq D.card_augmentedEdgeIndex
  have hl := D.assembleGraph_connected.card_vert_le_card_edgeSet_add_one
  have hl' : n + 1 ≤ Nat.card D.assembleGraph.edgeSet + 1 := by
    simpa only [Nat.card_fin] using hl
  rw [Nat.card_fin]
  omega

/-- Root deletion gives the forward direction of the finite combinatorial
equivalence. -/
noncomputable def treeRootBranchFamily
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) :
    (B : (finRootlessPartition n H).parts) → LabelledRootBranch B.1 :=
  fun B =>
    { graph := (H.comap (Fin.succ : Fin n → Fin (n + 1))).induce
        (B.1 : Set (Fin n))
      isTree := by
        have hpart := finRootlessPartition_part_branchRoot H hT B
        rw [← hpart]
        exact finRootlessPartition_part_isTree n H hT
          (finRootlessBranchRoot H hT B)
      root := ⟨finRootlessBranchRoot H hT B,
        finRootlessBranchRoot_mem H hT B⟩ }

noncomputable def treeRootBranchDecomposition
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) :
    LabelledRootBranchDecomposition n :=
  ⟨finRootlessPartition n H, treeRootBranchFamily H hT⟩

@[simp] theorem treeRootBranchDecomposition_fst
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) :
    (treeRootBranchDecomposition H hT).1 = finRootlessPartition n H := rfl

@[simp] theorem treeRootBranchDecomposition_root_val
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    ((treeRootBranchDecomposition H hT).2 B).root.1 =
      finRootlessBranchRoot H hT B := rfl

@[simp] theorem treeRootBranchDecomposition_graph
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    ((treeRootBranchDecomposition H hT).2 B).graph =
      (H.comap (Fin.succ : Fin n → Fin (n + 1))).induce
        (B.1 : Set (Fin n)) := rfl

theorem exists_finRootlessBranchRoot_eq_iff_adj
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) :
    (∃ B : (finRootlessPartition n H).parts,
        finRootlessBranchRoot H hT B = i) ↔ H.Adj 0 i.succ := by
  let P := finRootlessPartition n H
  constructor
  · rintro ⟨B, hBi⟩
    rw [← hBi]
    exact finRootlessBranchRoot_adj H hT B
  · intro hi
    let B : P.parts :=
      ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩
    have hroot := Classical.choose_spec
      (finRootlessPartition_part_existsUnique_root_neighbor
        H hT B.1 B.2)
    have hiB : i ∈ B.1 := P.mem_part_self.mpr (Finset.mem_univ i)
    exact ⟨B, (hroot.2 i ⟨hiB, hi⟩).symm⟩

theorem exists_treeRootBranch_internal_adj_iff
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i j : Fin n) :
    (∃ (B : (finRootlessPartition n H).parts) (x y : B.1),
        ((treeRootBranchDecomposition H hT).2 B).graph.Adj x y ∧
          x.1 = i ∧ y.1 = j) ↔
      H.Adj i.succ j.succ := by
  constructor
  · rintro ⟨B, x, y, hxy, rfl, rfl⟩
    rw [treeRootBranchDecomposition_graph] at hxy
    exact hxy
  · intro hij
    let P := finRootlessPartition n H
    let B : P.parts :=
      ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩
    have hijpart := finRootless_adj_same_part H i j hij
    have hiB : i ∈ B.1 := P.mem_part_self.mpr (Finset.mem_univ i)
    have hjB : j ∈ B.1 := by
      change j ∈ P.part i
      rw [hijpart]
      exact P.mem_part_self.mpr (Finset.mem_univ j)
    have hxy :
        ((treeRootBranchDecomposition H hT).2 B).graph.Adj
          ⟨i, hiB⟩ ⟨j, hjB⟩ := by
      rw [treeRootBranchDecomposition_graph]
      exact hij
    exact ⟨B, ⟨i, hiB⟩, ⟨j, hjB⟩, hxy, rfl, rfl⟩

/-- The graph assembled from the actual root-deletion data has exactly the
original adjacency relation.  This is the graph-level `forward_inverse`
half of the finite equivalence; it does not use any analytic data. -/
theorem assembleGraph_treeRootBranchDecomposition
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) :
    (treeRootBranchDecomposition H hT).assembleGraph = H := by
  ext u v
  cases u using Fin.cases with
  | zero =>
      cases v using Fin.cases with
      | zero => simp
      | succ j =>
          rw [LabelledRootBranchDecomposition.assembleGraph_adj_zero_succ]
          change (∃ B : (finRootlessPartition n H).parts,
            finRootlessBranchRoot H hT B = j) ↔ H.Adj 0 j.succ
          exact exists_finRootlessBranchRoot_eq_iff_adj H hT j
  | succ i =>
      cases v using Fin.cases with
      | zero =>
          rw [(treeRootBranchDecomposition H hT).assembleGraph.adj_comm,
            H.adj_comm]
          rw [LabelledRootBranchDecomposition.assembleGraph_adj_zero_succ]
          change (∃ B : (finRootlessPartition n H).parts,
            finRootlessBranchRoot H hT B = i) ↔ H.Adj 0 i.succ
          exact exists_finRootlessBranchRoot_eq_iff_adj H hT i
      | succ j =>
          rw [LabelledRootBranchDecomposition.assembleGraph_adj_succ_succ]
          exact exists_treeRootBranch_internal_adj_iff H hT i j

/-- The two maps underlying the finite equivalence. -/
noncomputable def labelledTreeToRootBranchDecomposition (n : ℕ) :
    {H : SimpleGraph (Fin (n + 1)) // H.IsTree} →
      LabelledRootBranchDecomposition n :=
  fun H => treeRootBranchDecomposition H.1 H.2

noncomputable def rootBranchDecompositionToLabelledTree (n : ℕ) :
    LabelledRootBranchDecomposition n →
      {H : SimpleGraph (Fin (n + 1)) // H.IsTree} :=
  fun D => ⟨D.assembleGraph, D.assembleGraph_isTree⟩

/-- Assembling the root-deletion data of a genuine labelled tree returns
that tree. -/
theorem rootBranchDecompositionToLabelledTree_leftInverse (n : ℕ) :
    Function.LeftInverse
      (rootBranchDecompositionToLabelledTree n)
      (labelledTreeToRootBranchDecomposition n) := by
  intro H
  apply Subtype.ext
  exact assembleGraph_treeRootBranchDecomposition H.1 H.2

/-- Root deletion of a graph assembled from independent branches returns
the original dependent partition/branch data. -/
theorem rootBranchDecompositionToLabelledTree_rightInverse (n : ℕ) :
    Function.RightInverse
      (rootBranchDecompositionToLabelledTree n)
      (labelledTreeToRootBranchDecomposition n) := by
  intro D
  change treeRootBranchDecomposition D.assembleGraph
      D.assembleGraph_isTree = D
  have hP : finRootlessPartition n D.assembleGraph = D.1 :=
    D.finRootlessPartition_assembleGraph
  apply Sigma.ext hP
  change HEq
    (treeRootBranchFamily D.assembleGraph D.assembleGraph_isTree) D.2
  have hparts :
      (finRootlessPartition n D.assembleGraph).parts = D.1.parts :=
    congrArg Finpartition.parts hP
  have hdom :
      ((finRootlessPartition n D.assembleGraph).parts : Type) =
        (D.1.parts : Type) :=
    congrArg (fun s : Finset (Finset (Fin n)) => (s : Type)) hparts
  apply Function.hfunext hdom
  intro B C hBC
  have hmem (A : Finset (Fin n)) :
      A ∈ (finRootlessPartition n D.assembleGraph).parts ↔
        A ∈ D.1.parts := by
    rw [hparts]
  have hBCval : B.1 = C.1 :=
    (Subtype.heq_iff_coe_eq hmem).mp hBC
  let C' : D.1.parts := ⟨B.1, (hmem B.1).mp B.2⟩
  have hC : C' = C := Subtype.ext hBCval
  subst C
  apply heq_of_eq
  apply LabelledRootBranch.ext
  · exact D.induce_assembleGraph_block C'
  · apply Subtype.ext
    have hspec := Classical.choose_spec
      (finRootlessPartition_part_existsUnique_root_neighbor
        D.assembleGraph D.assembleGraph_isTree B.1 B.2)
    have hrootAdj :
        D.assembleGraph.Adj 0 (D.2 C').root.1.succ :=
      Or.inr (Or.inl ⟨C', rfl, rfl⟩)
    exact (hspec.2 (D.2 C').root.1
      ⟨(D.2 C').root.2, hrootAdj⟩).symm

/-- Exact finite equivalence implementing labelled root deletion and
reassembly. -/
noncomputable def labelledTreeEquivRootBranchDecomposition (n : ℕ) :
    {H : SimpleGraph (Fin (n + 1)) // H.IsTree} ≃
      LabelledRootBranchDecomposition n where
  toFun := labelledTreeToRootBranchDecomposition n
  invFun := rootBranchDecompositionToLabelledTree n
  left_inv := rootBranchDecompositionToLabelledTree_leftInverse n
  right_inv := rootBranchDecompositionToLabelledTree_rightInverse n

/-- Canonically relabel one independently labelled branch by `Fin |B|` and
view its distinguished vertex as the parent-facing root. -/
noncomputable def LabelledRootBranch.profileMap
    (M : CompactBJRModel S) {n : ℕ} {B : Finset (Fin n)}
    (T : LabelledRootBranch B) : C(S, ℝ) :=
  M.fixedRootedFinGraphProfileMap
    (T.graph.comap (B.equivFin.symm : Fin B.card → B))
    (B.equivFin T.root)

/-- The branch profile agrees with the relabelled root-block profile once
the distinguished root and its partition block have been identified.  The
root label `i` is an independent argument here so that the block equality
can be eliminated without creating a circular dependent transport. -/
theorem CompactBJRModel.treeRootBranch_profileMap_eq_of_root
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) (i : Fin n)
    (hi : ((treeRootBranchDecomposition H hT).2 B).root.1 = i)
    (hpart : (finRootlessPartition n H).part i = B.1) :
    LabelledRootBranch.profileMap M
        ((treeRootBranchDecomposition H hT).2 B) =
      M.relabelledRootBlockTreeProfileMap H i := by
  let C : (finRootlessPartition n H).parts :=
    ⟨(finRootlessPartition n H).part i,
      (finRootlessPartition n H).part_mem.mpr (Finset.mem_univ i)⟩
  have hCB : C = B := Subtype.ext hpart
  subst B
  have hroot :
      ((treeRootBranchDecomposition H hT).2 C).root =
        ⟨i, (finRootlessPartition n H).mem_part_self.mpr
          (Finset.mem_univ i)⟩ := by
    apply Subtype.ext
    exact hi
  unfold LabelledRootBranch.profileMap
    CompactBJRModel.relabelledRootBlockTreeProfileMap
  rw [treeRootBranchDecomposition_graph, hroot]
  unfold finRootlessBlockTreeGraph
  rfl

/-- On genuine tree data, the independent branch profile is exactly the
already-constructed relabelled root-block profile. -/
theorem CompactBJRModel.treeRootBranch_profileMap_eq
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    LabelledRootBranch.profileMap M
        ((treeRootBranchDecomposition H hT).2 B) =
      M.relabelledRootBlockTreeProfileMap H
        (finRootlessBranchRoot H hT B) := by
  apply M.treeRootBranch_profileMap_eq_of_root H hT B
  · exact treeRootBranchDecomposition_root_val H hT B
  · exact finRootlessPartition_part_branchRoot H hT B

/-- Exact all-size root decomposition for one genuine labelled tree. -/
theorem CompactBJRModel.zeroTree_integral_eq_rootBranch_kernelActions
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) (root : S) :
    (∫ z : Fin n → S,
      M.fieldGraphWeightIntegrand 0 H (Fin.cons root z)
        ∂Measure.pi (fun _ : Fin n => M.mu)) =
      M.zeroTreeVertexFactor root *
        ∏ B : (finRootlessPartition n H).parts,
          M.kernel.action M.mu
            (M.relabelledRootBlockTreeProfileMap H
              (finRootlessBranchRoot H hT B)) root := by
  rw [M.zeroTree_integral_root_block_partition H root]
  congr 1
  apply Fintype.prod_congr
  intro B
  have hpart := finRootlessPartition_part_branchRoot H hT B
  have hadj := finRootlessBranchRoot_adj H hT B
  have hblock :=
    M.tree_rootBlock_integral_eq_kernel_action H hT
      (finRootlessBranchRoot H hT B) hadj root
  rw [hpart] at hblock
  exact hblock

/-- The actual rooted-tree numerator after the already-proved analytic
factorization.  Every term is still indexed by its original tree; the next
combinatorial module must reindex this finite sum by labelled partitions and
independent rooted block trees. -/
theorem CompactBJRModel.rootedTreeNumerator_eq_sum_rootBranch_kernelActions
    (M : CompactBJRModel S) (n : ℕ) (root : S) :
    M.rootedTreeNumerator n root =
      ∑ H : SimpleGraph (Fin (n + 1)),
        if hT : H.IsTree then
          M.zeroTreeVertexFactor root *
            ∏ B : (finRootlessPartition n H).parts,
              M.kernel.action M.mu
                (M.relabelledRootBlockTreeProfileMap H
                  (finRootlessBranchRoot H hT B)) root
        else 0 := by
  classical
  unfold CompactBJRModel.rootedTreeNumerator
  apply Finset.sum_congr rfl
  intro H _
  split
  next hT =>
    simpa only [Fin.insertNth_zero'] using
      M.zeroTree_integral_eq_rootBranch_kernelActions H hT root
  next hT => rfl

end PerronWright
