import PerronWright.Enumeration.CoreForestAttachments
import PerronWright.Enumeration.CoreTerminal

/-!
# A fixed ordered core with genuine labelled rooted-tree attachments

This file supplies the assembly/recovery half of the graph--core
classification.  No representative of an unspecified fibre is chosen:
the graph is assembled explicitly from a fixed ordered core and the actual
partition/rooted-tree data of `LabelledCoreForestAttachment`.

The converse construction from an arbitrary positive-surplus connected
graph is deliberately left for the next layer.  It requires the separate
structural theorem that the complement of the greatest two-core is a forest
and that every one of its components has exactly one edge to the core.
-/

open scoped Classical
noncomputable section

namespace PerronWright

namespace GraphCore

/-- A walk starting outside a set and ending inside it has a first boundary
edge.  The outside endpoint remains reachable from the starting point in
the graph induced by the complement. -/
theorem walk_from_compl_to_set_has_boundary
    {V : Type*} {G : SimpleGraph V} {s : Set V} {a b : V}
    (p : G.Walk a b) (ha : a ∉ s) (hb : b ∈ s) :
    ∃ x : (sᶜ : Set V), ∃ y : V,
      y ∈ s ∧ G.Adj x.1 y ∧
        (G.induce sᶜ).Reachable
          (⟨a, by simpa⟩ : (sᶜ : Set V)) x := by
  induction p with
  | nil => exact False.elim (ha hb)
  | @cons u v w huv p ih =>
      by_cases hv : v ∈ s
      · exact ⟨⟨u, by simpa using ha⟩, v, hv, huv,
          SimpleGraph.Reachable.rfl⟩
      · obtain ⟨x, y, hy, hxy, hreach⟩ := ih hv hb
        have huv' : (G.induce sᶜ).Adj
            (⟨u, by simpa using ha⟩ : (sᶜ : Set V))
            (⟨v, by simpa using hv⟩ : (sᶜ : Set V)) := huv
        exact ⟨x, y, hy, hxy,
          (SimpleGraph.Adj.reachable huv').trans hreach⟩

/-- The graph induced away from the canonical greatest two-core is a
forest.  A cycle outside the core would itself supply a two-neighbor set,
contradicting maximality of the core. -/
theorem greatestTwoCore_compl_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.induce (greatestTwoCore G)ᶜ).IsAcyclic := by
  intro v c hcycle
  let m := c.length
  have hm : 3 ≤ m := hcycle.three_le_length
  have hcontained :
      SimpleGraph.IsContained (SimpleGraph.cycleGraph m)
        (G.induce (greatestTwoCore G)ᶜ) :=
    (SimpleGraph.cycleGraph_isContained_iff hm).mpr
      ⟨v, c, hcycle, rfl⟩
  obtain ⟨f⟩ := hcontained
  have houtside :
      IsTwoCore (G.induce (greatestTwoCore G)ᶜ) (Set.range f) :=
    isTwoCore_copy_range (G.induce (greatestTwoCore G)ᶜ)
      (SimpleGraph.cycleGraph m) f (cycleGraph_isTwoCore m hm)
  have hlift : IsTwoCore G (Subtype.val '' Set.range f) :=
    isTwoCore_image_subtype G houtside
  have hmax : Subtype.val '' Set.range f ⊆ greatestTwoCore G :=
    isTwoCore_subset_greatest G hlift
  let i : Fin m := ⟨0, by omega⟩
  have himage : (f i : V) ∈ Subtype.val '' Set.range f :=
    ⟨f i, ⟨i, rfl⟩, rfl⟩
  exact (f i).property (hmax himage)

/-- Consequently every connected component outside the canonical core is
a genuine tree. -/
theorem greatestTwoCore_compl_component_isTree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent) :
    C.toSimpleGraph.IsTree :=
  (greatestTwoCore_compl_isAcyclic G).isTree_connectedComponent C

/-- In a connected graph with nonempty core, every component outside the
core has at least one edge to the core. -/
theorem greatestTwoCore_compl_component_exists_core_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcore : (greatestTwoCore G).Nonempty)
    (C : (G.induce (greatestTwoCore G)ᶜ).ConnectedComponent) :
    ∃ x : ((greatestTwoCore G)ᶜ : Set V), ∃ y : V,
      y ∈ greatestTwoCore G ∧
        (G.induce (greatestTwoCore G)ᶜ).connectedComponentMk x = C ∧
        G.Adj x.1 y := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep C
  obtain ⟨y, hy⟩ := hcore
  obtain ⟨p⟩ := hconn a.1 y
  obtain ⟨x, z, hz, hxz, hreach⟩ :=
    walk_from_compl_to_set_has_boundary p a.2 hy
  exact ⟨x, z, hz,
    (SimpleGraph.ConnectedComponent.sound hreach).symm, hxz⟩

end GraphCore

/-- Assemble a fixed ordered core and a finite labelled rooted forest.

The left summand contains the ordered core labels.  The right summand
contains the off-core labels.  Besides the core and branch-tree edges there
is exactly one root edge for every partition block. -/
def LabelledCoreForestAttachment.assembleGraph
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    SimpleGraph (Fin q ⊕ Fin n) where
  Adj u v :=
    match u, v with
    | Sum.inl i, Sum.inl j => H.Adj i j
    | Sum.inr i, Sum.inr j =>
        ∃ (B : D.1.parts) (x y : B.1),
          (D.2 B).2.graph.Adj x y ∧ x.1 = i ∧ y.1 = j
    | Sum.inl c, Sum.inr i =>
        ∃ B : D.1.parts,
          (D.2 B).1 = c ∧ (D.2 B).2.root.1 = i
    | Sum.inr i, Sum.inl c =>
        ∃ B : D.1.parts,
          (D.2 B).1 = c ∧ (D.2 B).2.root.1 = i
  symm := ⟨by
    intro u v
    rcases u with i | i <;> rcases v with j | j
    · intro hij
      exact hij.symm
    · rintro ⟨B, hc, hi⟩
      exact ⟨B, hc, hi⟩
    · rintro ⟨B, hc, hi⟩
      exact ⟨B, hc, hi⟩
    · rintro ⟨B, x, y, hxy, hx, hy⟩
      exact ⟨B, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨by
    intro u
    rcases u with i | i
    · exact H.loopless.irrefl i
    · rintro ⟨B, x, y, hxy, hx, hy⟩
      have hval : x.1 = y.1 := hx.trans hy.symm
      have hxy' : x = y := Subtype.ext hval
      exact (D.2 B).2.graph.loopless.irrefl x (hxy' ▸ hxy)⟩

@[simp] theorem LabelledCoreForestAttachment.assembleGraph_adj_core_core
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (i j : Fin q) :
    (D.assembleGraph H).Adj (Sum.inl i) (Sum.inl j) ↔ H.Adj i j :=
  Iff.rfl

@[simp] theorem LabelledCoreForestAttachment.assembleGraph_adj_core_off
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (c : Fin q) (i : Fin n) :
    (D.assembleGraph H).Adj (Sum.inl c) (Sum.inr i) ↔
      ∃ B : D.1.parts,
        (D.2 B).1 = c ∧ (D.2 B).2.root.1 = i :=
  Iff.rfl

@[simp] theorem LabelledCoreForestAttachment.assembleGraph_adj_off_core
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (i : Fin n) (c : Fin q) :
    (D.assembleGraph H).Adj (Sum.inr i) (Sum.inl c) ↔
      ∃ B : D.1.parts,
        (D.2 B).1 = c ∧ (D.2 B).2.root.1 = i :=
  Iff.rfl

@[simp] theorem LabelledCoreForestAttachment.assembleGraph_adj_off_off
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (i j : Fin n) :
    (D.assembleGraph H).Adj (Sum.inr i) (Sum.inr j) ↔
      ∃ (B : D.1.parts) (x y : B.1),
        (D.2 B).2.graph.Adj x y ∧ x.1 = i ∧ y.1 = j :=
  Iff.rfl

/-- The core embeds as a graph homomorphism into the assembled graph. -/
def LabelledCoreForestAttachment.coreHom
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    H →g D.assembleGraph H where
  toFun := Sum.inl
  map_rel' hij := hij

/-- Every supplied rooted branch embeds on the right labels. -/
def LabelledCoreForestAttachment.branchHom
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (B : D.1.parts) :
    (D.2 B).2.graph →g D.assembleGraph H where
  toFun x := Sum.inr x.1
  map_rel' hxy := ⟨B, _, _, hxy, rfl, rfl⟩

/-- A branch homomorphism directly into the graph on off-core labels. -/
def LabelledCoreForestAttachment.offBranchHom
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (B : D.1.parts) :
    (D.2 B).2.graph →g
      (D.assembleGraph H).comap (Sum.inr : Fin n → Fin q ⊕ Fin n) where
  toFun x := x.1
  map_rel' hxy := ⟨B, _, _, hxy, rfl, rfl⟩

/-- Restriction to the left summand recovers the supplied core literally. -/
theorem LabelledCoreForestAttachment.comap_inl_assembleGraph
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    (D.assembleGraph H).comap (Sum.inl : Fin q → Fin q ⊕ Fin n) = H := by
  ext i j
  rfl

/-- An off-core edge cannot cross two partition blocks. -/
theorem LabelledCoreForestAttachment.off_adj_part_eq
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) {i j : Fin n}
    (hij : (D.assembleGraph H).Adj (Sum.inr i) (Sum.inr j)) :
    D.1.part i = D.1.part j := by
  obtain ⟨B, x, y, _, hx, hy⟩ := hij
  subst i
  subst j
  exact (D.1.part_eq_of_mem B.2 x.2).trans
    (D.1.part_eq_of_mem B.2 y.2).symm

/-- Reachability inside the off-core induced graph is exactly equality of
the original partition blocks.  Thus the partition is recoverable from the
assembled graph without any arbitrary representative choice. -/
theorem LabelledCoreForestAttachment.off_reachable_iff_part_eq
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (i j : Fin n) :
    ((D.assembleGraph H).comap
        (Sum.inr : Fin n → Fin q ⊕ Fin n)).Reachable i j ↔
      D.1.part i = D.1.part j := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
        exact (D.off_adj_part_eq H huv).trans ih
  · intro hij
    let B : D.1.parts :=
      ⟨D.1.part i, D.1.part_mem.mpr (Finset.mem_univ i)⟩
    have hiB : i ∈ B.1 := D.1.mem_part_self.mpr (Finset.mem_univ i)
    have hjB : j ∈ B.1 := by
      change j ∈ D.1.part i
      rw [hij]
      exact D.1.mem_part_self.mpr (Finset.mem_univ j)
    have hbranch : (D.2 B).2.graph.Reachable ⟨i, hiB⟩ ⟨j, hjB⟩ :=
      (D.2 B).2.isTree.connected _ _
    exact hbranch.map (D.offBranchHom H B)

/-- Restriction of the off-core graph to one block recovers that block's
actual supplied tree. -/
theorem LabelledCoreForestAttachment.induce_off_assembleGraph_block
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (B : D.1.parts) :
    ((D.assembleGraph H).comap
        (Sum.inr : Fin n → Fin q ⊕ Fin n)).induce
        (B.1 : Set (Fin n)) =
      (D.2 B).2.graph := by
  ext x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  rw [D.assembleGraph_adj_off_off]
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

/-- A block contributes exactly one edge to the core, namely from its
chosen core colour to its distinguished tree root. -/
theorem LabelledCoreForestAttachment.existsUnique_core_edge_in_block
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (B : D.1.parts) :
    ∃! z : Fin q × Fin n,
      z.2 ∈ B.1 ∧
        (D.assembleGraph H).Adj (Sum.inl z.1) (Sum.inr z.2) := by
  let z : Fin q × Fin n := ((D.2 B).1, (D.2 B).2.root.1)
  refine ⟨z, ⟨(D.2 B).2.root.2, ?_⟩, ?_⟩
  · exact ⟨B, rfl, rfl⟩
  · intro z' hz'
    obtain ⟨C, hcolor, hroot⟩ := hz'.2
    have hCB : C = B := by
      apply Subtype.ext
      calc
        C.1 = D.1.part (D.2 C).2.root.1 :=
          (D.1.part_eq_of_mem C.2 (D.2 C).2.root.2).symm
        _ = D.1.part z'.2 := congrArg D.1.part hroot
        _ = B.1 := D.1.part_eq_of_mem B.2 hz'.1
    subst C
    apply Prod.ext
    · exact hcolor.symm
    · exact hroot.symm

/-- Equality of assembled graphs forces equality of the off-core component
partitions.  This is the partition-recovery half of injectivity. -/
theorem LabelledCoreForestAttachment.partition_eq_of_assembleGraph_eq
    {q n : ℕ} {H H' : SimpleGraph (Fin q)}
    (D E : LabelledCoreForestAttachment q n)
    (hgraph : D.assembleGraph H = E.assembleGraph H') :
    D.1 = E.1 := by
  have hoff :
      (D.assembleGraph H).comap
          (Sum.inr : Fin n → Fin q ⊕ Fin n) =
        (E.assembleGraph H').comap
          (Sum.inr : Fin n → Fin q ⊕ Fin n) :=
    congrArg
      (fun G : SimpleGraph (Fin q ⊕ Fin n) =>
        G.comap (Sum.inr : Fin n → Fin q ⊕ Fin n)) hgraph
  have hrel (i j : Fin n) :
      D.1.part i = D.1.part j ↔ E.1.part i = E.1.part j := by
    rw [← D.off_reachable_iff_part_eq H,
      ← E.off_reachable_iff_part_eq H', hoff]
  have hpart (i : Fin n) : D.1.part i = E.1.part i := by
    ext j
    rw [D.1.mem_part_iff_part_eq_part
        (Finset.mem_univ j) (Finset.mem_univ i),
      E.1.mem_part_iff_part_eq_part
        (Finset.mem_univ j) (Finset.mem_univ i)]
    simpa only [eq_comm] using hrel i j
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hiB⟩ := D.1.nonempty_of_mem_parts hB
    have hDi : D.1.part i = B := D.1.part_eq_of_mem hB hiB
    rw [← hDi, hpart]
    exact E.1.part_mem.mpr (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hiB⟩ := E.1.nonempty_of_mem_parts hB
    have hEi : E.1.part i = B := E.1.part_eq_of_mem hB hiB
    rw [← hEi, ← hpart]
    exact D.1.part_mem.mpr (Finset.mem_univ i)

/-- The explicit assembly remembers both its ordered core and every item of
the dependent attachment datum. -/
theorem LabelledCoreForestAttachment.assembleGraph_injective
    {q n : ℕ} {H H' : SimpleGraph (Fin q)}
    {D E : LabelledCoreForestAttachment q n}
    (hgraph : D.assembleGraph H = E.assembleGraph H') :
    H = H' ∧ D = E := by
  have hcore : H = H' := by
    rw [← D.comap_inl_assembleGraph H,
      ← E.comap_inl_assembleGraph H', hgraph]
  subst H'
  refine ⟨rfl, ?_⟩
  rcases D with ⟨P, f⟩
  rcases E with ⟨Q, g⟩
  have hP : P = Q :=
    LabelledCoreForestAttachment.partition_eq_of_assembleGraph_eq
      (H := H) (H' := H) ⟨P, f⟩ ⟨Q, g⟩ hgraph
  subst Q
  congr 1
  funext B
  let D : LabelledCoreForestAttachment q n := ⟨P, f⟩
  let E : LabelledCoreForestAttachment q n := ⟨P, g⟩
  have hpair :
      ((f B).1, (f B).2.root.1) =
        ((g B).1, (g B).2.root.1) := by
    have hDedge :
        (D.assembleGraph H).Adj
          (Sum.inl (f B).1) (Sum.inr (f B).2.root.1) :=
      ⟨B, rfl, rfl⟩
    have hEedge :
        (E.assembleGraph H).Adj
          (Sum.inl (f B).1) (Sum.inr (f B).2.root.1) := by
      rw [← hgraph]
      exact hDedge
    exact (E.existsUnique_core_edge_in_block H B).unique
      ⟨(f B).2.root.2, hEedge⟩
      ⟨(g B).2.root.2, ⟨B, rfl, rfl⟩⟩
  apply Prod.ext
  · exact congrArg (fun z : Fin q × Fin n => z.1) hpair
  · apply LabelledRootBranch.ext
    · rw [← D.induce_off_assembleGraph_block H B,
        ← E.induce_off_assembleGraph_block H B, hgraph]
    · apply Subtype.ext
      exact congrArg (fun z : Fin q × Fin n => z.2) hpair

/-- The assembled graph is connected whenever the supplied core is
connected and nonempty. -/
theorem LabelledCoreForestAttachment.assembleGraph_connected
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n)
    (hH : H.Connected) [Nonempty (Fin q)] :
    (D.assembleGraph H).Connected := by
  let c0 : Fin q := Classical.choice inferInstance
  rw [(D.assembleGraph H).connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl c0, ?_⟩
  intro v
  rcases v with c | i
  · exact (hH c0 c).map (D.coreHom H)
  · let B : D.1.parts :=
      ⟨D.1.part i, D.1.part_mem.mpr (Finset.mem_univ i)⟩
    have hiB : i ∈ B.1 := D.1.mem_part_self.mpr (Finset.mem_univ i)
    let x : B.1 := ⟨i, hiB⟩
    have hcore : (D.assembleGraph H).Reachable
        (Sum.inl c0) (Sum.inl (D.2 B).1) :=
      (hH c0 (D.2 B).1).map (D.coreHom H)
    have hroot : (D.assembleGraph H).Adj
        (Sum.inl (D.2 B).1) (Sum.inr (D.2 B).2.root.1) :=
      ⟨B, rfl, rfl⟩
    have hbranch : (D.assembleGraph H).Reachable
        (Sum.inr (D.2 B).2.root.1) (Sum.inr i) :=
      ((D.2 B).2.isTree.connected (D.2 B).2.root x).map
        (D.branchHom H B)
    exact hcore.trans ((SimpleGraph.Adj.reachable hroot).trans hbranch)

/-- A finite disjoint index for every edge of the assembled graph. -/
def LabelledCoreForestAttachment.edgeIndex
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :=
  H.edgeSet ⊕ Σ B : D.1.parts, Unit ⊕ (D.2 B).2.graph.edgeSet

instance LabelledCoreForestAttachment.edgeIndex_finite
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    Finite (D.edgeIndex H) := by
  unfold LabelledCoreForestAttachment.edgeIndex
  infer_instance

/-- Map the disjoint core/root/internal-edge index to the corresponding
edge of the assembled graph. -/
def LabelledCoreForestAttachment.edgeIndexToEdge
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    D.edgeIndex H → (D.assembleGraph H).edgeSet
  | Sum.inl e => (D.coreHom H).mapEdgeSet e
  | Sum.inr ⟨B, Sum.inl _⟩ =>
      ⟨s(Sum.inl (D.2 B).1, Sum.inr (D.2 B).2.root.1),
        ⟨B, rfl, rfl⟩⟩
  | Sum.inr ⟨B, Sum.inr e⟩ => (D.branchHom H B).mapEdgeSet e

/-- Every assembled edge is visibly either a core edge, the unique root
edge of a block, or an internal edge of one branch tree. -/
theorem LabelledCoreForestAttachment.edgeIndexToEdge_surjective
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    Function.Surjective (D.edgeIndexToEdge H) := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rcases u with i | i <;> rcases v with j | j
      · refine ⟨Sum.inl ⟨s(i, j), he⟩, ?_⟩
        rfl
      · obtain ⟨B, hc, hr⟩ := he
        subst i
        subst j
        refine ⟨Sum.inr ⟨B, Sum.inl Unit.unit⟩, ?_⟩
        rfl
      · obtain ⟨B, hc, hr⟩ := he
        subst j
        subst i
        refine ⟨Sum.inr ⟨B, Sum.inl Unit.unit⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap
      · obtain ⟨B, x, y, hxy, hx, hy⟩ := he
        subst i
        subst j
        refine ⟨Sum.inr ⟨B, Sum.inr ⟨s(x, y), hxy⟩⟩, ?_⟩
        rfl

private theorem sym2_core_core_ne_core_off
    {A B : Type*} (a b c : A) (x : B) :
    s(Sum.inl a, Sum.inl b) ≠ s(Sum.inl c, Sum.inr x) := by
  intro h
  rw [Sym2.eq_iff] at h
  simp at h

private theorem sym2_core_core_ne_off_off
    {A B : Type*} (a b : A) (x y : B) :
    s(Sum.inl a, Sum.inl b) ≠ s(Sum.inr x, Sum.inr y) := by
  intro h
  rw [Sym2.eq_iff] at h
  simp at h

private theorem sym2_core_off_ne_off_off
    {A B : Type*} (a : A) (x y z : B) :
    s(Sum.inl a, Sum.inr x) ≠ s(Sum.inr y, Sum.inr z) := by
  intro h
  rw [Sym2.eq_iff] at h
  simp at h

private theorem sym2_core_off_eq_iff
    {A B : Type*} (a c : A) (x y : B) :
    s(Sum.inl a, Sum.inr x) = s(Sum.inl c, Sum.inr y) ↔
      a = c ∧ x = y := by
  rw [Sym2.eq_iff]
  simp

/-- The visible edge trichotomy is disjoint, and distinct branch blocks
cannot produce the same off-core edge. -/
theorem LabelledCoreForestAttachment.edgeIndexToEdge_injective
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    Function.Injective (D.edgeIndexToEdge H) := by
  intro a b hab
  rcases a with ea | a
  · rcases b with eb | b
    · apply congrArg Sum.inl
      exact SimpleGraph.Hom.mapEdgeSet.injective
        (f := D.coreHom H) Sum.inl_injective hab
    · rcases b with ⟨B, ub | eb⟩
      · exfalso
        have h := congrArg Subtype.val hab
        rcases ea with ⟨e, he⟩
        induction e using Sym2.inductionOn with
        | _ i j =>
            exact sym2_core_core_ne_core_off i j (D.2 B).1
              (D.2 B).2.root.1 h
      · exfalso
        have h := congrArg Subtype.val hab
        rcases ea with ⟨e, he⟩
        rcases eb with ⟨e', he'⟩
        induction e using Sym2.inductionOn with
        | _ i j =>
          induction e' using Sym2.inductionOn with
          | _ x y =>
              exact sym2_core_core_ne_off_off i j x.1 y.1 h
  · rcases a with ⟨A, ua | ea⟩
    · rcases b with eb | b
      · exfalso
        have h := congrArg Subtype.val hab
        rcases eb with ⟨e, he⟩
        induction e using Sym2.inductionOn with
        | _ i j =>
            exact sym2_core_core_ne_core_off i j (D.2 A).1
              (D.2 A).2.root.1 h.symm
      · rcases b with ⟨B, ub | eb⟩
        · have h := congrArg Subtype.val hab
          have hp := (sym2_core_off_eq_iff
            (D.2 A).1 (D.2 B).1
            (D.2 A).2.root.1 (D.2 B).2.root.1).mp h
          have hAB : A = B := by
            apply Subtype.ext
            calc
              A.1 = D.1.part (D.2 A).2.root.1 :=
                (D.1.part_eq_of_mem A.2 (D.2 A).2.root.2).symm
              _ = D.1.part (D.2 B).2.root.1 := congrArg D.1.part hp.2
              _ = B.1 := D.1.part_eq_of_mem B.2 (D.2 B).2.root.2
          subst B
          rfl
        · exfalso
          have h := congrArg Subtype.val hab
          rcases eb with ⟨e, he⟩
          induction e using Sym2.inductionOn with
          | _ x y =>
              exact sym2_core_off_ne_off_off (D.2 A).1
                (D.2 A).2.root.1 x.1 y.1 h
    · rcases b with eb | b
      · exfalso
        have h := congrArg Subtype.val hab
        rcases ea with ⟨e, he⟩
        rcases eb with ⟨e', he'⟩
        induction e using Sym2.inductionOn with
        | _ x y =>
          induction e' using Sym2.inductionOn with
          | _ i j =>
              exact sym2_core_core_ne_off_off i j x.1 y.1 h.symm
      · rcases b with ⟨B, ub | eb⟩
        · exfalso
          have h := congrArg Subtype.val hab
          rcases ea with ⟨e, he⟩
          induction e using Sym2.inductionOn with
          | _ x y =>
              exact sym2_core_off_ne_off_off (D.2 B).1
                (D.2 B).2.root.1 x.1 y.1 h.symm
        · have h := congrArg Subtype.val hab
          rcases ea with ⟨e, he⟩
          rcases eb with ⟨e', he'⟩
          induction e using Sym2.inductionOn with
          | _ x y =>
            induction e' using Sym2.inductionOn with
            | _ z w =>
              have hend := (Sym2.eq_iff.mp h)
              have hAB : A = B := by
                apply Subtype.ext
                rcases hend with hsame | hswap
                · calc
                    A.1 = D.1.part x.1 :=
                      (D.1.part_eq_of_mem A.2 x.2).symm
                    _ = D.1.part z.1 := congrArg D.1.part
                      (Sum.inr_injective hsame.1)
                    _ = B.1 := D.1.part_eq_of_mem B.2 z.2
                · calc
                    A.1 = D.1.part x.1 :=
                      (D.1.part_eq_of_mem A.2 x.2).symm
                    _ = D.1.part w.1 := congrArg D.1.part
                      (Sum.inr_injective hswap.1)
                    _ = B.1 := D.1.part_eq_of_mem B.2 w.2
              subst B
              have hedge := SimpleGraph.Hom.mapEdgeSet.injective
                (f := D.branchHom H A)
                (Sum.inr_injective.comp Subtype.val_injective) hab
              exact congrArg
                (fun e : (D.2 A).2.graph.edgeSet =>
                  (Sum.inr ⟨A, Sum.inr e⟩ : D.edgeIndex H)) hedge

/-- The disjoint edge index has `|E(H)| + n` elements. -/
theorem LabelledCoreForestAttachment.card_edgeIndex
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    Nat.card (D.edgeIndex H) = H.edgeFinset.card + n := by
  classical
  have hblock (B : D.1.parts) :
      Nat.card (Unit ⊕ (D.2 B).2.graph.edgeSet) = B.1.card := by
    rw [Nat.card_sum, Nat.card_unique]
    have htree := (D.2 B).2.isTree.card_edgeFinset
    rw [SimpleGraph.edgeFinset_card] at htree
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, add_comm] using htree
  change Nat.card
      (H.edgeSet ⊕ Σ B : D.1.parts,
        Unit ⊕ (D.2 B).2.graph.edgeSet) = H.edgeFinset.card + n
  rw [Nat.card_sum, Nat.card_sigma]
  rw [SimpleGraph.edgeFinset_card]
  simp_rw [hblock]
  simpa only [Nat.card_eq_fintype_card, Finset.sum_coe_sort, Finset.card_univ,
    Fintype.card_fin] using
      congrArg (Fintype.card H.edgeSet + ·) D.1.sum_card_parts

/-- Exact edge count of a core with attached rooted trees. -/
theorem LabelledCoreForestAttachment.assembleGraph_edge_count
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    (D.assembleGraph H).edgeFinset.card = H.edgeFinset.card + n := by
  rw [SimpleGraph.edgeFinset_card, ← D.card_edgeIndex H]
  simpa only [Nat.card_eq_fintype_card] using (Nat.card_congr
    (Equiv.ofBijective (D.edgeIndexToEdge H)
      ⟨D.edgeIndexToEdge_injective H,
        D.edgeIndexToEdge_surjective H⟩)).symm

/-- Attaching rooted trees changes vertices and edges by the same number,
so the exact paper surplus is preserved. -/
theorem LabelledCoreForestAttachment.assembleGraph_surplus
    {q n ell : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n)
    (hs : H.edgeFinset.card + 1 = q + ell) :
    (D.assembleGraph H).edgeFinset.card + 1 =
      Fintype.card (Fin q ⊕ Fin n) + ell := by
  rw [D.assembleGraph_edge_count H]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end PerronWright
