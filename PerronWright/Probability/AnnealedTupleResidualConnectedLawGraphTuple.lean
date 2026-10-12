import PerronWright.Probability.AnnealedTupleResidualPatternFormula
import PerronWright.Probability.ConnectedTypeLaw
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Labelled component graphs and the actual selected edge patterns

The ordered graph tuple is embedded into the ambient vertex set by the
same placement used for the genuine component-count formula.  The induced
block isomorphisms and the correspondence with valid local edge patterns
are proved from adjacency, not assumed as a relabelling interface.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualConnectedLawGraphTuple

open AnnealedGraph ComponentBlocks ComponentCounts SelectedConfiguration
open ExactFactorialExpectation AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula

abbrev GraphTuple {q : ℕ} (k : Fin q → ℕ) := (i : Fin q) → SimpleGraph (Fin (k i))

/-- Embed exactly the internal edges of each labelled component, and no others. -/
def tupleGraph {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k)
    (H : GraphTuple k) : SimpleGraph (Fin n) where
  Adj u v := ∃ (i : Fin q) (a b : Fin (k i)), (H i).Adj a b ∧ f ⟨i,a⟩ = u ∧ f ⟨i,b⟩ = v
  symm := ⟨by
    rintro u v ⟨i,a,b,hab,ha,hb⟩
    exact ⟨i,b,a,hab.symm,hb,ha⟩⟩
  loopless := ⟨by
    rintro u ⟨i,a,b,hab,ha,hb⟩
    have he : a = b := eq_of_heq (Sigma.mk.inj_iff.mp (f.injective (ha.trans hb.symm))).2
    exact (H i).loopless.irrefl a (he ▸ hab)⟩

@[simp] theorem tupleGraph_adj_same {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (i : Fin q) (a b : Fin (k i)) :
    (tupleGraph f H).Adj (f ⟨i,a⟩) (f ⟨i,b⟩) ↔ (H i).Adj a b := by
  constructor
  · rintro ⟨j,c,d,hcd,hc,hd⟩
    have hji : j = i := congrArg Sigma.fst (f.injective hc)
    subst j
    have hca : c = a := eq_of_heq (Sigma.mk.inj_iff.mp (f.injective hc)).2
    have hdb : d = b := eq_of_heq (Sigma.mk.inj_iff.mp (f.injective hd)).2
    simpa only [hca,hdb] using hcd
  · intro hab
    exact ⟨i,a,b,hab,rfl,rfl⟩

theorem tupleGraph_isolated {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (i : Fin q) :
    Isolated (tupleGraph f H) (blockOfPlacement f i : Set (Fin n)) := by
  intro u hu v huv
  obtain ⟨a,ha⟩ := (mem_blockOfPlacement f i u).mp hu
  obtain ⟨j,c,d,_,hc,hd⟩ := huv
  have hji : j = i := congrArg Sigma.fst (f.injective (hc.trans ha.symm))
  subst j
  exact (mem_blockOfPlacement f i v).mpr ⟨d,hd⟩

/-- Each block induction is genuinely isomorphic to its own labelled graph. -/
def tupleGraph_blockIso {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (i : Fin q) :
    H i ≃g (tupleGraph f H).induce (blockOfPlacement f i : Set (Fin n)) where
  toEquiv := labelsOfPlacement f i
  map_rel_iff' := by
    intro a b
    exact tupleGraph_adj_same f H i a b

/-- In a connected labelled graph, natural surplus has no truncation loss. -/
theorem connected_surplus_iff {k r : ℕ} (H : SimpleGraph (Fin k))
    (hc : H.Connected) : H.edgeFinset.card + 1 - k = r ↔ H.edgeFinset.card = k+r-1 := by
  have hbound := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← H.edgeFinset_card,
    Fintype.card_fin] at hbound
  have hk : 0 < k := by
    obtain ⟨v⟩ := hc.nonempty
    exact Nat.zero_lt_of_lt v.isLt
  omega

theorem tupleGraph_matchesBlock_iff {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (i : Fin q) (r : ℕ) :
    MatchesBlock (tupleGraph f H) (blockOfPlacement f i) (k i) r ↔
      ConnectedTypeLaw.Eligible r (H i) := by
  have hiso := tupleGraph_isolated f H i
  have hconn := (tupleGraph_blockIso f H i).connected_iff
  have he := (tupleGraph_blockIso f H i).card_edgeFinset_eq
  unfold MatchesBlock blockSurplus ConnectedTypeLaw.Eligible
  rw [← hconn,← he,blockOfPlacement_card]
  constructor
  · rintro ⟨hc,_,_,hr⟩
    exact ⟨hc,(connected_surplus_iff _ hc).mp hr⟩
  · rintro ⟨hc,hr⟩
    exact ⟨hc,hiso,rfl,(connected_surplus_iff _ hc).mpr hr⟩

/-- Recover the labelled internal graph from any actual ambient graph. -/
def restrictTupleGraph {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (G : SimpleGraph (Fin n)) : GraphTuple k :=
  fun i ↦ G.comap (fun a : Fin (k i) ↦ f ⟨i,a⟩)

@[simp] theorem restrictTupleGraph_tupleGraph {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) : restrictTupleGraph f (tupleGraph f H) = H := by
  funext i
  apply SimpleGraph.ext
  funext a b
  exact propext (tupleGraph_adj_same f H i a b)

def restrictTupleGraph_blockIso {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (G : SimpleGraph (Fin n)) (i : Fin q) :
    restrictTupleGraph f G i ≃g G.induce (blockOfPlacement f i : Set (Fin n)) where
  toEquiv := labelsOfPlacement f i
  map_rel_iff' := by intro a b; rfl

theorem restrictTupleGraph_eligible {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (G : SimpleGraph (Fin n)) (r : Fin q → ℕ)
    (hG : ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)) :
    ∀ i, ConnectedTypeLaw.Eligible (r i) (restrictTupleGraph f G i) := by
  intro i
  have hc := (restrictTupleGraph_blockIso f G i).connected_iff.mpr (hG i).1
  refine ⟨hc,(connected_surplus_iff _ hc).mp ?_⟩
  have hs := (hG i).2.2.2
  unfold blockSurplus at hs
  rw [← (restrictTupleGraph_blockIso f G i).card_edgeFinset_eq,blockOfPlacement_card] at hs
  exact hs

theorem mem_selectedUnion_placement {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (u : Fin n) :
    u ∈ selectedUnion (blocksOfPlacement hk f) ↔ ∃ a : SelectedVertices k, f a = u := by
  simp only [selectedUnion,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨a,ha⟩ := (mem_blockOfPlacement f i u).mp hi
    exact ⟨⟨i,a⟩,ha⟩
  · rintro ⟨⟨i,a⟩,ha⟩
    exact ⟨i,(mem_blockOfPlacement f i u).mpr ⟨a,ha⟩⟩

theorem tupleGraph_adj_selected {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (H : GraphTuple k)
    {u v : Fin n} (huv : (tupleGraph f H).Adj u v) :
    u ∈ selectedUnion (blocksOfPlacement hk f) ∧ v ∈ selectedUnion (blocksOfPlacement hk f) := by
  obtain ⟨i,a,b,_,ha,hb⟩ := huv
  exact ⟨(mem_selectedUnion_placement hk f u).mpr ⟨⟨i,a⟩,ha⟩,
    (mem_selectedUnion_placement hk f v).mpr ⟨⟨i,b⟩,hb⟩⟩

/-- A padded prescribed pattern has no unselected/unselected edge. -/
theorem patternGraph_adj_touches {n q : ℕ} (B : Fin q ↪ Finset (Fin n))
    (c : prescribedEdges (selectedUnion B) → Bool) {u v : Fin n}
    (huv : (patternGraph B c).Adj u v) :
    u ∈ selectedUnion B ∨ v ∈ selectedUnion B := by
  let e : Edge n := ⟨s(u,v),by simpa only [Sym2.mk_isDiag_iff] using
    (patternGraph B c).ne_of_adj huv⟩
  have he : IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e = true :=
    (mem_toGraph_edgeSet _ e).mp (by exact huv)
  by_contra hn
  have hnot : e ∉ prescribedEdges (selectedUnion B) := by
    simpa only [mem_prescribedEdges,touches_mk,e] using hn
  simp only [IndependentEdges.extend,dif_neg hnot] at he
  contradiction

/-- Internal graph restriction followed by embedding recovers every supported
graph whose selected blocks are isolated. -/
theorem tupleGraph_restrict_eq {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (G : SimpleGraph (Fin n))
    (hSupp : ∀ u v, G.Adj u v → u ∈ selectedUnion (blocksOfPlacement hk f) ∨
      v ∈ selectedUnion (blocksOfPlacement hk f))
    (hIso : ∀ i, Isolated G (blockOfPlacement f i : Set (Fin n))) :
    tupleGraph f (restrictTupleGraph f G) = G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · rintro ⟨i,a,b,hab,ha,hb⟩
    exact ha ▸ hb ▸ hab
  · intro huv
    have hsame : ∃ i, u ∈ blockOfPlacement f i ∧ v ∈ blockOfPlacement f i := by
      rcases hSupp u v huv with hu | hv
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
        exact ⟨i,hi,hIso i u hi v huv⟩
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
        exact ⟨i,hIso i v hi u huv.symm,hi⟩
    obtain ⟨i,hi,hj⟩ := hsame
    obtain ⟨a,ha⟩ := (mem_blockOfPlacement f i u).mp hi
    obtain ⟨b,hb⟩ := (mem_blockOfPlacement f i v).mp hj
    exact ⟨i,a,b,by change G.Adj (f ⟨i,a⟩) (f ⟨i,b⟩); simpa only [ha,hb] using huv,ha,hb⟩

theorem patternGraph_injective {n q : ℕ} (B : Fin q ↪ Finset (Fin n)) :
    Function.Injective (patternGraph B) := by
  intro c d h
  have ha := congrArg (IndependentEdges.restrict (prescribedEdges (selectedUnion B)))
    (congrArg assignmentOfGraph h)
  simpa only [patternGraph,assignmentOfGraph_toGraph,IndependentEdges.restrict_extend] using ha

/-- Restriction and absent-edge padding recover any graph with no edge
between two unused vertices. -/
theorem patternGraph_restrict_eq {n q : ℕ} (B : Fin q ↪ Finset (Fin n))
    (G : SimpleGraph (Fin n))
    (hSupp : ∀ u v, G.Adj u v → u ∈ selectedUnion B ∨ v ∈ selectedUnion B) :
    patternGraph B (IndependentEdges.restrict (prescribedEdges (selectedUnion B))
      (assignmentOfGraph G)) = G := by
  unfold patternGraph
  rw [← toGraph_assignmentOfGraph G]
  congr 1
  funext e
  by_cases he : e ∈ prescribedEdges (selectedUnion B)
  · simp only [IndependentEdges.extend,he,dite_true,IndependentEdges.restrict]
    simp only [assignmentOfGraph_toGraph]
  · have hfalse : assignmentOfGraph G e = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hm : e.val ∈ G.edgeSet := by
        simpa only [assignmentOfGraph,decide_eq_true_eq] using ht
      rcases e with ⟨e,heDiag⟩
      induction e using Sym2.inductionOn with
      | _ u v =>
        have ht := hSupp u v hm
        exact he ((mem_prescribedEdges _ _).mpr ht)
    simp only [IndependentEdges.extend,he,dite_false,assignmentOfGraph_toGraph,hfalse]

abbrev ValidPatterns {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (f : Placements n k) (r : Fin q → ℕ) :=
  {c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool //
    ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
      (blockOfPlacement f i) (k i) (r i)}

abbrev EligibleGraphTuples {q : ℕ} (k r : Fin q → ℕ) :=
  {H : GraphTuple k // ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)}

/-- The actual valid selected edge patterns are exactly tuples of labelled
connected graphs with the required edge counts. -/
def validPatternsEquivGraphTuples {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (r : Fin q → ℕ) :
    ValidPatterns hk f r ≃ EligibleGraphTuples k r where
  toFun c := ⟨restrictTupleGraph f (patternGraph (blocksOfPlacement hk f) c.val),
    restrictTupleGraph_eligible f _ r c.property⟩
  invFun H := ⟨IndependentEdges.restrict (prescribedEdges (selectedUnion (blocksOfPlacement hk f)))
    (assignmentOfGraph (tupleGraph f H.val)),by
      rw [patternGraph_restrict_eq _ _ (fun _ _ h ↦ Or.inl (tupleGraph_adj_selected hk f H.val h).1)]
      intro i
      exact (tupleGraph_matchesBlock_iff f H.val i (r i)).mpr (H.property i)⟩
  left_inv c := by
    apply Subtype.ext
    apply patternGraph_injective (blocksOfPlacement hk f)
    rw [patternGraph_restrict_eq _ _ (fun _ _ h ↦ Or.inl (tupleGraph_adj_selected hk f _ h).1)]
    exact tupleGraph_restrict_eq hk f _
      (fun _ _ h ↦ patternGraph_adj_touches _ _ h) (fun i ↦ (c.property i).2.1)
  right_inv H := by
    apply Subtype.ext
    change restrictTupleGraph f (patternGraph (blocksOfPlacement hk f)
      (IndependentEdges.restrict (prescribedEdges (selectedUnion (blocksOfPlacement hk f)))
        (assignmentOfGraph (tupleGraph f H.val)))) = H.val
    rw [patternGraph_restrict_eq _ _ (fun _ _ h ↦ Or.inl (tupleGraph_adj_selected hk f H.val h).1)]
    exact restrictTupleGraph_tupleGraph f H.val

/-- Reindex any actual valid-pattern sum by the genuinely corresponding
labelled component graph tuples. -/
theorem sum_valid_patterns_eq_sum_eligible_graphTuples {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (r : Fin q → ℕ)
    (F : SimpleGraph (Fin n) → ℝ) :
    (∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool,
      if ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
        (blockOfPlacement f i) (k i) (r i) then F (patternGraph (blocksOfPlacement hk f) c) else 0) =
    ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
      then F (tupleGraph f H) else 0 := by
  have hs₁ := Finset.sum_congr_set
    (s := {c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool |
      ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
        (blockOfPlacement f i) (k i) (r i)})
    (fun c ↦ if ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
      (blockOfPlacement f i) (k i) (r i) then F (patternGraph (blocksOfPlacement hk f) c) else 0)
    (fun c ↦ F (patternGraph (blocksOfPlacement hk f) c.val))
    (fun _ h ↦ if_pos h) (fun _ h ↦ if_neg h)
  have hs₂ := Finset.sum_congr_set
    (s := {H : GraphTuple k | ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)})
    (fun H ↦ if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then F (tupleGraph f H) else 0)
    (fun H ↦ F (tupleGraph f H.val))
    (fun _ h ↦ if_pos h) (fun _ h ↦ if_neg h)
  rw [hs₁,hs₂]
  apply Fintype.sum_equiv (validPatternsEquivGraphTuples hk f r)
  intro c
  congr 1
  exact (tupleGraph_restrict_eq hk f _ (fun _ _ h ↦ patternGraph_adj_touches _ _ h)
    (fun i ↦ (c.property i).2.1)).symm

end PerronWright.AnnealedTupleResidualConnectedLawGraphTuple
