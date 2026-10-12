import PerronWright.Probability.SelectedConfiguration
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Literal ordered distinct component counts

The count is the cardinality of the finite set of injective component
tuples with prescribed sizes and surpluses.  A proved equivalence turns
these genuine component tuples into candidate vertex-block tuples.
Their expectation is consequently an exact finite sum of event probabilities.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ComponentCounts

open AnnealedGraph ComponentBlocks

/-- Internal surplus `edges + 1 - vertices` of a finite vertex block. -/
def blockSurplus {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : ℕ :=
  (G.induce (B : Set (Fin n))).edgeFinset.card + 1 - B.card

/-- Size of an actual connected component. -/
def componentSize {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : ℕ := (componentBlockEquiv G C).val.card

/-- Surplus of an actual connected component. -/
def componentSurplus {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : ℕ := blockSurplus G (componentBlockEquiv G C).val

/-- A candidate block is one isolated connected component of the required
size and surplus. -/
def MatchesBlock {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (k r : ℕ) : Prop :=
  (G.induce (B : Set (Fin n))).Connected ∧ Isolated G (B : Set (Fin n)) ∧
    B.card = k ∧ blockSurplus G B = r

/-- Ordered distinct genuine components with prescribed sizes and surpluses. -/
abbrev GoodComponentTuples {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :=
  {c : Fin q ↪ G.ConnectedComponent //
    ∀ i, componentSize (c i) = k i ∧ componentSurplus (c i) = r i}

/-- Ordered distinct candidate blocks that are genuine components. -/
abbrev GoodBlockTuples {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :=
  {B : Fin q ↪ Finset (Fin n) // ∀ i, MatchesBlock G (B i) (k i) (r i)}

instance goodComponentTuples_fintype {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) : Fintype (GoodComponentTuples G k r) := Fintype.ofFinite _

/-- The literal ordered factorial component count from the paper. -/
def count {n q : ℕ} (G : SimpleGraph (Fin n)) (k r : Fin q → ℕ) : ℕ :=
  Fintype.card (GoodComponentTuples G k r)

/-- Exact bijection; no connectivity or isolation assertion is assumed. -/
def componentTupleBlockEquiv {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) : GoodComponentTuples G k r ≃ GoodBlockTuples G k r where
  toFun c := ⟨⟨fun i ↦ (componentBlockEquiv G (c.val i)).val, by
      intro i j hij
      apply c.val.injective
      apply (componentBlockEquiv G).injective
      exact Subtype.ext hij⟩, by
    intro i
    have hb := (componentBlockEquiv G (c.val i)).property
    change (G.induce ((componentBlockEquiv G (c.val i)).val : Set (Fin n))).Connected ∧
        Isolated G ((componentBlockEquiv G (c.val i)).val : Set (Fin n)) ∧
        (componentBlockEquiv G (c.val i)).val.card = k i ∧
        blockSurplus G (componentBlockEquiv G (c.val i)).val = r i
    exact ⟨hb.1, hb.2, (c.property i).1, (c.property i).2⟩⟩
  invFun B := ⟨⟨fun i ↦ (componentBlockEquiv G).symm
      ⟨B.val i, (B.property i).1, (B.property i).2.1⟩, by
    intro i j hij
    apply B.val.injective
    have he := (componentBlockEquiv G).symm.injective hij
    exact congrArg Subtype.val he⟩, by
    intro i
    change componentSize ((componentBlockEquiv G).symm
        ⟨B.val i, (B.property i).1, (B.property i).2.1⟩) = k i ∧
      componentSurplus ((componentBlockEquiv G).symm
        ⟨B.val i, (B.property i).1, (B.property i).2.1⟩) = r i
    unfold componentSize componentSurplus
    rw [(componentBlockEquiv G).apply_symm_apply
      ⟨B.val i, (B.property i).1, (B.property i).2.1⟩]
    exact (B.property i).2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    change (componentBlockEquiv G).symm
      ⟨(componentBlockEquiv G (c.val i)).val, _⟩ = c.val i
    exact (componentBlockEquiv G).symm_apply_apply (c.val i)
  right_inv B := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    change (componentBlockEquiv G ((componentBlockEquiv G).symm
      ⟨B.val i, (B.property i).1, (B.property i).2.1⟩)).val = B.val i
    exact congrArg Subtype.val ((componentBlockEquiv G).apply_symm_apply
      ⟨B.val i, (B.property i).1, (B.property i).2.1⟩)

/-- Component counts are exactly the sum of candidate-block indicators. -/
theorem count_eq_sum_blocks {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :
    count G k r = ∑ B : Fin q ↪ Finset (Fin n),
      if ∀ i, MatchesBlock G (B i) (k i) (r i) then 1 else 0 := by
  unfold count
  rw [Fintype.card_congr (componentTupleBlockEquiv G k r)]
  change Fintype.card {B : Fin q ↪ Finset (Fin n) //
      ∀ i, MatchesBlock G (B i) (k i) (r i)} = _
  rw [Fintype.card_subtype]
  exact Finset.card_filter _ _

/-- The real-valued form, used by probability integrals. -/
theorem count_cast_eq_sum_blocks {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :
    (count G k r : ℝ) = ∑ B : Fin q ↪ Finset (Fin n),
      if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0 := by
  rw [count_eq_sum_blocks, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro B _
  split_ifs <;> simp

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exact factorial expectation as a sum over isolated block events. -/
theorem expectation_eq_sum_block_probabilities (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (n q : ℕ) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) =
      ∑ B : Fin q ↪ Finset (Fin n),
        ∫ G, if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0
          ∂AnnealedGraph.law M t ht n := by
  simp_rw [count_cast_eq_sum_blocks]
  rw [integral_finsetSum]
  intro B _
  exact Integrable.of_finite

end PerronWright.ComponentCounts
