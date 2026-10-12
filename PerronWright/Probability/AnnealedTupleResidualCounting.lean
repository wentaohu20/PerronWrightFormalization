import PerronWright.Probability.ExactFactorialExpectation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin

/-!
# Ordered disjoint blocks and their exact labelling multiplicity

These are finite combinatorial identities for the genuine component tuples
of `ComponentCounts`, not interfaces postulating a relabelling reduction.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualCounting

open AnnealedGraph ComponentBlocks ComponentCounts ExactFactorialExpectation

/-- The selected labelled vertices, with one finite fibre for each ordered component. -/
abbrev SelectedVertices {q : ℕ} (k : Fin q → ℕ) := Σ i : Fin q, Fin (k i)

/-- An injection places all selected labelled vertices in the ambient graph. -/
abbrev Placements (n : ℕ) {q : ℕ} (k : Fin q → ℕ) := SelectedVertices k ↪ Fin n

/-- Ordered candidate blocks of the required sizes, pairwise disjoint. -/
abbrev DisjointBlockFamilies (n : ℕ) {q : ℕ} (k : Fin q → ℕ) :=
  {B : Fin q → Finset (Fin n) //
    (∀ i, (B i).card = k i) ∧ Pairwise (fun i j ↦ Disjoint (B i) (B j))}

/-- Every block carries a bijective internal labelling. -/
abbrev LabelledBlockFamilies (n : ℕ) {q : ℕ} (k : Fin q → ℕ) :=
  Σ B : DisjointBlockFamilies n k, ∀ i, Fin (k i) ≃ ↥(B.val i)

def blockOfPlacement {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k)
    (i : Fin q) : Finset (Fin n) :=
  Finset.univ.image (fun a : Fin (k i) ↦ f ⟨i,a⟩)

@[simp] theorem mem_blockOfPlacement {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (i : Fin q) (v : Fin n) :
    v ∈ blockOfPlacement f i ↔ ∃ a : Fin (k i), f ⟨i,a⟩ = v := by
  simp [blockOfPlacement]

theorem blockOfPlacement_card {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (i : Fin q) : (blockOfPlacement f i).card = k i := by
  unfold blockOfPlacement
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (f.injective h)).2

theorem blockOfPlacement_pairwise {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) : Pairwise (fun i j ↦ Disjoint (blockOfPlacement f i) (blockOfPlacement f j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hi hj
  obtain ⟨a,ha⟩ := (mem_blockOfPlacement f i v).mp hi
  obtain ⟨b,hb⟩ := (mem_blockOfPlacement f j v).mp hj
  exact hij (congrArg Sigma.fst (f.injective (ha.trans hb.symm)))

def familyOfPlacement {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k) :
    DisjointBlockFamilies n k :=
  ⟨blockOfPlacement f, blockOfPlacement_card f, blockOfPlacement_pairwise f⟩

def labelsOfPlacement {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k)
    (i : Fin q) : Fin (k i) ≃ ↥(blockOfPlacement f i) :=
  Equiv.ofBijective
    (fun a ↦ ⟨f ⟨i,a⟩, (mem_blockOfPlacement f i _).mpr ⟨a,rfl⟩⟩)
    ⟨by
      intro a b h
      exact eq_of_heq (Sigma.mk.inj_iff.mp (f.injective (congrArg Subtype.val h))).2,
      by
      intro v
      obtain ⟨a,ha⟩ := (mem_blockOfPlacement f i v.val).mp v.property
      exact ⟨a,Subtype.ext ha⟩⟩

def placementOfLabels {n q : ℕ} {k : Fin q → ℕ}
    (p : LabelledBlockFamilies n k) : Placements n k where
  toFun a := (p.2 a.1 a.2).val
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    by_cases hij : i = j
    · subst j
      have ha : a = b := (p.2 i).injective (Subtype.ext h)
      subst b
      rfl
    · change (p.2 i a).val = (p.2 j b).val at h
      exact False.elim ((Finset.disjoint_left.mp (p.1.property.2 hij))
        (p.2 i a).property (h.symm ▸ (p.2 j b).property))

theorem blockOfPlacement_placementOfLabels {n q : ℕ} {k : Fin q → ℕ}
    (p : LabelledBlockFamilies n k) (i : Fin q) :
    blockOfPlacement (placementOfLabels p) i = p.1.val i := by
  ext v
  rw [mem_blockOfPlacement]
  constructor
  · rintro ⟨a,ha⟩
    exact ha ▸ (p.2 i a).property
  · intro hv
    refine ⟨(p.2 i).symm ⟨v,hv⟩, ?_⟩
    change ((p.2 i) ((p.2 i).symm ⟨v,hv⟩)).val = v
    simp

theorem placementOfLabels_injective {n q : ℕ} {k : Fin q → ℕ} :
    Function.Injective (placementOfLabels (n := n) (k := k)) := by
  rintro ⟨B,L⟩ ⟨C,N⟩ h
  have hBC : B = C := by
    apply Subtype.ext
    funext i
    rw [← blockOfPlacement_placementOfLabels ⟨B,L⟩ i,
      ← blockOfPlacement_placementOfLabels ⟨C,N⟩ i,h]
  cases hBC
  have hLN : L = N := by
    funext i
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun f : Placements n k ↦ f ⟨i,a⟩) h
  cases hLN
  rfl

theorem placementOfLabels_surjective {n q : ℕ} {k : Fin q → ℕ} :
    Function.Surjective (placementOfLabels (n := n) (k := k)) := by
  intro f
  refine ⟨⟨familyOfPlacement f,labelsOfPlacement f⟩, ?_⟩
  apply Function.Embedding.ext
  rintro ⟨i,a⟩
  rfl

/-- A completely proved finite correspondence between placements and
ordered disjoint blocks with internal vertex labels. -/
def placementsEquivLabelledBlocks {n q : ℕ} (k : Fin q → ℕ) :
    Placements n k ≃ LabelledBlockFamilies n k :=
  (Equiv.ofBijective placementOfLabels
    ⟨placementOfLabels_injective,placementOfLabels_surjective⟩).symm

/-- Every fixed candidate block family has exactly the product of its
component-size factorials many internal labellings. -/
theorem card_internal_labels {n q : ℕ} (k : Fin q → ℕ)
    (B : DisjointBlockFamilies n k) :
    Fintype.card (∀ i, Fin (k i) ≃ ↥(B.val i)) = ∏ i, (k i).factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_equiv ((Finset.equivFinOfCardEq (B.property.1 i)).symm)]
  simp

/-- Count all placements by their ordered disjoint blocks and labels. -/
theorem card_disjointBlockFamilies_mul_factorials {n q : ℕ} (k : Fin q → ℕ) :
    Fintype.card (DisjointBlockFamilies n k) * (∏ i, (k i).factorial) =
      n.descFactorial (∑ i, k i) := by
  have h := Fintype.card_congr (placementsEquivLabelledBlocks (n := n) k)
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_sigma] at h
  simp only [Fintype.card_fin] at h
  rw [Fintype.card_sigma] at h
  simp_rw [card_internal_labels] at h
  simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using h.symm

theorem factorialProduct_pos {q : ℕ} (k : Fin q → ℕ) :
    0 < ∏ i, ((k i).factorial : ℝ) := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast Nat.factorial_pos (k i)

/-- The exact ordered block-selection coefficient `(n)_K / ∏ k_i!`. -/
theorem card_disjointBlockFamilies_real_eq {n q : ℕ} (k : Fin q → ℕ) :
    (Fintype.card (DisjointBlockFamilies n k) : ℝ) =
      (n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ) := by
  apply (eq_div_iff (factorialProduct_pos k).ne').mpr
  exact_mod_cast card_disjointBlockFamilies_mul_factorials (n := n) k

theorem familyOfPlacement_placementOfLabels {n q : ℕ} {k : Fin q → ℕ}
    (p : LabelledBlockFamilies n k) : familyOfPlacement (placementOfLabels p) = p.1 := by
  apply Subtype.ext
  funext i
  exact blockOfPlacement_placementOfLabels p i

/-- Weighted form of the exact label multiplicity, valid for every observable
of the ordered candidate blocks. -/
theorem sum_placements_eq_factorial_mul_sum_blocks {n q : ℕ} (k : Fin q → ℕ)
    (W : DisjointBlockFamilies n k → ℝ) :
    (∑ f : Placements n k, W (familyOfPlacement f)) =
      (∏ i, ((k i).factorial : ℝ)) * ∑ B : DisjointBlockFamilies n k, W B := by
  let e : LabelledBlockFamilies n k ≃ Placements n k :=
    Equiv.ofBijective placementOfLabels
      ⟨placementOfLabels_injective,placementOfLabels_surjective⟩
  calc
    _ = ∑ p : LabelledBlockFamilies n k, W (familyOfPlacement (placementOfLabels p)) :=
      (e.sum_comp (fun f ↦ W (familyOfPlacement f))).symm
    _ = ∑ p : LabelledBlockFamilies n k, W p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [familyOfPlacement_placementOfLabels]
    _ = ∑ B : DisjointBlockFamilies n k, ∑ _L : (∀ i, Fin (k i) ≃ ↥(B.val i)), W B :=
      Fintype.sum_sigma _
    _ = _ := by
      simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_internal_labels,
        Nat.cast_prod]
      rw [Finset.mul_sum]

theorem matchesBlock_card_pos {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (k r : ℕ) (hB : MatchesBlock G B k r) : 0 < B.card := by
  obtain ⟨⟨v,hv⟩⟩ := hB.1.nonempty
  exact Finset.card_pos.mpr ⟨v,hv⟩

def embeddingOfGoodFamily {n q : ℕ} {G : SimpleGraph (Fin n)} {k r : Fin q → ℕ}
    (B : DisjointBlockFamilies n k) (hB : ∀ i, MatchesBlock G (B.val i) (k i) (r i)) :
    Fin q ↪ Finset (Fin n) where
  toFun := B.val
  inj' := by
    intro i j heq
    by_contra hij
    have hd := B.property.2 hij
    change Disjoint (B.val i) (B.val j) at hd
    rw [heq] at hd
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (matchesBlock_card_pos G (B.val j) (k j) (r j) (hB j))
    exact (Finset.disjoint_left.mp hd) hv hv

/-- Genuine component tuples are also exactly the good disjoint block families.
Distinctness follows from connectivity, not from an extra positivity assumption. -/
def goodBlockFamiliesEquiv {n q : ℕ} (G : SimpleGraph (Fin n)) (k r : Fin q → ℕ) :
    GoodBlockTuples G k r ≃
      {B : DisjointBlockFamilies n k // ∀ i, MatchesBlock G (B.val i) (k i) (r i)} where
  toFun B := ⟨⟨B.val, (fun i ↦ (B.property i).2.2.1),
    matchesTuple_disjoint G B.val k r B.property⟩, B.property⟩
  invFun B := ⟨embeddingOfGoodFamily B.val B.property, B.property⟩
  left_inv B := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Reindex the actual component count by disjoint ordered candidate blocks. -/
theorem count_cast_eq_sum_disjointBlocks {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :
    (count G k r : ℝ) = ∑ B : DisjointBlockFamilies n k,
      if ∀ i, MatchesBlock G (B.val i) (k i) (r i) then (1 : ℝ) else 0 := by
  unfold count
  rw [Fintype.card_congr ((componentTupleBlockEquiv G k r).trans (goodBlockFamiliesEquiv G k r))]
  rw [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro B _
  split_ifs <;> simp

/-- Each genuine ordered component tuple has precisely `∏ k_i!` labellings.
The sum is over actual ambient vertex placements and actual component tests. -/
theorem count_mul_factorials_eq_sum_placements {n q : ℕ} (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) :
    (count G k r : ℝ) * (∏ i, ((k i).factorial : ℝ)) =
      ∑ f : Placements n k,
        if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i) then (1 : ℝ) else 0 := by
  have h := sum_placements_eq_factorial_mul_sum_blocks k
    (fun B ↦ if ∀ i, MatchesBlock G (B.val i) (k i) (r i) then (1 : ℝ) else 0)
  have h' :
      (∑ f : Placements n k,
        if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i) then (1 : ℝ) else 0) =
        (∏ i, ((k i).factorial : ℝ)) * (count G k r : ℝ) := by
    rw [count_cast_eq_sum_disjointBlocks]
    simpa only [familyOfPlacement] using h
  rw [h']
  ring

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exact finite-size factorial expectation after the proved internal-label
regrouping.  No exchangeability or graph-sum identity is postulated. -/
theorem expectation_mul_factorials_eq_sum_placement_probabilities
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n q : ℕ) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) *
        (∏ i, ((k i).factorial : ℝ)) =
      ∑ f : Placements n k,
        ∫ G, if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)
          then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n := by
  rw [← integral_mul_const]
  simp_rw [count_mul_factorials_eq_sum_placements]
  rw [integral_finsetSum]
  intro f _
  exact Integrable.of_finite

/-- The literal actual factorial expectation divided by its proved internal
labelling multiplicity; this holds also when the size constraints are impossible. -/
theorem expectation_eq_div_sum_placement_probabilities
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n q : ℕ) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) =
      (∑ f : Placements n k,
        ∫ G, if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)
          then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n) /
        (∏ i, ((k i).factorial : ℝ)) := by
  apply (eq_div_iff (factorialProduct_pos k).ne').mpr
  exact expectation_mul_factorials_eq_sum_placement_probabilities M t ht n q k r

end PerronWright.AnnealedTupleResidualCounting
