import PerronWright.Probability.FiniteIrreducibleTypedGraphLaw
import PerronWright.Probability.FiniteIrreducibleTypePreservingPermutations
import PerronWright.Probability.AnnealedTupleResidualExchangeability

/-!
# Exchangeability within actual deterministic type fibres

The conditional graph law is invariant under exactly those ambient
permutations that preserve the fixed assignment. The proof is the actual
finite independent-edge product, not an annealed type integral.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.FiniteIrreducibleFixedTypeExchangeability

open AnnealedGraph ComponentCounts AnnealedTupleResidualCounting
open AnnealedTupleResidualExchangeability
open FiniteIrreducibleTypedGraphLaw
open FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleTypePreservingPermutations

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem hazard_typePreserving_permutation (M : FiniteIrreducibleModel S)
    (t : ℝ) {n : ℕ} (x : Fin n → S) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v, x (σ v) = x v) (e : Edge n) :
    hazard M t x (edgePermutation σ e) = hazard M t x e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
    change t * M.kernel (x (σ i)) (x (σ j)) / (n : ℝ) =
      t * M.kernel (x i) (x j) / (n : ℝ)
    rw [hσ i, hσ j]

/-- Literal finite independent-edge masses are invariant whenever every
edge hazard is invariant under the actual permutation. -/
theorem independentMass_permutation {n : ℕ} (z : Edge n → ℝ)
    (σ : Equiv.Perm (Fin n))
    (hzσ : ∀ e, z (edgePermutation σ e) = z e) (a : Assignment n) :
    IndependentEdges.mass z (assignmentPermutation σ a) =
      IndependentEdges.mass z a := by
  unfold IndependentEdges.mass
  change (∏ e, IndependentEdges.edgeMass (z e) (a (edgePermutation σ e))) = _
  calc
    _ = ∏ e, IndependentEdges.edgeMass (z (edgePermutation σ e))
      (a (edgePermutation σ e)) := by
        apply Finset.prod_congr rfl
        intro e _
        rw [hzσ e]
    _ = _ := (edgePermutation σ).prod_comp
      (fun e ↦ IndependentEdges.edgeMass (z e) (a e))

/-- Invariance of every genuine graph observable under a type-preserving
permutation, with the actual fixed-type probability measure. -/
theorem law_expectation_typePreserving_permutation
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v, x (σ v) = x v) (F : SimpleGraph (Fin n) → ℝ) :
    (∫ G, F (G.comap σ) ∂law M t ht x) =
      ∫ G, F G ∂law M t ht x := by
  change (∫ G, F (G.comap σ) ∂FixedTypeGraph.law _ _) =
    ∫ G, F G ∂FixedTypeGraph.law _ _
  rw [FixedTypeGraph.expectation_eq_sum, FixedTypeGraph.expectation_eq_sum]
  calc
    _ = ∑ a : Assignment n,
        IndependentEdges.mass (hazard M t x) (assignmentPermutation σ a) *
          F (toGraph (assignmentPermutation σ a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [independentMass_permutation _ σ
        (hazard_typePreserving_permutation M t x σ hσ),
        toGraph_assignmentPermutation]
    _ = _ := (assignmentPermutation σ).sum_comp
      (fun a ↦ IndependentEdges.mass (hazard M t x) a * F (toGraph a))

/-- Actual probability of an ordered placed genuine-component event. -/
def placementProbability (M : FiniteIrreducibleModel S)
    (t : ℝ) (ht : 0 ≤ t) {n q : ℕ} (x : Fin n → S)
    (k r : Fin q → ℕ) (f : Placements n k) : ℝ :=
  ∫ G, if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)
    then (1 : ℝ) else 0 ∂law M t ht x

/-- Only the actual selected type vector matters: the ambient counts and
assignment remain fixed, and connectivity/size/surplus are genuine tests. -/
theorem placementProbability_eq_of_selectedTypes
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (f g : Placements n k) (hfg : ∀ v, x (f v) = x (g v)) :
    placementProbability M t ht x k r f =
      placementProbability M t ht x k r g := by
  let y : SelectedVertices k → S := fun v ↦ x (f v)
  let F : TypePreservingEmbeddings y x := ⟨f, fun _ ↦ rfl⟩
  let G : TypePreservingEmbeddings y x := ⟨g, fun v ↦ (hfg v).symm⟩
  obtain ⟨σ, hσ, hσfg⟩ := exists_typePreserving_permutation y x F G
  have he (H : SimpleGraph (Fin n)) :
      (∀ i, MatchesBlock (H.comap σ) (blockOfPlacement f i) (k i) (r i)) ↔
        (∀ i, MatchesBlock H (blockOfPlacement g i) (k i) (r i)) := by
    apply forall_congr'
    intro i
    rw [matchesBlock_comap_permutation,
      blockOfPlacement_permutation σ f g hσfg]
  unfold placementProbability
  calc
    _ = ∫ H, if ∀ i, MatchesBlock (H.comap σ) (blockOfPlacement f i) (k i) (r i)
        then (1 : ℝ) else 0 ∂law M t ht x :=
      (law_expectation_typePreserving_permutation M t ht x σ hσ
        (fun H ↦ if ∀ i, MatchesBlock H (blockOfPlacement f i) (k i) (r i)
          then (1 : ℝ) else 0)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with H
      exact if_congr (he H) rfl rfl

end PerronWright.FiniteIrreducibleFixedTypeExchangeability

