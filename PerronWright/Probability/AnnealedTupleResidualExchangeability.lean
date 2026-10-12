import PerronWright.Probability.AnnealedTupleResidualCounting
import Mathlib.Logic.Equiv.Fintype

/-!
# Literal annealed exchangeability and the vertex-selection coefficient

The permutation invariance of the graph law is proved from its conditional
independent-edge product and its sampled-type product law.  It is then used
with the proved placement/block correspondence, rather than assumed as a
relabelling interface.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualExchangeability

open AnnealedGraph ComponentBlocks ComponentCounts AnnealedTupleResidualCounting

/-- Permute each unordered non-diagonal edge coordinate. -/
def edgePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Edge n ≃ Edge n where
  toFun e := ⟨e.val.map σ, fun h ↦ e.property ((Sym2.isDiag_map σ.injective).mp h)⟩
  invFun e := ⟨e.val.map σ.symm, fun h ↦ e.property ((Sym2.isDiag_map σ.symm.injective).mp h)⟩
  left_inv := by
    rintro ⟨e,hdiag⟩
    apply Subtype.ext
    induction e using Sym2.inductionOn with
    | _ i j => simp
  right_inv := by
    rintro ⟨e,hdiag⟩
    apply Subtype.ext
    induction e using Sym2.inductionOn with
    | _ i j => simp

/-- Relabel a literal Boolean graph sample. -/
def assignmentPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Assignment n ≃ Assignment n where
  toFun a e := a (edgePermutation σ e)
  invFun a e := a ((edgePermutation σ).symm e)
  left_inv a := by funext e; simp
  right_inv a := by funext e; simp

theorem toGraph_assignmentPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Assignment n) :
    toGraph (assignmentPermutation σ a) = (toGraph a).comap σ := by
  apply SimpleGraph.ext
  funext i j
  apply propext
  by_cases hij : i = j
  · simp [hij]
  · let e : Edge n := ⟨s(i,j), by simpa only [Sym2.mk_isDiag_iff] using hij⟩
    have hm := mem_toGraph_edgeSet (assignmentPermutation σ a) e
    have hn := mem_toGraph_edgeSet a (edgePermutation σ e)
    simpa only [e, SimpleGraph.mem_edgeSet, assignmentPermutation,
      Equiv.coe_fn_mk, edgePermutation, Sym2.map_mk, SimpleGraph.comap_adj]
      using hm.trans hn.symm

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem hazard_permutation {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → S) (e : Edge n) :
    hazard M t (fun i ↦ x (σ i)) e = hazard M t x (edgePermutation σ e) := by
  rcases e with ⟨e,hdiag⟩
  induction e using Sym2.inductionOn with
  | _ i j => rfl

theorem conditionalMass_permutation {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → S) (a : Assignment n) :
    conditionalMass M t (fun i ↦ x (σ i)) (assignmentPermutation σ a) =
      conditionalMass M t x a := by
  unfold conditionalMass IndependentEdges.mass
  simp_rw [hazard_permutation]
  exact (edgePermutation σ).prod_comp
    (fun e ↦ IndependentEdges.edgeMass (hazard M t x e) (a e))

/-- The actual i.i.d. sampled-type law is invariant under relabelling. -/
theorem integral_type_permutation {n : ℕ} (M : CompactBJRModel S)
    (σ : Equiv.Perm (Fin n)) (F : (Fin n → S) → ℝ) :
    (∫ x : Fin n → S, F (fun i ↦ x (σ i)) ∂typeLaw M n) =
      ∫ x : Fin n → S, F x ∂typeLaw M n := by
  have hmp := (measurePreserving_piCongrLeft (fun _ : Fin n ↦ M.mu) σ).symm
  exact hmp.integral_comp' F

theorem mass_assignmentPermutation {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (σ : Equiv.Perm (Fin n)) (a : Assignment n) :
    AnnealedGraph.mass M t (assignmentPermutation σ a) = AnnealedGraph.mass M t a := by
  unfold AnnealedGraph.mass
  rw [← integral_type_permutation M σ
    (fun x ↦ conditionalMass M t x (assignmentPermutation σ a))]
  simp_rw [conditionalMass_permutation]

theorem lawIntegral_eq_assignmentIntegral {n : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (F : SimpleGraph (Fin n) → ℝ) :
    (∫ G, F G ∂AnnealedGraph.law M t ht n) =
      ∫ a : Assignment n, F (toGraph a) ∂(AnnealedGraph.pmf M t ht n).toMeasure := by
  rw [AnnealedGraph.law_expectation_eq_type_integral]
  exact (AnnealedGraph.expectation_eq_type_integral M t ht n F).symm

/-- Exchangeability of every graph observable under the actual annealed law. -/
theorem law_expectation_permutation {n : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (σ : Equiv.Perm (Fin n)) (F : SimpleGraph (Fin n) → ℝ) :
    (∫ G, F (G.comap σ) ∂AnnealedGraph.law M t ht n) =
      ∫ G, F G ∂AnnealedGraph.law M t ht n := by
  rw [lawIntegral_eq_assignmentIntegral, lawIntegral_eq_assignmentIntegral,
    PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [AnnealedGraph.pmf_apply_toReal, smul_eq_mul]
  calc
    _ = ∑ a : Assignment n,
        AnnealedGraph.mass M t (assignmentPermutation σ a) *
          F (toGraph (assignmentPermutation σ a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mass_assignmentPermutation, toGraph_assignmentPermutation]
    _ = _ := (assignmentPermutation σ).sum_comp
      (fun a ↦ AnnealedGraph.mass M t a * F (toGraph a))

/-- The permutation restricts to a bijection from a block onto its image. -/
def blockPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) (B : Finset (Fin n)) :
    ↥(B : Set (Fin n)) ≃ ↥(B.image σ : Set (Fin n)) :=
  Equiv.ofBijective
    (fun i ↦ ⟨σ i.val, Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩)
    ⟨by
      intro i j h
      exact Subtype.ext (σ.injective (congrArg Subtype.val h)),
      by
      intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩⟩

def blockGraphIso {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) :
    ((G.comap σ).induce (B : Set (Fin n))) ≃g
      (G.induce (B.image σ : Set (Fin n))) where
  toEquiv := blockPermutation σ B
  map_rel_iff' := by intro i j; rfl

theorem isolated_comap_iff_image {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) :
    Isolated (G.comap σ) (B : Set (Fin n)) ↔ Isolated G (B.image σ : Set (Fin n)) := by
  constructor
  · intro h i hi j hij
    obtain ⟨a,ha,hai⟩ := Finset.mem_image.mp hi
    have hmem : σ.symm j ∈ B := h a ha (σ.symm j) (by
      change G.Adj (σ a) (σ (σ.symm j))
      simpa only [hai,Equiv.apply_symm_apply] using hij)
    exact Finset.mem_image.mpr ⟨σ.symm j,hmem,σ.apply_symm_apply j⟩
  · intro h i hi j hij
    have hmem : σ j ∈ B.image σ := h (σ i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) (σ j) hij
    obtain ⟨a,ha,haj⟩ := Finset.mem_image.mp hmem
    exact (σ.injective haj) ▸ ha

theorem blockSurplus_comap_permutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) :
    blockSurplus (G.comap σ) B = blockSurplus G (B.image σ) := by
  unfold blockSurplus
  rw [(blockGraphIso σ G B).card_edgeFinset_eq,
    Finset.card_image_of_injective B σ.injective]

/-- Component membership, size, and surplus are all preserved by the proved
induced-block graph isomorphism. -/
theorem matchesBlock_comap_permutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (k r : ℕ) :
    MatchesBlock (G.comap σ) B k r ↔ MatchesBlock G (B.image σ) k r := by
  unfold MatchesBlock
  rw [(blockGraphIso σ G B).connected_iff, isolated_comap_iff_image,
    blockSurplus_comap_permutation, Finset.card_image_of_injective B σ.injective]

theorem blockOfPlacement_permutation {n q : ℕ} {k : Fin q → ℕ}
    (σ : Equiv.Perm (Fin n)) (f g : Placements n k)
    (hfg : ∀ a, σ (f a) = g a) (i : Fin q) :
    (blockOfPlacement f i).image σ = blockOfPlacement g i := by
  ext v
  simp only [Finset.mem_image, mem_blockOfPlacement]
  constructor
  · rintro ⟨w,⟨a,ha⟩,hw⟩
    refine ⟨a, ?_⟩
    rw [← hfg,ha,hw]
  · rintro ⟨a,ha⟩
    exact ⟨f ⟨i,a⟩,⟨a,rfl⟩,(hfg ⟨i,a⟩).trans ha⟩

/-- Any two placements of the same selected labels are related by an
actual permutation of all ambient vertices. -/
theorem exists_permutation_placements {n q : ℕ} {k : Fin q → ℕ}
    (f g : Placements n k) : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (f a) = g a := by
  let E := (Function.Embedding.toEquivRange f).symm.trans (Function.Embedding.toEquivRange g)
  refine ⟨E.extendSubtype, ?_⟩
  intro a
  rw [Equiv.extendSubtype_apply_of_mem E (f a) ⟨a,rfl⟩]
  change (E ⟨f a,⟨a,rfl⟩⟩).val = g a
  simp only [E,Equiv.trans_apply]
  have h : (Function.Embedding.toEquivRange f).symm ⟨f a,⟨a,rfl⟩⟩ = a := by
    exact (Function.Embedding.toEquivRange f).symm_apply_apply a
  rw [h]
  rfl

theorem placement_probability_eq {n q : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ) (f g : Placements n k) :
    (∫ G, if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)
      then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n) =
      ∫ G, if ∀ i, MatchesBlock G (blockOfPlacement g i) (k i) (r i)
        then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n := by
  obtain ⟨σ,hσ⟩ := exists_permutation_placements f g
  have he (G : SimpleGraph (Fin n)) :
      (∀ i, MatchesBlock (G.comap σ) (blockOfPlacement f i) (k i) (r i)) ↔
        (∀ i, MatchesBlock G (blockOfPlacement g i) (k i) (r i)) := by
    apply forall_congr'
    intro i
    rw [matchesBlock_comap_permutation,blockOfPlacement_permutation σ f g hσ]
  calc
    _ = ∫ G, if ∀ i, MatchesBlock (G.comap σ) (blockOfPlacement f i) (k i) (r i)
        then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n :=
      (law_expectation_permutation M t ht σ
        (fun G ↦ if ∀ i, MatchesBlock G (blockOfPlacement f i) (k i) (r i)
          then (1 : ℝ) else 0)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact if_congr (he G) rfl rfl

/-- Exact extraction of the paper's ordered vertex-selection factor from
the actual factorial component expectation.  Any one valid placement may
be used for the fixed selected-block event on the right. -/
theorem factorial_expectation_selection_factor {n q : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ) (f₀ : Placements n k) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) =
      ((n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        ∫ G, if ∀ i, MatchesBlock G (blockOfPlacement f₀ i) (k i) (r i)
          then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n := by
  rw [expectation_eq_div_sum_placement_probabilities]
  have hs (f : Placements n k) := placement_probability_eq M t ht k r f f₀
  simp_rw [hs]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_embedding_eq,
    Fintype.card_fin,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  ring

end PerronWright.AnnealedTupleResidualExchangeability
