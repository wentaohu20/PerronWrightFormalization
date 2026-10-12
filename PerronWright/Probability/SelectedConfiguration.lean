import PerronWright.Probability.AnnealedGraph
import PerronWright.Probability.ComponentBlocks

/-!
# Exact probabilities for isolated configurations

The constrained edge set consists of all pairs meeting the selected block.
Its internal values prescribe a graph, while its boundary values prohibit
edges to the remaining vertices.  All edges between unselected vertices
are summed out exactly.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.SelectedConfiguration

open AnnealedGraph ComponentBlocks

/-- Whether an unordered pair touches the selected vertex block. -/
def touches {n : ℕ} (B : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  Sym2.lift ⟨fun i j ↦ i ∈ B ∨ j ∈ B, by
    intro i j
    exact propext or_comm⟩ e

@[simp] theorem touches_mk {n : ℕ} (B : Finset (Fin n)) (i j : Fin n) :
    touches B s(i, j) ↔ i ∈ B ∨ j ∈ B := Iff.rfl

/-- The edges constrained by the isolated-configuration event. -/
def prescribedEdges {n : ℕ} (B : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e ↦ touches B e.val)

@[simp] theorem mem_prescribedEdges {n : ℕ} (B : Finset (Fin n)) (e : Edge n) :
    e ∈ prescribedEdges B ↔ touches B e.val := by
  simp [prescribedEdges]

/-- The edge assignment agrees with the candidate graph on every pair
meeting the selected block. -/
def Event {n : ℕ} (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (a : Assignment n) : Prop :=
  IndependentEdges.AgreesOn (prescribedEdges B) (assignmentOfGraph H) a

theorem agrees_adj_iff {n : ℕ} {B : Finset (Fin n)}
    {H : SimpleGraph (Fin n)} {a : Assignment n} (ha : Event B H a)
    (i j : Fin n) (hij : i ≠ j) (hB : i ∈ B ∨ j ∈ B) :
    (toGraph a).Adj i j ↔ H.Adj i j := by
  let e : Edge n := ⟨s(i, j), by simpa only [Sym2.mk_isDiag_iff] using hij⟩
  have he : e ∈ prescribedEdges B := (mem_prescribedEdges B e).mpr hB
  have hv := ha e he
  have hm := mem_toGraph_edgeSet a e
  rw [hv] at hm
  simpa only [e, assignmentOfGraph, decide_eq_true_eq,
    SimpleGraph.mem_edgeSet] using hm

/-- The finite edge constraints are precisely connectivity-independent
internal-graph agreement and isolation of the selected block. -/
theorem event_iff_induce_and_isolated {n : ℕ}
    (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hH : Isolated H (B : Set (Fin n))) (a : Assignment n) :
    Event B H a ↔
      (toGraph a).induce (B : Set (Fin n)) = H.induce (B : Set (Fin n)) ∧
        Isolated (toGraph a) (B : Set (Fin n)) := by
  constructor
  · intro ha
    constructor
    · apply SimpleGraph.ext
      funext i j
      apply propext
      change (toGraph a).Adj i.val j.val ↔ H.Adj i.val j.val
      by_cases hij : i.val = j.val
      · simp [hij]
      · exact agrees_adj_iff ha i.val j.val hij (Or.inl i.property)
    · intro i hi j hij
      have hne := (toGraph a).ne_of_adj hij
      exact hH i hi j ((agrees_adj_iff ha i j hne (Or.inl hi)).mp hij)
  · rintro ⟨hgraph, hiso⟩
    intro e he
    rcases e with ⟨e, hdiag⟩
    induction e using Sym2.inductionOn with
    | _ i j =>
      have hij : i ≠ j := by simpa only [Sym2.mk_isDiag_iff] using hdiag
      have hB : i ∈ B ∨ j ∈ B := (mem_prescribedEdges B ⟨s(i, j), hdiag⟩).mp he
      have hrel : (toGraph a).Adj i j ↔ H.Adj i j := by
        by_cases hi : i ∈ B
        · by_cases hj : j ∈ B
          · exact Iff.of_eq (congrArg
              (fun G : SimpleGraph (B : Set (Fin n)) ↦ G.Adj ⟨i, hi⟩ ⟨j, hj⟩) hgraph)
          · exact iff_of_false (fun h ↦ hj (hiso i hi j h))
              (fun h ↦ hj (hH i hi j h))
        · have hj : j ∈ B := hB.resolve_left hi
          exact iff_of_false (fun h ↦ hi (hiso j hj i h.symm))
            (fun h ↦ hi (hH j hj i h.symm))
      have hm := mem_toGraph_edgeSet a ⟨s(i, j), hdiag⟩
      simp only [SimpleGraph.mem_edgeSet] at hm
      have heq : a ⟨s(i, j), hdiag⟩ = true ↔
          assignmentOfGraph H ⟨s(i, j), hdiag⟩ = true := by
        simpa only [assignmentOfGraph, decide_eq_true_eq, SimpleGraph.mem_edgeSet]
          using hm.symm.trans hrel
      exact Bool.eq_iff_iff.mpr heq

/-- If the candidate block is internally connected, the event makes it
the support of an actual connected component. -/
theorem event_exists_component {n : ℕ} (B : Finset (Fin n))
    (H : SimpleGraph (Fin n)) (hH : Isolated H (B : Set (Fin n)))
    (hconn : (H.induce (B : Set (Fin n))).Connected)
    {a : Assignment n} (ha : Event B H a) :
    ∃ C : (toGraph a).ConnectedComponent, C.supp = (B : Set (Fin n)) := by
  obtain ⟨heq, hiso⟩ := (event_iff_induce_and_isolated B H hH a).mp ha
  apply (connected_isolated_iff_component (toGraph a) (B : Set (Fin n))).mp
  refine ⟨?_, hiso⟩
  rw [heq]
  exact hconn

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exact annealed probability of any partial edge configuration. -/
theorem expectation_prescribed (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (D : Finset (Edge n)) (c : Assignment n) :
    (∫ a : Assignment n,
      if IndependentEdges.AgreesOn D c a then (1 : ℝ) else 0
      ∂(AnnealedGraph.pmf M t ht n).toMeasure) =
      ∫ x : Fin n → S,
        ∏ e ∈ D, IndependentEdges.edgeMass (hazard M t x e) (c e)
        ∂typeLaw M n := by
  rw [PMF.integral_eq_sum]
  simp only [AnnealedGraph.pmf_apply_toReal, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  have hs (a : Assignment n) :
      (if IndependentEdges.AgreesOn D c a then AnnealedGraph.mass M t a else 0) =
        ∫ x : Fin n → S,
          if IndependentEdges.AgreesOn D c a then conditionalMass M t x a else 0
          ∂typeLaw M n := by
    split_ifs <;> simp [AnnealedGraph.mass]
  simp_rw [hs]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    exact IndependentEdges.sum_mass_agreesOn (hazard M t x) D c
  · intro a _
    by_cases ha : IndependentEdges.AgreesOn D c a
    · simpa only [if_pos ha] using conditionalMass_integrable M t a
    · simp only [if_neg ha]
      exact integrable_const (0 : ℝ)

/-- Exact exponential-odds formula for a selected isolated configuration. -/
theorem probability_event_odds (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n)) :
    (∫ a : Assignment n, if Event B H a then (1 : ℝ) else 0
      ∂(AnnealedGraph.pmf M t ht n).toMeasure) =
      ∫ x : Fin n → S,
        Real.exp (-(∑ e ∈ prescribedEdges B, hazard M t x e)) *
          ∏ e ∈ prescribedEdges B,
            if assignmentOfGraph H e then Real.exp (hazard M t x e) - 1 else 1
          ∂typeLaw M n := by
  calc
    _ = ∫ x : Fin n → S,
        ∏ e ∈ prescribedEdges B,
          IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph H e)
        ∂typeLaw M n :=
      expectation_prescribed M t ht n (prescribedEdges B) (assignmentOfGraph H)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact IndependentEdges.prescribedMass_odds _ _ _

/-- Exact elimination of all edges outside a prescribed finite set, for
every observable determined by the prescribed edge pattern. -/
theorem expectation_local_patterns (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (D : Finset (Edge n)) (F : Assignment n → ℝ)
    (hF : ∀ a, F a = F (IndependentEdges.extend D
      (IndependentEdges.restrict D a))) :
    (∫ a, F a ∂(AnnealedGraph.pmf M t ht n).toMeasure) =
      ∫ x : Fin n → S,
        ∑ c : D → Bool,
          (∏ e ∈ D, IndependentEdges.edgeMass (hazard M t x e)
            (IndependentEdges.extend D c e)) * F (IndependentEdges.extend D c)
        ∂typeLaw M n := by
  rw [PMF.integral_eq_sum]
  simp only [AnnealedGraph.pmf_apply_toReal, smul_eq_mul, AnnealedGraph.mass]
  have hs (a : Assignment n) :
      (∫ x : Fin n → S, conditionalMass M t x a ∂typeLaw M n) * F a =
      ∫ x : Fin n → S, conditionalMass M t x a * F a ∂typeLaw M n :=
    (integral_mul_const _ _).symm
  simp_rw [hs]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    exact IndependentEdges.sum_mass_mul_local (hazard M t x) D F hF
  · intro a _
    exact (conditionalMass_integrable M t a).mul_const _

end PerronWright.SelectedConfiguration
