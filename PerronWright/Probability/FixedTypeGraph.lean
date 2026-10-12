import PerronWright.Probability.ExactFactorialExpectation
import PerronWright.Probability.ComponentPointProcesses

/-!
# Fixed-type finite graph laws

The edge hazards may come from deterministic finite types or from a
countable kernel restricted to a finite typed vertex set.  The probability
law below needs neither compactness of the type space nor an annealed type
law.  Its finite factorial formula is proved on genuine graph components.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FixedTypeGraph

open AnnealedGraph SelectedConfiguration ComponentCounts ExactFactorialExpectation

/-- A finite independent-edge graph probability mass function. -/
def graphPMF {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e) :
    PMF (SimpleGraph (Fin n)) := (IndependentEdges.pmf z hz).map toGraph

/-- The probability law on actual labelled graphs with the given hazards. -/
def law {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e) :
    Measure (SimpleGraph (Fin n)) := (graphPMF z hz).toMeasure

instance law_isProbability {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e) :
    IsProbabilityMeasure (law z hz) :=
  inferInstanceAs (IsProbabilityMeasure (graphPMF z hz).toMeasure)

/-- Every graph expectation is the literal independent-edge finite sum. -/
theorem expectation_eq_sum {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e)
    (F : SimpleGraph (Fin n) → ℝ) :
    (∫ G, F G ∂law z hz) =
      ∑ a : Assignment n, IndependentEdges.mass z a * F (toGraph a) := by
  unfold law graphPMF
  rw [← PMF.toMeasure_map toGraph (IndependentEdges.pmf z hz) (measurable_toGraph n)]
  rw [integral_map (measurable_toGraph n).aemeasurable
    (measurable_of_finite F).aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [IndependentEdges.pmf_apply_toReal, smul_eq_mul]

/-- Integrating unobserved edges gives an exact finite local-pattern sum. -/
theorem expectation_local_patterns {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e)
    (D : Finset (Edge n)) (F : SimpleGraph (Fin n) → ℝ)
    (hF : ∀ a : Assignment n, F (toGraph a) = F (toGraph (IndependentEdges.extend D
      (IndependentEdges.restrict D a)))) :
    (∫ G, F G ∂law z hz) =
      ∑ c : D → Bool,
        (∏ e ∈ D, IndependentEdges.edgeMass (z e) (IndependentEdges.extend D c e)) *
          F (toGraph (IndependentEdges.extend D c)) := by
  rw [expectation_eq_sum]
  exact IndependentEdges.sum_mass_mul_local z D (fun a ↦ F (toGraph a)) hF

/-- Exact isolated connected-block probability for a fixed type assignment. -/
theorem block_probability_odds {n q : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e)
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) :
    (∫ G, if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0 ∂law z hz) =
      ∑ c : prescribedEdges (selectedUnion B) → Bool,
        Real.exp (-(∑ e ∈ prescribedEdges (selectedUnion B), z e)) *
          (∏ e ∈ prescribedEdges (selectedUnion B),
            if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
            then Real.exp (z e) - 1 else 1) *
          (if ∀ i, MatchesBlock
            (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))
            (B i) (k i) (r i) then (1 : ℝ) else 0) := by
  rw [expectation_local_patterns z hz (prescribedEdges (selectedUnion B))
    (fun G ↦ if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0)
    (fun a ↦ if_congr (matchesTuple_local B k r a) rfl rfl)]
  apply Finset.sum_congr rfl
  intro c _
  rw [IndependentEdges.prescribedMass_odds]

/-- The literal finite factorial expectation for deterministic types.
This counts ordered distinct genuine components, not arbitrary disjoint
graphs supplied as a surrogate random variable. -/
theorem factorial_expectation_exact {n q : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e)
    (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂law z hz) =
      ∑ B : Fin q ↪ Finset (Fin n),
        ∑ c : prescribedEdges (selectedUnion B) → Bool,
          Real.exp (-(∑ e ∈ prescribedEdges (selectedUnion B), z e)) *
            (∏ e ∈ prescribedEdges (selectedUnion B),
              if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
              then Real.exp (z e) - 1 else 1) *
            (if ∀ i, MatchesBlock
              (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))
              (B i) (k i) (r i) then (1 : ℝ) else 0) := by
  simp_rw [count_cast_eq_sum_blocks]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro B _
    exact block_probability_odds z hz B k r
  · intro B _
    exact Integrable.of_finite

variable {S : Type*} [MeasurableSpace S]

/-- The graph law and empirical component marks for a deterministic type
vector; it also applies to countably many possible types. -/
def markedLaw {n : ℕ} (z : Edge n → ℝ) (hz : ∀ e, 0 ≤ z e) (x : Fin n → S) :
    Measure (Measure ((ℝ × ℕ) × ProbabilityMeasure S)) :=
  (law z hz).map (fun G ↦ ComponentPointProcesses.marked G x)

instance markedLaw_isProbability {n : ℕ} (z : Edge n → ℝ)
    (hz : ∀ e, 0 ≤ z e) (x : Fin n → S) : IsProbabilityMeasure (markedLaw z hz x) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

end PerronWright.FixedTypeGraph
