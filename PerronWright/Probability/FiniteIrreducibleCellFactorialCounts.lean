import PerronWright.Probability.FiniteIrreducibleComponentProcess
import PerronWright.Probability.ComponentWindowMixedFactorials

/-! # Exact mixed cell factorials of the actual fixed-type graph law

The pure injective-component tuple identities are reused, while every
source probability measure is the literal fixed assignment graph law.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleCellFactorialCounts

open ComponentCounts ComponentWindowPointMeasures ComponentWindowMixedFactorials
open FiniteIrreducibleComponentProcess FinitePointMeasureCompact
  FinitePointMeasureMixedFactorials FactorialCountDeterminacy

variable {D : Type*} [Fintype D]
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem windowLaw_mixed_factorial_integrable (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (fun η ↦ factorialPolynomial q (fun i ↦ count η (A i)))
      (unmarkedWindowLaw M lambda a b R n x0 : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R n x0 (measurable_window_mixed_factorial a b R A q hAm)

theorem windowLaw_mixed_factorial_expectation_eq_card (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (hAm : ∀ i, MeasurableSet (A i)) :
    (∫ η, factorialPolynomial q (fun i ↦ count η (A i))
      ∂(unmarkedWindowLaw M lambda a b R n x0 : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∫ G, (Fintype.card (OrderedCellTuples (windowAtom a b R 1 (G := G)) A q) : ℝ)
        ∂graphLaw M lambda n x0 := by
  have hm := measurable_window_mixed_factorial a b R A q hAm
  rw [windowLaw_integral M lambda a b R n x0 hm]
  simp_rw [window_mixed_factorial_eq_card a b R 1 _ A q hA hAm]

/-- The actual count-vector pushforward law has these same genuine
component-tuple mixed factorial moments. -/
theorem windowCountLaw_mixed_integral_eq_card (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (hAm : ∀ i, MeasurableSet (A i)) :
    (∫ y, factorialPolynomial q y ∂(FinitePointMeasureMeasurable.countLaw
      (unmarkedWindowLaw M lambda a b R n x0) A hAm : Measure (D → ℕ))) =
      ∫ G, (Fintype.card (OrderedCellTuples (windowAtom a b R 1 (G := G)) A q) : ℝ)
        ∂graphLaw M lambda n x0 := by
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure,
    integral_map (FinitePointMeasureMeasurable.measurable_count_vector A hAm).aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  exact windowLaw_mixed_factorial_expectation_eq_card M lambda a b R n x0 A q hA hAm

theorem windowCountLaw_mixed_factorial_integrable (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (factorialPolynomial q) (FinitePointMeasureMeasurable.countLaw
      (unmarkedWindowLaw M lambda a b R n x0) A hAm : Measure (D → ℕ)) := by
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure]
  exact (integrable_map_measure (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    (FinitePointMeasureMeasurable.measurable_count_vector A hAm).aemeasurable).mpr
      (windowLaw_mixed_factorial_integrable M lambda a b R n x0 A q hAm)

theorem windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n : ℕ) (x0 : Fin n → T) (hn : 0 < n)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ η, factorialPolynomial q (fun i ↦ count η
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))
      ∂(unmarkedWindowLaw M lambda a b R n x0 : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices n a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0) := by
  have hm := measurable_window_mixed_factorial a b R
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i) q
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
  rw [windowLaw_integral M lambda a b R n x0 hm]
  simp_rw [window_sizeSurplus_mixed_factorial_eq_sum _ hn a b hb R J S q hJ hdis]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

/-- The genuine finite-dimensional count law of these actual window
cells. Its source is the actual fixed assignment graph law. -/
def sizeSurplusCountLaw (M : FiniteIrreducibleModel T) (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    ProbabilityMeasure (D → ℕ) :=
  FinitePointMeasureMeasurable.countLaw (unmarkedWindowLaw M lambda a b R n x0)
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

theorem sizeSurplusCountLaw_mixed_factorial_integrable (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (R n : ℕ) (x0 : Fin n → T) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ) :
    Integrable (factorialPolynomial q) (sizeSurplusCountLaw M lambda a b R n x0 J S hJ :
      Measure (D → ℕ)) :=
  windowCountLaw_mixed_factorial_integrable M lambda a b R n x0 _ q
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

/-- The complete actual finite-dimensional mixed count-law moment
identity, with no mixed-moment identification premise. -/
theorem sizeSurplusCountLaw_mixed_factorial_integral_eq_sum (M : FiniteIrreducibleModel T)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n : ℕ) (x0 : Fin n → T) (hn : 0 < n)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ y, factorialPolynomial q y ∂(sizeSurplusCountLaw M lambda a b R n x0 J S hJ :
      Measure (D → ℕ))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices n a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0) := by
  unfold sizeSurplusCountLaw
  rw [FinitePointMeasureMeasurable.countLaw_toMeasure,
    integral_map (FinitePointMeasureMeasurable.measurable_count_vector _
      (fun i ↦ (measurable_windowEmbedding a b R)
        (measurableSet_sizeSurplusCells J S hJ i))).aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  exact windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum M lambda a b hb R n x0 hn
    J S q hJ hdis

end PerronWright.FiniteIrreducibleCellFactorialCounts

