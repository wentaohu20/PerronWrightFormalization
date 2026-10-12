import PerronWright.Probability.BrownianActualArbitraryWindowCellMoments
import PerronWright.Probability.FiniteBooleanCellRefinement
import PerronWright.Probability.WindowCountGenerators

/-! # Density determination in every actual Brownian closed window

The comparison law needs only the literal nonnegative density factorial
moments. Their finite values prove integrability, and the proved actual
Brownian moments supply the determination series. Boolean refinement
recovers the rational count generators of the entire weak-Borel law.
No comparison-law integrability, series, or boundary-nullity interface
is assumed. All positive closed windows, including singletons, occur.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianActualArbitraryWindowDeterminacy

open BrownianActualArbitraryWindowCellMoments ComponentWindowMixedFactorials
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMeasurable
open FactorialCountDeterminacy CompactSizeCellFactorialLimits
open FiniteBooleanCellRefinement WindowCountGenerators

variable {D : Type*} [Fintype D]

private theorem factorial_nonneg (q n : D → ℕ) : 0 ≤ factorialPolynomial q n :=
  Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

/-- The literal density moments determine the full disjoint-cell count
law in an arbitrary positive closed window. -/
theorem actual_cell_countLaw_eq_of_factorial_lintegrals (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (μ : ProbabilityMeasure (D → ℕ))
    (hmom : ∀ q : D → ℕ,
      (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n) ∂(μ : Measure (D → ℕ))) =
        ENNReal.ofReal (cellMomentMass 1 1 lambda a b R J S q)) :
    μ = cellCountLaw lambda a b R ha hab J S hJ := by
  let ν := cellCountLaw lambda a b R ha hab J S hJ
  have hν := all_mixed_factorial_moments lambda a b R ha hab J S hJ hdis
  have hμint (q : D → ℕ) : Integrable (factorialPolynomial q) (μ : Measure (D → ℕ)) := by
    refine ⟨(measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (factorial_nonneg q)),hmom q]
    exact ENNReal.ofReal_lt_top
  have heq (q : D → ℕ) : factorialMoment (μ : Measure (D → ℕ)) q =
      factorialMoment (ν : Measure (D → ℕ)) q := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg (factorial_nonneg q)) (integral_nonneg (factorial_nonneg q))).mp
    change ENNReal.ofReal (∫ n, factorialPolynomial q n ∂(μ : Measure (D → ℕ))) =
      ENNReal.ofReal (∫ n, factorialPolynomial q n ∂(ν : Measure (D → ℕ)))
    rw [ofReal_integral_eq_lintegral_ofReal (hμint q)
      (Eventually.of_forall (factorial_nonneg q)),hmom q]
    change _ = ENNReal.ofReal (factorialMoment
      (cellCountLaw lambda a b R ha hab J S hJ : Measure (D → ℕ)) q)
    rw [hν.2 q]
  have hs : Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      factorialMoment (μ : Measure (D → ℕ)) q / ∏ i, ((q i).factorial : ℝ)) := by
    simp_rw [heq]
    exact summable_actual_cell_factorial_moments lambda a b R ha hab J S hJ hdis
  apply ProbabilityMeasure.toMeasure_injective
  exact measure_eq_of_factorialMoments (μ : Measure (D → ℕ)) (ν : Measure (D → ℕ))
    hμint hν.1 hs heq

private theorem queryLaw_eq_map_atomLaw (a b : ℝ) (R : ℕ)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    countLaw μ
      (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)) =
      (countLaw μ
        (fun k ↦ windowEmbedding a b R ⁻¹'
          sizeSurplusCells (atomSizes J R) (atomSurpluses D R) k)
        (fun k ↦ (measurable_windowEmbedding a b R)
          (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
            (fun k ↦ measurableSet_sizeAtom J hJ k.1) k))).map
              (measurable_of_countable (reconstruct S R)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [countLaw_toMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_of_countable (reconstruct S R))
    (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)))]
  congr 1
  funext η
  exact countVector_eq_reconstruct J S hJ a b R η

/-- Disjoint Lebesgue-continuity size-cell density moments identify the
entire actual Brownian point law in every positive closed window. -/
theorem actual_windowLaw_eq_of_density_factorial_lintegrals (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hmom : ∀ (D : Type) [Fintype D] (J : D → Set ℝ) (S : D → Finset ℕ)
      (q : D → ℕ), (∀ i, MeasurableSet (J i)) →
      (∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) →
      Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)) →
      (∫⁻ η, ENNReal.ofReal (mixedStatistic a b R J S q η)
        ∂(μ : Measure (PointMeasure (SurplusWindow a b R)))) =
        ENNReal.ofReal (cellMomentMass 1 1 lambda a b R J S q)) :
    μ = BrownianArbitraryWindowLaw.law lambda a b R ha hab := by
  apply probabilityMeasure_eq_of_finite_cell_countLaws a b R hab
  intro I
  let J : I → Set ℝ := fun i ↦ sizeCell R i.val
  let S : I → Finset ℕ := fun i ↦ surplusCell R i.val
  have hJ (i : I) : MeasurableSet (J i) := measurableSet_sizeCell R i.val
  have hJf (i : I) : (volume : Measure ℝ) (frontier (J i)) = 0 :=
    volume_frontier_sizeCell R i.val
  let A := atomSizes J R
  let B := atomSurpluses I R
  have hA (k : AtomIndex I R) : MeasurableSet (A k) := measurableSet_sizeAtom J hJ k.1
  let α := countLaw μ
    (fun k ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells A B k)
    (fun k ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells A B hA k))
  have hαmom (q : AtomIndex I R → ℕ) :
      (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n)
        ∂(α : Measure (AtomIndex I R → ℕ))) =
      ENNReal.ofReal (cellMomentMass 1 1 lambda a b R A B q) := by
    change (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n)
      ∂(μ : Measure (PointMeasure (SurplusWindow a b R))).map _) = _
    rw [lintegral_map (measurable_of_countable (factorialPolynomial q)).ennreal_ofReal
      (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding a b R)
        (measurableSet_sizeSurplusCells A B hA k)))]
    exact hmom (AtomIndex I R) A B q hA
      (fun k ↦ volume_frontier_sizeAtom J hJf k.1) (atomCells_disjoint J R)
  have hα := actual_cell_countLaw_eq_of_factorial_lintegrals lambda a b R ha hab A B hA
    (atomCells_disjoint J R) α hαmom
  change countLaw μ
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ measurableSet_cell a b R i.val) =
    countLaw (BrownianArbitraryWindowLaw.law lambda a b R ha hab)
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ measurableSet_cell a b R i.val)
  rw [queryLaw_eq_map_atomLaw a b R μ J S hJ,
    queryLaw_eq_map_atomLaw a b R (BrownianArbitraryWindowLaw.law lambda a b R ha hab) J S hJ]
  change α.map (measurable_of_countable (reconstruct S R)).aemeasurable =
    (cellCountLaw lambda a b R ha hab A B hA).map
      (measurable_of_countable (reconstruct S R)).aemeasurable
  rw [hα]

end PerronWright.BrownianActualArbitraryWindowDeterminacy
