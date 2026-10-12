import PerronWright.Probability.BrownianActualWindowCellMoments
import PerronWright.Probability.FiniteBooleanCellRefinement
import PerronWright.Probability.WindowCountGenerators

/-! # Literal factorial-density determination of the actual Brownian window

Nonnegative extended factorial moments determine the genuine canonical
Brownian weak-Borel point law. Their finite values prove candidate
integrability; the actual density bound supplies the summable inversion
series. Boolean refinement reconstructs overlapping rational generators.
No candidate integrability, exponential moment, or zero-boundary-mass
hypothesis is supplied. The point-law criterion only needs cells with
Lebesgue-null size frontiers, as furnished by the graph moment limits.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianActualWindowDeterminacy

open BrownianActualWindowCellMoments BrownianWindowCellTupleGeometry
open BrownianExcursionPointProcessLaw ComponentWindowMixedFactorials
open ComponentWindowPointMeasures PositiveSizeSurplusExhaustion GlobalPointMeasureCharts
open FinitePointMeasureCompact FinitePointMeasureMeasurable FactorialCountDeterminacy
open CompactSizeCellFactorialLimits FiniteBooleanCellRefinement WindowCountGenerators

variable {D : Type*} [Fintype D]

private theorem factorial_nonneg (q n : D → ℕ) : 0 ≤ factorialPolynomial q n :=
  Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

/-- Matching literal nonnegative density moments identifies the full
finite cell-count law, without an assumed integrability or series bound
for the comparison law. -/
theorem actual_cell_countLaw_eq_of_factorial_lintegrals (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (μ : ProbabilityMeasure (D → ℕ))
    (hmom : ∀ q : D → ℕ,
      (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n) ∂(μ : Measure (D → ℕ))) =
        ENNReal.ofReal (cellMomentMass 1 1 lambda (lower m) (upper m) m J S q)) :
    μ = cellCountLaw lambda m J S hJ := by
  let ν := cellCountLaw lambda m J S hJ
  have hν := all_mixed_factorial_moments lambda m J S hJ hdis
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
      (cellCountLaw lambda m J S hJ : Measure (D → ℕ)) q)
    rw [hν.2 q]
  have hs : Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      factorialMoment (μ : Measure (D → ℕ)) q / ∏ i, ((q i).factorial : ℝ)) := by
    simp_rw [heq]
    exact summable_actual_cell_factorial_moments lambda m J S hJ hdis
  apply ProbabilityMeasure.toMeasure_injective
  exact measure_eq_of_factorialMoments (μ : Measure (D → ℕ)) (ν : Measure (D → ℕ))
    hμint hν.1 hs heq

private theorem queryLaw_eq_map_atomLaw (m : ℕ) (μ : ProbabilityMeasure (Chart m))
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    countLaw μ
      (fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells J S hJ i)) =
      (countLaw μ
        (fun k ↦ windowEmbedding (lower m) (upper m) m ⁻¹'
          sizeSurplusCells (atomSizes J m) (atomSurpluses D m) k)
        (fun k ↦ (measurable_windowEmbedding _ _ _)
          (measurableSet_sizeSurplusCells (atomSizes J m) (atomSurpluses D m)
            (fun k ↦ measurableSet_sizeAtom J hJ k.1) k))).map
              (measurable_of_countable (reconstruct S m)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [countLaw_toMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_of_countable (reconstruct S m))
    (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding _ _ _)
      (measurableSet_sizeSurplusCells (atomSizes J m) (atomSurpluses D m)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)))]
  congr 1
  funext η
  exact countVector_eq_reconstruct J S hJ (lower m) (upper m) m η

/-- Literal disjoint-cell density factorial moments on Lebesgue-continuity
size cells uniquely determine
the actual Brownian canonical window probability measure in its existing
weak-Borel space, including multiplicities and overlapping queries. -/
theorem actual_windowLaw_eq_of_density_factorial_lintegrals (lambda : ℝ) (m : ℕ)
    (μ : ProbabilityMeasure (Chart m))
    (hmom : ∀ (D : Type) [Fintype D] (J : D → Set ℝ) (S : D → Finset ℕ)
      (q : D → ℕ), (∀ i, MeasurableSet (J i)) →
      (∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) →
      Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)) →
      (∫⁻ η, ENNReal.ofReal (mixedStatistic m J S q η) ∂(μ : Measure (Chart m))) =
        ENNReal.ofReal (cellMomentMass 1 1 lambda (lower m) (upper m) m J S q)) :
    μ = BrownianExcursionPointProcessLaw.windowLaw lambda m := by
  apply probabilityMeasure_eq_of_finite_cell_countLaws (lower m) (upper m) m (lower_le_upper m)
  intro I
  let J : I → Set ℝ := fun i ↦ sizeCell m i.val
  let S : I → Finset ℕ := fun i ↦ surplusCell m i.val
  have hJ (i : I) : MeasurableSet (J i) := measurableSet_sizeCell m i.val
  have hJf (i : I) : (volume : Measure ℝ) (frontier (J i)) = 0 :=
    volume_frontier_sizeCell m i.val
  let A := atomSizes J m
  let B := atomSurpluses I m
  have hA (k : AtomIndex I m) : MeasurableSet (A k) := measurableSet_sizeAtom J hJ k.1
  let α := countLaw μ
    (fun k ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells A B k)
    (fun k ↦ (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells A B hA k))
  have hαmom (q : AtomIndex I m → ℕ) :
      (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n)
        ∂(α : Measure (AtomIndex I m → ℕ))) =
      ENNReal.ofReal (cellMomentMass 1 1 lambda (lower m) (upper m) m A B q) := by
    change (∫⁻ n, ENNReal.ofReal (factorialPolynomial q n)
      ∂(μ : Measure (Chart m)).map _) = _
    rw [lintegral_map (measurable_of_countable (factorialPolynomial q)).ennreal_ofReal
      (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding _ _ _)
        (measurableSet_sizeSurplusCells A B hA k)))]
    exact hmom (AtomIndex I m) A B q hA
      (fun k ↦ volume_frontier_sizeAtom J hJf k.1) (atomCells_disjoint J m)
  have hα := actual_cell_countLaw_eq_of_factorial_lintegrals lambda m A B hA
    (atomCells_disjoint J m) α hαmom
  change countLaw μ
    (fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ measurableSet_cell (lower m) (upper m) m i.val) =
    countLaw (BrownianExcursionPointProcessLaw.windowLaw lambda m)
    (fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ measurableSet_cell (lower m) (upper m) m i.val)
  rw [queryLaw_eq_map_atomLaw m μ J S hJ,
    queryLaw_eq_map_atomLaw m (BrownianExcursionPointProcessLaw.windowLaw lambda m) J S hJ]
  change α.map (measurable_of_countable (reconstruct S m)).aemeasurable =
    (cellCountLaw lambda m A B hA).map (measurable_of_countable (reconstruct S m)).aemeasurable
  rw [hα]

end PerronWright.BrownianActualWindowDeterminacy
