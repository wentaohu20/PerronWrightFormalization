import PerronWright.Probability.FiniteIrreducibleJointCellCountLaw
import PerronWright.Probability.FiniteBooleanCellRefinement

/-! # Actual weak limits of possibly overlapping window count queries

The source count law is exactly the finite linear reconstruction of its
disjoint Boolean size atoms and literal surplus fibers. The atom moments,
series and unique limit are all proved, including the atom boundary test.
No count convergence or target realization is supplied as an input.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleOverlappingCellCountLaw

open FiniteBooleanCellRefinement FiniteIrreducibleJointCellCountLaw
  ComponentWindowMixedFactorials ComponentWindowPointMeasures FinitePointMeasureMeasurable
open FiniteIrreducibleCellFactorialCounts

variable {D : Type*} [Fintype D]
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem continuous_reconstruct (S : D → Finset ℕ) (R : ℕ) :
    Continuous (reconstruct S R) := continuous_of_discreteTopology

theorem actualQueryLaw_eq_map_atomLaw (M : FiniteIrreducibleModel T) (lambda a b : ℝ)
    (R n : ℕ) (x0 : Fin n → T) (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R n x0 J S hJ =
      (FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R n x0 (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1)).map
          (continuous_reconstruct S R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw,countLaw_toMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_reconstruct S R).measurable
    (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)))]
  congr 1
  funext η
  exact countVector_eq_reconstruct J S hJ a b R η


variable [MetricSpace T] [DiscreteTopology T] [MeasurableSpace T] [BorelSpace T]

/-- Arbitrary finite overlapping Borel size-surplus queries of the
actual model window law have a unique weak limit. The proof constructs
the law from the actual disjoint refinement rather than assuming its
existence or treating overlapping mixed moments as disjoint ones. -/
theorem exists_unique_actual_overlappingCellCountLaw_limit (M : FiniteIrreducibleModel T)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (v : (n : ℕ) → Fin n → T) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (D → ℕ),
      Tendsto (fun n ↦ FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R n (v n) J S hJ) atTop (𝓝 ν) := by
  obtain ⟨μ,hμ,_⟩ := exists_unique_actual_jointCellCountLaw_limit M hM lambda a b ha hab R
    (atomSizes J R) (atomSurpluses D R) (fun k ↦ measurableSet_sizeAtom J hJ k.1)
    (fun k ↦ volume_frontier_sizeAtom J hJf k.1) (atomCells_disjoint J R) v E hE hround
  let ν := μ.map (continuous_reconstruct S R).measurable.aemeasurable
  have ht : Tendsto (fun n ↦ FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R n (v n) J S hJ) atTop (𝓝 ν) := by
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ μ hμ.2.2
      (continuous_reconstruct S R)
    simpa only [← actualQueryLaw_eq_map_atomLaw M lambda a b R _ (v _) J S hJ] using hm
  exact ⟨ν,ht,fun ρ hρ ↦ tendsto_nhds_unique hρ ht⟩

end PerronWright.FiniteIrreducibleOverlappingCellCountLaw

