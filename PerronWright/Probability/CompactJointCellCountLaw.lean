import PerronWright.Probability.CompactSizeCellMomentBounds
import PerronWright.Probability.FactorialCountLimitExistence

/-! # Actual joint component-cell count laws and their unique weak limit

Every source law is the actual sampled-graph window count law. Its
integrability, all mixed factorial limits and summable limiting series
are proved upstream, not required as separate probabilistic interfaces.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology

noncomputable section

namespace PerronWright.CompactJointCellCountLaw

open ComponentWindowMixedFactorials CompactSizeCellFactorialLimits
  CompactSizeCellMomentBounds FactorialCountDeterminacy FactorialCountLimitExistence

variable {D : Type*} [Fintype D]
variable {T : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]

/-- The entire actual joint count-law sequence has a unique weak limit,
and all its literal density factorial moments are identified. The cells
are disjoint Borel size-surplus cells with Lebesgue-null size boundaries;
these are test-cell conditions, not assumptions about a target process. -/
theorem exists_unique_actual_jointCellCountLaw_limit (M : CompactBJRModel T)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    ∃! ν : ProbabilityMeasure (D → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (D → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (D → ℕ)) q =
        cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q) ∧
      Tendsto (fun n ↦ sizeSurplusCountLaw M lambda a b R n J S hJ) atTop (𝓝 ν) :=
  exists_unique_limit_of_factorialMoments
    (fun n ↦ sizeSurplusCountLaw M lambda a b R n J S hJ)
    (fun n q ↦ sizeSurplusCountLaw_mixed_factorial_integrable M lambda a b R n J S hJ q)
    (fun q ↦ cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q)
    (sizeSurplusCountLaw_all_mixed_factorials_tendsto M hM hQP lambda a b ha hab R
      J S hJ hJf hdis)
    (summable_cellMomentMass_factorial _ _ (M.beta_pos hM) ha hab R J S hJ)

end PerronWright.CompactJointCellCountLaw
