import PerronWright.Probability.FiniteIrreducibleWindowPointLawLimit
import PerronWright.Probability.FiniteIrreducibleJointCellCountLaw

/-! # Literal density moments of the genuine spatial window limit

The actual point-law limit is pushed forward through half-open interval
counts. Boundary nullity is proved from the actual graph laws. The
proved full joint count-law limit therefore identifies all its mixed
factorial moments with literal labelled factorial-density integrals.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleWindowDensityMoments

open ComponentWindowPointMeasures ComponentWindowMixedFactorials
open FinitePointMeasureCompact FinitePointMeasureMeasurable FactorialCountDeterminacy
open CompactSizeCellFactorialLimits (cellMomentMass)
open FiniteIrreducibleComponentProcess FiniteIrreducibleWindowBoundary
open FiniteIrreducibleJointCellCountLaw PointMeasureCountMapping

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Actual interval-cell factorial moments of every genuine full window
weak limit. No target moment or frontier-nullity premise is used. -/
theorem interval_cell_factorials_of_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Finset ℕ)
    (hdis : Pairwise (fun i j ↦ Disjoint
      (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T i)
      (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T j))) :
    (∀ q, Integrable (factorialPolynomial q)
      (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
        (fun i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ))) ∧
    (∀ q, factorialMoment
      (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
        (fun i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ)) q =
        cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R
          (fun i ↦ Set.Ico (lo i) (hi i)) T q) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a,le_rfl,hab⟩,⟨0,by omega⟩)⟩
  let J : Fin d → Set ℝ := fun i ↦ Set.Ico (lo i) (hi i)
  have hJ : ∀ i, MeasurableSet (J i) := fun _ ↦ measurableSet_Ico
  have hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0 :=
    fun i ↦ SizeCellIndicators.volume_frontier_Ico (lo i) (hi i)
  let A : Fin d → Set (SurplusWindow a b R) :=
    fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J T i
  have hA : ∀ i, MeasurableSet (A i) :=
    fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J T hJ i)
  have hfront : ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ∀ i, ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (A i)) = 0 :=
    ae_all_iff.mpr (fun i ↦ ae_Ico_cell_frontier_eq_zero M hM lambda a b ha hab R
      v E hE hround id tendsto_id ν hν (lo i) (hi i) (T i : Set ℕ))
  have hmap := countLaw_tendsto_of_ae_null_frontiers
    (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) ν hν A hA hfront
  obtain ⟨μ,hμ,_⟩ := exists_unique_actual_jointCellCountLaw_limit M hM lambda a b ha hab R
    J T hJ hJf hdis v E hE hround
  have ht : Tendsto (fun n ↦ countLaw (unmarkedWindowLaw M lambda a b R n (v n)) A hA)
      atTop (𝓝 μ) := hμ.2.2
  have he : countLaw ν A hA = μ := tendsto_nhds_unique hmap ht
  change (∀ q, Integrable (factorialPolynomial q) (countLaw ν A hA : Measure (Fin d → ℕ))) ∧
    (∀ q, factorialMoment (countLaw ν A hA : Measure (Fin d → ℕ)) q =
      cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J T q)
  rw [he]
  exact ⟨hμ.1,hμ.2.1⟩

/-- A genuine spatial window limit simultaneously realizes every finite
disjoint half-open interval/surplus mixed factorial-density integral. -/
theorem exists_actual_window_limit_with_all_interval_factorials
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    ∃ ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) atTop (𝓝 ν) ∧
      ∀ (d : ℕ) (lo hi : Fin d → ℝ) (T : Fin d → Finset ℕ),
        Pairwise (fun i j ↦ Disjoint
          (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T i)
          (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T j)) →
        (∀ q, Integrable (factorialPolynomial q)
          (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
            (fun i ↦ (measurable_windowEmbedding a b R)
              (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ))) ∧
        (∀ q, factorialMoment
          (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
            (fun i ↦ (measurable_windowEmbedding a b R)
              (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ)) q =
            cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R
              (fun i ↦ Set.Ico (lo i) (hi i)) T q) := by
  obtain ⟨ν,hν,_⟩ := FiniteIrreducibleWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
    M hM lambda a b ha hab R v E hE hround
  refine ⟨ν,hν,?_⟩
  intro d lo hi T hdis
  exact interval_cell_factorials_of_limit M hM lambda a b ha hab R v E hE hround ν hν lo hi T hdis

end PerronWright.FiniteIrreducibleWindowDensityMoments
