import PerronWright.Probability.CompactWindowPointLawLimit
import PerronWright.Probability.CompactJointCellCountLaw

/-!
# Literal density moments of the actual limiting window point law

The point-law limit is constructed upstream from the real graph law.
For disjoint cells with finite size boundaries, the proved boundary
nullity passes actual count laws to that limit. Uniqueness of the
already proved count-law limit then identifies every factorial moment,
including zero. No moment identity of a target process is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section

namespace PerronWright.CompactWindowLimitCellMoments

open FinitePointMeasureCompact FinitePointMeasureMeasurable
open ComponentWindowPointMeasures ComponentWindowMixedFactorials CompactSizeCellFactorialLimits
open FactorialCountDeterminacy PointMeasureCountMapping CompactWindowBoundary

variable {D : Type*} [Fintype D]
variable {T : Type*} [MeasurableSpace T] [MetricSpace T] [CompactSpace T] [BorelSpace T]

def pointLawCellCounts (a b : ℝ) (R : ℕ)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    ProbabilityMeasure (D → ℕ) :=
  countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

/-- Factorial moments of actual cell counts under the actual point-law
limit are the literal integrals of the stated Perron--Wright density. -/
theorem all_mixed_factorial_moments (M : CompactBJRModel T)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (unmarkedWindowLaw M lambda a b R) atTop (𝓝 ν))
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (lo hi : D → ℝ) (hfront : ∀ i, frontier (J i) ⊆ {lo i, hi i})
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∀ q, Integrable (factorialPolynomial q)
      (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ))) ∧
    (∀ q, factorialMoment (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ)) q =
      cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  have hsource : Tendsto (fun n ↦ sizeSurplusCountLaw M lambda a b R n J S hJ)
      atTop (𝓝 (pointLawCellCounts a b R ν J S hJ)) := by
    apply countLaw_tendsto_of_ae_null_frontiers _ ν hν
      (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
    exact ae_all_iff.mpr (fun i ↦ ae_sizeSurplusCell_frontier_eq_zero
      M hM hQP lambda a b ha hab R id tendsto_id ν (by simpa only [id_eq] using hν)
      (J i) (S i : Set ℕ) (lo i) (hi i) (hfront i))
  obtain ⟨θ, hθ, _⟩ := CompactJointCellCountLaw.exists_unique_actual_jointCellCountLaw_limit
    M hM hQP lambda a b ha hab R J S hJ hJf hdis
  have he : θ = pointLawCellCounts a b R ν J S hJ :=
    tendsto_nhds_unique hθ.2.2 hsource
  rw [he] at hθ
  exact ⟨hθ.1, hθ.2.1⟩

/-- The same identity directly under the actual limiting point law,
with intrinsic integer point counts rather than an abstract count vector. -/
theorem actual_pointLaw_integral_mixed_counts (M : CompactBJRModel T)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (unmarkedWindowLaw M lambda a b R) atTop (𝓝 ν))
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (lo hi : D → ℝ) (hfront : ∀ i, frontier (J i) ⊆ {lo i, hi i})
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (q : D → ℕ) :
    Integrable (fun η ↦ factorialPolynomial q
      (fun i ↦ count η (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)))
        (ν : Measure (PointMeasure (SurplusWindow a b R))) ∧
    (∫ η, factorialPolynomial q
      (fun i ↦ count η (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))
        ∂(ν : Measure (PointMeasure (SurplusWindow a b R)))) =
      cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q := by
  obtain ⟨hint, hval⟩ := all_mixed_factorial_moments M hM hQP lambda a b ha hab R ν hν
    J S hJ hJf lo hi hfront hdis
  have hm := measurable_count_vector
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
  have hp : AEStronglyMeasurable (factorialPolynomial q)
      (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ)) :=
    (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
  have hI := hint q
  change Integrable (factorialPolynomial q)
    ((ν : Measure (PointMeasure (SurplusWindow a b R))).map
      (fun η i ↦ count η (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))) at hI
  refine ⟨(integrable_map_measure hp hm.aemeasurable).mp hI, ?_⟩
  calc
    _ = factorialMoment (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ)) q :=
      (integral_map hm.aemeasurable hp).symm
    _ = _ := hval q

/-- A genuine limiting point law, convergence, and all stated cell
factorial moments are obtained together from the actual compact model. -/
theorem exists_unique_pointLaw_limit_with_cellMoments (M : CompactBJRModel T)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (lo hi : D → ℝ) (hfront : ∀ i, frontier (J i) ⊆ {lo i, hi i})
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (unmarkedWindowLaw M lambda a b R) atTop (𝓝 ν) ∧
      (∀ q, Integrable (factorialPolynomial q)
        (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ))) ∧
      (∀ q, factorialMoment (pointLawCellCounts a b R ν J S hJ : Measure (D → ℕ)) q =
        cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q) := by
  obtain ⟨ν, hν, hunique⟩ := CompactWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
    M hM hQP lambda a b ha hab R
  exact ⟨ν, ⟨hν, all_mixed_factorial_moments M hM hQP lambda a b ha hab R ν hν
    J S hJ hJf lo hi hfront hdis⟩, fun θ hθ ↦ hunique θ hθ.1⟩

end PerronWright.CompactWindowLimitCellMoments
