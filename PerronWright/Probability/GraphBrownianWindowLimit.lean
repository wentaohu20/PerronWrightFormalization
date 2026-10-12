import PerronWright.Probability.GraphWindowSpatialLimit
import PerronWright.Probability.BrownianInverseWindowLaw
import PerronWright.Probability.BrownianActualArbitraryWindowCellMoments
import PerronWright.Probability.FactorialCellMomentRescaling
import PerronWright.Probability.FactorialCountConvergenceCriterion

/-!
# Actual graph windows converge to the actual Brownian window law

The Brownian count moments are proved from the literal full-excursion
process. Actual inverse size dilation matches the original local density.
The target-only factorial series criterion then identifies disjoint
counts, Boolean refinement restores overlapping queries, and the proved
rational count generators identify the whole weak-Borel window law.
-/

open MeasureTheory Filter Topology Set
open scoped Classical BigOperators Real
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphBrownianWindowLimit

open GraphWindowSource GraphWindowFactorialLimits GraphWindowCellFactorials
open FinitePointMeasureCompact FinitePointMeasureMeasurable ComponentWindowPointMeasures
open ComponentWindowMixedFactorials FactorialCountDeterminacy
open CompactSizeCellFactorialLimits CompactSizeCellMomentBounds
open FactorialCountConvergenceCriterion FiniteBooleanCellRefinement
open InverseWindowSizeRescaling

variable {D : Type*} [Fintype D]

omit [Fintype D] in
private theorem scaled_cells_disjoint (J : D → Set ℝ) (S : D → Finset ℕ) (c : ℝ)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Pairwise (fun i j ↦ Disjoint
      (sizeSurplusCells (fun k ↦ (fun x : ℝ ↦ x/c) ⁻¹' J k) S i)
      (sizeSurplusCells (fun k ↦ (fun x : ℝ ↦ x/c) ⁻¹' J k) S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ⟨x,r⟩ hi hj
  have hi' : (x/c,r) ∈ sizeSurplusCells J S i := hi
  have hj' : (x/c,r) ∈ sizeSurplusCells J S j := hj
  exact Set.disjoint_left.mp (hdis hij) hi' hj'

private theorem target_countLaw_eq_standard (alpha lambda a b : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (R : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    countLaw (BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
      (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab)
      (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)) =
      BrownianActualArbitraryWindowCellMoments.cellCountLaw
        (alpha*beta^(-2/3 : ℝ)*lambda) (beta^(1/3 : ℝ)*a) (beta^(1/3 : ℝ)*b) R
        (mul_pos (Real.rpow_pos_of_pos hbeta _) ha)
        (mul_le_mul_of_nonneg_left hab (Real.rpow_pos_of_pos hbeta _).le)
        (fun i ↦ (fun x : ℝ ↦ x/beta^(1/3 : ℝ)) ⁻¹' J i) S
        (fun i ↦ (measurable_id.div_const _) (hJ i)) := by
  unfold BrownianInverseWindowLaw.law
  rw [countLaw_map_inverseWindowScaleMap a b R (Real.rpow_pos_of_pos hbeta _) J S hJ]
  rfl

private theorem actual_target_moments (alpha lambda a b : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (R : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    let ν := countLaw (BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
      (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab)
      (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
    (∀ q, Integrable (factorialPolynomial q) (ν : Measure (D → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (D → ℕ)) q =
        cellMomentMass alpha beta lambda a b R J S q) := by
  dsimp only
  rw [target_countLaw_eq_standard alpha lambda a b hbeta R ha hab J S hJ]
  have hm := BrownianActualArbitraryWindowCellMoments.all_mixed_factorial_moments
    (alpha*beta^(-2/3 : ℝ)*lambda) (beta^(1/3 : ℝ)*a) (beta^(1/3 : ℝ)*b) R
    (mul_pos (Real.rpow_pos_of_pos hbeta _) ha)
    (mul_le_mul_of_nonneg_left hab (Real.rpow_pos_of_pos hbeta _).le)
    (fun i ↦ (fun x : ℝ ↦ x/beta^(1/3 : ℝ)) ⁻¹' J i) S
    (fun i ↦ (measurable_id.div_const _) (hJ i))
    (scaled_cells_disjoint J S _ hdis)
  refine ⟨hm.1, fun q ↦ ?_⟩
  rw [hm.2]
  exact (FactorialCellMomentRescaling.cellMomentMass_starred_normalization
    alpha lambda a b hbeta ha R J S q).symm

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

theorem disjoint_countLaw_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Tendsto (fun n ↦ GraphWindowCellFactorials.sizeSurplusCountLaw ρ a b R n J S hJ) atTop
      (𝓝 (countLaw (BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab)
        (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
        (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)))) := by
  have hm := actual_target_moments alpha lambda a b hbeta R ha hab J S hJ hdis
  apply weak_tendsto_of_factorialMoments_of_target_series _ _
    (fun n q ↦ GraphWindowCellFactorials.sizeSurplusCountLaw_mixed_factorial_integrable
      ρ a b R n J S hJ q) hm.1
  · intro q
    rw [hm.2]
    exact sizeSurplusCountLaw_all_mixed_factorials_tendsto ρ hbeta hlocal ha hab R J S hJ hJf hdis q
  · simp_rw [hm.2]
    exact summable_cellMomentMass_factorial alpha lambda hbeta ha hab R J S hJ

private theorem queryLaw_eq_map_atomLaw (a b : ℝ) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)) =
      (countLaw ν
        (fun k ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells (atomSizes J R) (atomSurpluses D R) k)
        (fun k ↦ (measurable_windowEmbedding a b R)
          (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
            (fun k ↦ measurableSet_sizeAtom J hJ k.1) k))).map
          (GraphWindowCellFactorials.continuous_reconstruct S R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [countLaw_toMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (GraphWindowCellFactorials.continuous_reconstruct S R).measurable
    (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)))]
  congr 1
  funext η
  exact countVector_eq_reconstruct J S hJ a b R η

theorem overlapping_countLaw_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) :
    Tendsto (fun n ↦ GraphWindowCellFactorials.sizeSurplusCountLaw ρ a b R n J S hJ) atTop
      (𝓝 (countLaw (BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab)
        (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
        (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)))) := by
  have ht := disjoint_countLaw_tendsto ρ hbeta hlocal ha hab R
    (atomSizes J R) (atomSurpluses D R) (fun k ↦ measurableSet_sizeAtom J hJ k.1)
    (fun k ↦ volume_frontier_sizeAtom J hJf k.1) (atomCells_disjoint J R)
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ ht
    (GraphWindowCellFactorials.continuous_reconstruct S R)
  simpa only [← actualQueryLaw_eq_map_atomLaw ρ a b R _ J S hJ,
    ← queryLaw_eq_map_atomLaw a b R J S hJ] using hm

theorem windowLaw_tendsto_actual_Brownian {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (GraphWindowSource.windowLaw ρ a b R) atTop
      (𝓝 (BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab)) := by
  obtain ⟨ν, hν, _⟩ := GraphWindowSpatialLimit.exists_unique_windowLaw_limit
    ρ hbeta hlocal ha hab R
  have he : ν = BrownianInverseWindowLaw.law (alpha*beta^(-2/3 : ℝ)*lambda) a b R
      (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab := by
    apply WindowCountGenerators.probabilityMeasure_eq_of_finite_cell_countLaws a b R hab
    intro I
    let J : I → Set ℝ := fun i ↦ WindowCountGenerators.sizeCell R i.val
    let S : I → Finset ℕ := fun i ↦ WindowCountGenerators.surplusCell R i.val
    have hJ (i : I) : MeasurableSet (J i) := WindowCountGenerators.measurableSet_sizeCell R i.val
    have hJf (i : I) : (volume : Measure ℝ) (frontier (J i)) = 0 :=
      WindowCountGenerators.volume_frontier_sizeCell R i.val
    have hactual := overlapping_countLaw_tendsto ρ hbeta hlocal ha hab R J S hJ hJf
    have hlimit := GraphWindowSpatialLimit.generator_finiteCountLaw_tendsto
      ρ hbeta hlocal ha hab R id tendsto_id ν (by simpa only [id_eq] using hν) I
    apply tendsto_nhds_unique hlimit
    simpa only [id_eq, GraphWindowCellFactorials.sizeSurplusCountLaw,
      sizeSurplusCells, WindowCountGenerators.cell, J, S] using hactual
  simpa only [he] using hν

end PerronWright.GraphBrownianWindowLimit
