import PerronWright.Probability.GraphWindowWeightedIntegral
import PerronWright.Probability.ComponentWindowMixedFactorials
import PerronWright.Probability.CompactSizeCellMomentBounds
import PerronWright.Probability.FiniteBooleanCellRefinement

/-! # Actual joint spatial cell laws from literal graph local formulas

All mixed moments are obtained from actual injective component tuples.
Disjoint cells give the density integrals; overlapping queries are first
split into disjoint Boolean atoms and then reconstructed. Thus neither a
target point law nor mixed moment identification is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowCellFactorials

open GraphWindowSource GraphWindowFactorialLimits GraphWindowWeightedIntegral
  ComponentWindowPointMeasures ComponentWindowMixedFactorials
  FinitePointMeasureCompact FinitePointMeasureMixedFactorials FactorialCountDeterminacy
  SizeCellIndicators CriticalWeightedFloorIntegral CriticalFloorWindow
  CompactWindowFactorialMoments FactorialDensity FinitePointMeasureMeasurable
open CompactSizeCellFactorialLimits (cellMomentMass cellMomentMass_zero)
open CompactSizeCellMomentBounds FactorialCountLimitExistence FiniteBooleanCellRefinement

variable {D : Type*} [Fintype D]
variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

theorem windowLaw_mixed_factorial_integrable (a b : ℝ) (R n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (fun η ↦ factorialPolynomial q (fun i ↦ count η (A i)))
      (windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable ρ a b R n (measurable_window_mixed_factorial a b R A q hAm)

theorem windowCountLaw_mixed_factorial_integrable (a b : ℝ) (R n : ℕ)
    (A : D → Set (SurplusWindow a b R)) (q : D → ℕ) (hAm : ∀ i, MeasurableSet (A i)) :
    Integrable (factorialPolynomial q) (countLaw
      (windowLaw ρ a b R n) A hAm : Measure (D → ℕ)) := by
  rw [countLaw_toMeasure]
  exact (integrable_map_measure (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    (measurable_count_vector A hAm).aemeasurable).mpr
      (windowLaw_mixed_factorial_integrable ρ a b R n A q hAm)

theorem windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum
    (a b : ℝ) (hb : 0 ≤ b) (R n : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ η, factorialPolynomial q (fun i ↦ count η
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i))
      ∂(windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices (n+1) a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) := by
  have hm := measurable_window_mixed_factorial a b R
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i) q
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))
  rw [windowLaw_integral ρ a b R n hm]
  simp_rw [window_sizeSurplus_mixed_factorial_eq_sum _ (Nat.succ_pos n) a b hb R J S q hJ hdis]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

def sizeSurplusCountLaw (a b : ℝ) (R n : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    ProbabilityMeasure (D → ℕ) :=
  countLaw (windowLaw ρ a b R n)
    (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

theorem sizeSurplusCountLaw_mixed_factorial_integrable
    (a b : ℝ) (R n : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ) :
    Integrable (factorialPolynomial q) (sizeSurplusCountLaw ρ a b R n J S hJ :
      Measure (D → ℕ)) :=
  windowCountLaw_mixed_factorial_integrable ρ a b R n _ q
    (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))

theorem sizeSurplusCountLaw_mixed_factorial_integral_eq_sum
    (a b : ℝ) (hb : 0 ≤ b) (R n : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ y, factorialPolynomial q y ∂(sizeSurplusCountLaw ρ a b R n J S hJ :
      Measure (D → ℕ))) =
      ∑ r ∈ cellSurplusIndices R S q, ∑ k ∈ cellSizeIndices (n+1) a b J q,
        (∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) := by
  unfold sizeSurplusCountLaw
  rw [countLaw_toMeasure,
    integral_map (measurable_count_vector _
      (fun i ↦ (measurable_windowEmbedding a b R)
        (measurableSet_sizeSurplusCells J S hJ i))).aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  exact windowLaw_sizeSurplus_mixed_factorial_expectation_eq_sum ρ a b hb R n J S q hJ hdis

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem filtered_integer_window_expectation_tendsto {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (q : D → ℕ)
    (hq : 0 < ∑ i, q i) (r : Fin (∑ i, q i) → ℕ)
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ cellSizeIndices (n+1) a b J q,
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) atTop
      (𝓝 (∫ x in sizeWindow (∑ i, q i) a b,
        cellWeight (fun j ↦ J (label q j)) x * density alpha beta lambda x r)) := by
  have ht := weighted_integer_window_expectation_tendsto ρ hbeta hlocal hq r ha hab
    (cellWeight (fun j ↦ J (label q j))) 1 (by norm_num)
    (cellWeight_norm_le _) (ae_continuousAt_cellWeight _ (fun j ↦ hJf (label q j)))
  apply ht.congr'
  filter_upwards [] with n
  have hh : 0 < ((n+1 : ℕ) : ℝ)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
  unfold cellSizeIndices
  rw [integerWindow_eq_indices hh (ha.le.trans hab),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [cellWeight_eq]
  by_cases hk : ∀ j, (normalizedInteger (n+1) k) j ∈ J (label q j)
  · have hk' : ∀ j, (k j : ℝ)/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) ∈ J (label q j) := hk
    simp only [if_pos hk,if_pos hk',one_mul]
  · have hk' : ¬∀ j, (k j : ℝ)/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) ∈ J (label q j) := hk
    simp only [if_neg hk,if_neg hk',zero_mul]

theorem sizeSurplusCountLaw_mixed_factorial_tendsto {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (q : D → ℕ) (hq : 0 < ∑ i, q i) :
    Tendsto (fun n ↦ factorialMoment
      (sizeSurplusCountLaw ρ a b R n J S hJ : Measure (D → ℕ)) q) atTop
      (𝓝 (cellMomentMass alpha beta lambda a b R J S q)) := by
  have ht : Tendsto (fun n : ℕ ↦ ∑ r ∈ cellSurplusIndices R S q,
      ∑ k ∈ cellSizeIndices (n+1) a b J q,
        ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) atTop
      (𝓝 (cellMomentMass alpha beta lambda a b R J S q)) :=
    tendsto_finsetSum _ (fun r _ ↦ filtered_integer_window_expectation_tendsto ρ hbeta hlocal
      ha hab J q hq r hJf)
  apply ht.congr'
  filter_upwards [] with n
  exact (sizeSurplusCountLaw_mixed_factorial_integral_eq_sum ρ a b (ha.le.trans hab)
    R n J S hJ q hdis).symm

theorem sizeSurplusCountLaw_all_mixed_factorials_tendsto {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (q : D → ℕ) :
    Tendsto (fun n ↦ factorialMoment
      (sizeSurplusCountLaw ρ a b R n J S hJ : Measure (D → ℕ)) q) atTop
      (𝓝 (cellMomentMass alpha beta lambda a b R J S q)) := by
  by_cases hq : 0 < ∑ i, q i
  · exact sizeSurplusCountLaw_mixed_factorial_tendsto ρ hbeta hlocal ha hab R
      J S hJ hJf hdis q hq
  · have hzero : q = fun _ ↦ 0 := by
      funext i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ Nat.zero_le (q j))
        (Finset.mem_univ i)
      omega
    subst q
    simpa only [factorialMoment,factorialPolynomial,Nat.descFactorial_zero,Nat.cast_one,
      Finset.prod_const_one,integral_const,probReal_univ,smul_eq_mul,mul_one,
      cellMomentMass_zero _ _ _ _ _ hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))

theorem exists_unique_actual_jointCellCountLaw_limit {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    ∃! ν : ProbabilityMeasure (D → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (D → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (D → ℕ)) q =
        cellMomentMass alpha beta lambda a b R J S q) ∧
      Tendsto (fun n ↦ sizeSurplusCountLaw ρ a b R n J S hJ) atTop (𝓝 ν) :=
  exists_unique_limit_of_factorialMoments
    (fun n ↦ sizeSurplusCountLaw ρ a b R n J S hJ)
    (fun n q ↦ sizeSurplusCountLaw_mixed_factorial_integrable ρ a b R n J S hJ q)
    (fun q ↦ cellMomentMass alpha beta lambda a b R J S q)
    (fun q ↦ sizeSurplusCountLaw_all_mixed_factorials_tendsto ρ hbeta hlocal ha hab R
      J S hJ hJf hdis q)
    (summable_cellMomentMass_factorial _ _ hbeta ha hab R J S hJ)

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem continuous_reconstruct (S : D → Finset ℕ) (R : ℕ) :
    Continuous (reconstruct S R) := continuous_of_discreteTopology

theorem actualQueryLaw_eq_map_atomLaw (a b : ℝ) (R n : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    sizeSurplusCountLaw ρ a b R n J S hJ =
      (sizeSurplusCountLaw ρ a b R n (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1)).map
          (continuous_reconstruct S R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [sizeSurplusCountLaw,countLaw_toMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_reconstruct S R).measurable
    (measurable_count_vector _ (fun k ↦ (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)))]
  congr 1
  funext η
  exact countVector_eq_reconstruct J S hJ a b R η

theorem exists_unique_actual_overlappingCellCountLaw_limit {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) :
    ∃! ν : ProbabilityMeasure (D → ℕ),
      Tendsto (fun n ↦ sizeSurplusCountLaw ρ a b R n J S hJ) atTop (𝓝 ν) := by
  obtain ⟨μ,hμ,_⟩ := exists_unique_actual_jointCellCountLaw_limit ρ hbeta hlocal ha hab R
    (atomSizes J R) (atomSurpluses D R) (fun k ↦ measurableSet_sizeAtom J hJ k.1)
    (fun k ↦ volume_frontier_sizeAtom J hJf k.1) (atomCells_disjoint J R)
  let ν := μ.map (continuous_reconstruct S R).measurable.aemeasurable
  have ht : Tendsto (fun n ↦ sizeSurplusCountLaw ρ a b R n J S hJ) atTop (𝓝 ν) := by
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ μ hμ.2.2
      (continuous_reconstruct S R)
    simpa only [← actualQueryLaw_eq_map_atomLaw ρ a b R _ J S hJ] using hm
  exact ⟨ν,ht,fun η hη ↦ tendsto_nhds_unique hη ht⟩

end PerronWright.GraphWindowCellFactorials
