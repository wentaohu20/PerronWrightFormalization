import PerronWright.Probability.BrownianWindowCellTupleGeometry
import PerronWright.Probability.BrownianActualFactorialDensity
import PerronWright.Probability.CompactSizeCellMomentBounds

/-! # Literal density moments of the actual canonical Brownian window law

Arbitrary disjoint Borel spatial cells are evaluated under the already
constructed Brownian size--surplus law. Actual labelled tuples, genuine
conditional Poisson weights, and the proved all-order density supply the
moments; finite integrability and the summable moment series follow from
the existing numerical density bounds. No density or identity premise is
introduced, and no condition on cell boundaries is needed here.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianActualWindowCellMoments

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianFullHorizonMarkJointLaw BrownianFullHorizonPoissonMarks BrownianFullHorizonExcursionAreas
open BrownianExcursionWindowPointMeasure BrownianExcursionPointProcessLaw
open BrownianExcursionTupleTests BrownianExcursionDeletionTupleSource
open BrownianActualFactorialDensity BrownianWindowCellTupleGeometry
open ComponentGlobalPointProcess ComponentWindowMixedFactorials
open ComponentWindowPointMeasures PositiveSizeSurplusExhaustion GlobalPointMeasureCharts
open FinitePointMeasureCompact FinitePointMeasureMixedFactorials FactorialCountDeterminacy
open SizeCellIndicators CompactSizeCellFactorialLimits CompactSizeCellMomentBounds
open ComponentWindowFactorialCounts FactorialDensity

variable {D : Type*} [Fintype D]

private theorem tuple_test_density (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (q : D → ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (r : Fin (∑ i, q i) → ℕ) :
    (∫⁻ p, statistic lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
      (fun z ↦ ENNReal.ofReal
        (cellWeight (fun j ↦ J (label q j)) (fun j ↦ (z j).1.val))) p
      ∂pathJointLaw lambda) =
      ENNReal.ofReal (∫ x in sizeWindow (∑ i, q i) (lower m) (upper m),
        cellWeight (fun j ↦ J (label q j)) x * density 1 1 lambda x r) := by
  let B := sizeWindow (∑ i, q i) (lower m) (upper m)
  let H : (Fin (∑ i, q i) → ℝ) → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal (cellWeight (fun j ↦ J (label q j)) x)
  have hB : MeasurableSet B := measurableSet_Icc
  have hH : Measurable H := (measurable_cellWeight _ (fun j ↦ hJ (label q j))).ennreal_ofReal
  have hΨ : Measurable (fun z : Fin (∑ i, q i) → PositiveSizeSurplus ↦
      H (fun j ↦ (z j).1.val)) :=
    hH.comp (measurable_pi_lambda _ (fun j ↦
      measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j))))
  have hs (f : Path) : sourceSum lambda r (B.indicator H) f =
      ∑' e : Fin (∑ i, q i) → ℚ,
        weight lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r
          (fun z ↦ H (fun j ↦ (z j).1.val)) e f := by
    change (∑' e : Fin (∑ i, q i) → ℚ,
      if Function.Injective e ∧ ∀ j, Representative (driftedReflectionPath lambda f) (e j)
      then B.indicator H (fun j ↦ lengthValue lambda (e j) f) *
        ∏ j, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e j : ℝ) lambda f) (r j) else 0) = _
    apply tsum_congr
    intro e
    rw [weight_eq_complete_area]
    by_cases hg : Function.Injective e ∧
        ∀ j, Representative (driftedReflectionPath lambda f) (e j)
    · by_cases hb : (fun j ↦ lengthValue lambda (e j) f) ∈ B
      · have he : BrownianExcursionTuplePoissonWeights.sourceEvent lambda
            (fun _ ↦ lower m) (fun _ ↦ upper m) e f :=
          ⟨hg.1,fun j ↦ ⟨hg.2 j,(mem_sizeWindow.mp hb) j⟩⟩
        have hp (j) : 0 < lengthValue lambda (e j) f :=
          (lower_pos m).trans_le ((mem_sizeWindow.mp hb) j).1
        have hv := funext (markedTuple_size lambda r e f hp)
        rw [if_pos hg,indicator_of_mem hb,if_pos he,hv,mul_comm]
      · have he : ¬ BrownianExcursionTuplePoissonWeights.sourceEvent lambda
            (fun _ ↦ lower m) (fun _ ↦ upper m) e f :=
          fun he ↦ hb (mem_sizeWindow.mpr (fun j ↦ (he.2 j).2))
        rw [if_pos hg,indicator_of_notMem hb,if_neg he,zero_mul]
    · have he : ¬ BrownianExcursionTuplePoissonWeights.sourceEvent lambda
          (fun _ ↦ lower m) (fun _ ↦ upper m) e f :=
        fun he ↦ hg ⟨he.1,fun j ↦ (he.2 j).1⟩
      rw [if_neg hg,if_neg he]
  rw [joint_expectation_eq_source_weights lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r _ hΨ,
    ← lintegral_congr hs,actual_ordered_source_factorial_density lambda r _ (hH.indicator hB)]
  have he : (∫⁻ x in {x : Fin (∑ i, q i) → ℝ | ∀ j, 0 < x j},
      ENNReal.ofReal (density 1 1 lambda x r) * B.indicator H x) =
      ∫⁻ x in B, ENNReal.ofReal (density 1 1 lambda x r) * H x := by
    have hP : MeasurableSet {x : Fin (∑ i, q i) → ℝ | ∀ j, 0 < x j} := by
      apply Measurable.setOf
      exact Measurable.forall (fun j ↦ measurableSet_setOfPred.mp
        (measurableSet_lt measurable_const (measurable_pi_apply j)))
    rw [← lintegral_indicator hP,← lintegral_indicator hB]
    apply lintegral_congr
    intro x
    by_cases hb : x ∈ B
    · have hp : ∀ j, 0 < x j := fun j ↦ (lower_pos m).trans_le ((mem_sizeWindow.mp hb) j).1
      rw [indicator_of_mem (show x ∈ {x : Fin (∑ i, q i) → ℝ | ∀ j, 0 < x j} from hp),
        indicator_of_mem hb,indicator_of_mem hb]
    · by_cases hp : ∀ j, 0 < x j
      · rw [indicator_of_mem (show x ∈ {x : Fin (∑ i, q i) → ℝ | ∀ j, 0 < x j} from hp),
          indicator_of_notMem hb,indicator_of_notMem hb,mul_zero]
      · rw [indicator_of_notMem (show x ∉ {x : Fin (∑ i, q i) → ℝ | ∀ j, 0 < x j} from hp),
          indicator_of_notMem hb]
  rw [he]
  have hI := weighted_density_integrableOn 1 1 lambda (b := upper m) (lower_pos m)
    (fun j ↦ J (label q j)) (fun j ↦ hJ (label q j)) r
  have hn : ∀ᵐ x ∂volume.restrict B,
      0 ≤ cellWeight (fun j ↦ J (label q j)) x * density 1 1 lambda x r := by
    filter_upwards [ae_restrict_mem hB] with x hx
    exact mul_nonneg (cellWeight_nonneg _ _)
      (density_pos 1 lambda (by norm_num) x r
        (fun j ↦ (lower_pos m).trans_le ((mem_sizeWindow.mp hx) j).1)).le
  rw [ofReal_integral_eq_lintegral_ofReal hI hn]
  apply lintegral_congr
  intro x
  dsimp [H]
  rw [ENNReal.ofReal_mul (cellWeight_nonneg _ _),mul_comm]

/-- Every mixed descending factorial under the actual Brownian canonical
window equals the literal Perron--Wright cell density integral. -/
theorem windowLaw_mixed_factorial_lintegral (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫⁻ η, ENNReal.ofReal (mixedStatistic m J S q η)
      ∂(BrownianExcursionPointProcessLaw.windowLaw lambda m : Measure (Chart m))) =
      ENNReal.ofReal (cellMomentMass 1 1 lambda (lower m) (upper m) m J S q) := by
  have hΨ : Measurable (fun z : Fin (∑ i, q i) → PositiveSizeSurplus ↦
      ENNReal.ofReal (cellWeight (fun j ↦ J (label q j)) (fun j ↦ (z j).1.val))) :=
    ((measurable_cellWeight _ (fun j ↦ hJ (label q j))).comp
      (measurable_pi_lambda _ (fun j ↦
        measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j))))).ennreal_ofReal
  change (∫⁻ η, ENNReal.ofReal (mixedStatistic m J S q η)
    ∂(pathJointLaw lambda).map
      (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m ∘ pathInput)) = _
  rw [lintegral_map (measurable_mixedStatistic m J S q hJ).ennreal_ofReal
    ((BrownianExcursionWindowPointMeasure.measurable_windowPointMeasure lambda m).comp measurable_pathInput)]
  simp only [Function.comp_apply]
  rw [lintegral_congr_ae (ae_window_mixedStatistic_eq_statistic_sum lambda m J S q hJ hdis),
    lintegral_finsetSum _ (fun r _ ↦
      measurable_statistic lambda (fun _ ↦ lower m) (fun _ ↦ upper m) r _ hΨ)]
  simp_rw [tuple_test_density lambda m J q hJ]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro r _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (s := sizeWindow (∑ i, q i) (lower m) (upper m))
    measurableSet_Icc] with x hx
  exact mul_nonneg (cellWeight_nonneg _ _)
    (density_pos 1 lambda (by norm_num) x r
      (fun j ↦ (lower_pos m).trans_le ((mem_sizeWindow.mp hx) j).1)).le

theorem windowLaw_mixed_factorial_integrable (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Integrable (mixedStatistic m J S q)
      (BrownianExcursionPointProcessLaw.windowLaw lambda m : Measure (Chart m)) := by
  refine ⟨(measurable_mixedStatistic m J S q hJ).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (mixedStatistic_nonneg m J S q)),
    windowLaw_mixed_factorial_lintegral lambda m J S q hJ hdis]
  exact ENNReal.ofReal_lt_top

theorem windowLaw_mixed_factorial_integral (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ)
    (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∫ η, mixedStatistic m J S q η
      ∂(BrownianExcursionPointProcessLaw.windowLaw lambda m : Measure (Chart m))) =
      cellMomentMass 1 1 lambda (lower m) (upper m) m J S q := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (mixedStatistic_nonneg m J S q))
    (cellMomentMass_nonneg 1 lambda _ _ (by norm_num) (lower_pos m) m J S q)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (windowLaw_mixed_factorial_integrable lambda m J S q hJ hdis)
    (Eventually.of_forall (mixedStatistic_nonneg m J S q))]
  exact windowLaw_mixed_factorial_lintegral lambda m J S q hJ hdis

theorem cellMomentMass_zero_order (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) :
    cellMomentMass 1 1 lambda (lower m) (upper m) m J S (fun _ ↦ 0) = 1 :=
  cellMomentMass_zero 1 1 lambda _ _ (lower_le_upper m) m J S

theorem summable_cell_mixed_factorial_moments (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      cellMomentMass 1 1 lambda (lower m) (upper m) m J S q /
        ∏ i, ((q i).factorial : ℝ)) :=
  summable_cellMomentMass_factorial 1 lambda (by norm_num) (lower_pos m) (lower_le_upper m)
    m J S hJ

/-- The literal cell-count pushforward of the actual Brownian window. -/
def cellCountLaw (lambda : ℝ) (m : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) : ProbabilityMeasure (D → ℕ) :=
  FinitePointMeasureMeasurable.countLaw (BrownianExcursionPointProcessLaw.windowLaw lambda m)
    (fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells J S hJ i))

theorem all_mixed_factorial_moments (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    (∀ q, Integrable (factorialPolynomial q)
      (cellCountLaw lambda m J S hJ : Measure (D → ℕ))) ∧
    (∀ q, factorialMoment (cellCountLaw lambda m J S hJ : Measure (D → ℕ)) q =
      cellMomentMass 1 1 lambda (lower m) (upper m) m J S q) := by
  have hm := FinitePointMeasureMeasurable.measurable_count_vector
    (fun i ↦ windowEmbedding (lower m) (upper m) m ⁻¹' sizeSurplusCells J S i)
    (fun i ↦ (measurable_windowEmbedding _ _ _) (measurableSet_sizeSurplusCells J S hJ i))
  constructor
  · intro q
    change Integrable (factorialPolynomial q)
      ((BrownianExcursionPointProcessLaw.windowLaw lambda m : Measure (Chart m)).map _)
    exact (integrable_map_measure
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable hm.aemeasurable).mpr
      (windowLaw_mixed_factorial_integrable lambda m J S q hJ hdis)
  · intro q
    change (∫ n, factorialPolynomial q n
      ∂(BrownianExcursionPointProcessLaw.windowLaw lambda m : Measure (Chart m)).map _) = _
    rw [integral_map hm.aemeasurable
      (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
    exact windowLaw_mixed_factorial_integral lambda m J S q hJ hdis

theorem summable_actual_cell_factorial_moments (lambda : ℝ) (m : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j))) :
    Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      factorialMoment (cellCountLaw lambda m J S hJ : Measure (D → ℕ)) q /
        ∏ i, ((q i).factorial : ℝ)) := by
  simp_rw [(all_mixed_factorial_moments lambda m J S hJ hdis).2]
  exact summable_cell_mixed_factorial_moments lambda m J S hJ

end PerronWright.BrownianActualWindowCellMoments
