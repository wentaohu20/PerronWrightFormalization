import PerronWright.Probability.BrownianExcursionTuplePoissonWeights
import PerronWright.Probability.BrownianExcursionCompactWindows
import PerronWright.Probability.FinitePointMeasureMeasurable

/-!
# Exact Campbell weights for actual full-excursion point-process windows

The actual finite point-process mass in a positive size interval at a
fixed surplus equals the literal full representative count. Its first
extended moment is the Brownian-source sum of genuine Poisson full-area
probabilities. No finite first moment or Brownian intensity is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionCampbellWeights

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure
open BrownianExcursionPointProcessLaw BrownianFullHorizonPoissonMarks
open BrownianFullHorizonExcursionAreas ComponentGlobalPointProcess
open BrownianExcursionTuplePoissonWeights (poissonWeight)
open FinitePointMeasureCompact

def cell (a b : ℝ) (r : ℕ) : Set PositiveSizeSurplus :=
  positiveWindowSet a b r ∩ {z | z.2 = r}

theorem measurableSet_cell (a b : ℝ) (r : ℕ) : MeasurableSet (cell a b r) :=
  (measurableSet_positiveWindowSet a b r).inter (measurableSet_eq_fun measurable_snd measurable_const)

theorem isCompact_cell (a b : ℝ) (r : ℕ) (ha : 0 < a) : IsCompact (cell a b r) :=
  (isCompact_positiveWindowSet a b r ha).inter_right (isClosed_eq continuous_snd continuous_const)

def sourceEvent (lambda a b : ℝ) (q : ℚ) (f : Path) : Prop :=
  Representative (driftedReflectionPath lambda f) q ∧ lengthValue lambda q f ∈ Icc a b

theorem measurable_sourceEvent (lambda a b : ℝ) (q : ℚ) : Measurable (sourceEvent lambda a b q) :=
  measurableSet_setOfPred.mp (((measurableSet_representative q).preimage
    (measurable_driftedReflectionPath lambda)).inter ((measurable_lengthValue lambda q) measurableSet_Icc))

def contribution (lambda a b : ℝ) (r : ℕ) (q : ℚ) (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  if sourceEvent lambda a b q p.1 ∧ rationalCount p.2 q = r then 1 else 0

theorem measurable_contribution (lambda a b : ℝ) (r : ℕ) (q : ℚ) :
    Measurable (contribution lambda a b r q) :=
  Measurable.ite (((measurable_sourceEvent lambda a b q).comp measurable_fst).and
    (((measurable_pi_apply (Encodable.encode q)).comp measurable_snd).eq measurable_const)).setOf
      measurable_const measurable_const

def weight (lambda a b : ℝ) (r : ℕ) (q : ℚ) (f : Path) : ℝ≥0∞ :=
  if sourceEvent lambda a b q f then poissonWeight (excursionArea (q : ℝ) lambda f) r else 0

theorem measurable_weight (lambda a b : ℝ) (r : ℕ) (q : ℚ) :
    Measurable (weight lambda a b r q) :=
  Measurable.ite (measurable_sourceEvent lambda a b q).setOf
    ((BrownianExcursionTuplePoissonWeights.measurable_poissonWeight r).comp
      (measurable_excursionArea (q : ℝ) lambda)) measurable_const

theorem conditional_contribution (lambda a b : ℝ) (r : ℕ) (q : ℚ) (f : Path) :
    (∫⁻ m, contribution lambda a b r q (f,m) ∂markLaw lambda f) = weight lambda a b r q f := by
  by_cases hs : sourceEvent lambda a b q f
  · let A : Set (ℕ → ℕ) := {m | rationalCount m q = r}
    have hA : MeasurableSet A := (measurable_pi_apply (Encodable.encode q)).eq measurable_const |>.setOf
    have hc : (fun m ↦ contribution lambda a b r q (f,m)) = A.indicator 1 := by
      funext m
      simp [contribution,A,hs,Set.indicator_apply]
    rw [hc,lintegral_indicator_one hA]
    have he := (markLaw_hasLaw_rationalCount lambda f q).measure_eq (measurableSet_singleton r)
    have hr : markLaw lambda f A = poissonMeasure (retainedArea q lambda f) {r} := by
      convert he using 1 <;> congr 1
    rw [hr,poissonMeasure_singleton,retainedArea,if_pos hs.1]
    exact (if_pos hs).symm
  · simp [contribution,weight,hs]

def statistic (lambda a b : ℝ) (r : ℕ) (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  ∑' q : ℚ, contribution lambda a b r q p

theorem measurable_statistic (lambda a b : ℝ) (r : ℕ) : Measurable (statistic lambda a b r) :=
  Measurable.tsum (fun q ↦ measurable_contribution lambda a b r q)

theorem conditional_statistic (lambda a b : ℝ) (r : ℕ) (f : Path) :
    (∫⁻ m, statistic lambda a b r (f,m) ∂markLaw lambda f) = ∑' q : ℚ, weight lambda a b r q f := by
  change (∫⁻ m, ∑' q : ℚ, contribution lambda a b r q (f,m) ∂markLaw lambda f) = _
  rw [lintegral_tsum]
  · exact tsum_congr (fun q ↦ conditional_contribution lambda a b r q f)
  · intro q
    exact ((measurable_contribution lambda a b r q).comp (measurable_const.prodMk measurable_id)).aemeasurable

theorem joint_expectation_eq_source_weights (lambda a b : ℝ) (r : ℕ) :
    (∫⁻ p, statistic lambda a b r p ∂pathJointLaw lambda) =
      ∫⁻ f, ∑' q : ℚ, weight lambda a b r q f ∂pathLaw := by
  rw [pathJointLaw,CountablePoissonKernel.jointLaw,Measure.lintegral_compProd (measurable_statistic lambda a b r)]
  apply lintegral_congr
  intro f
  exact conditional_statistic lambda a b r f

/-- First factorial statistic of the genuine global point process,
with no finite-moment assumption. -/
theorem process_cell_eq_statistic (lambda a b : ℝ) (r : ℕ) (ha : 0 < a)
    (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1) :
    (process lambda (pathInput p) : Measure PositiveSizeSurplus) (cell a b r) =
      statistic lambda a b r p := by
  change BrownianExcursionAtomicMeasure.measure lambda (pathInput p) (cell a b r) = _
  rw [BrownianExcursionAtomicMeasure.measure,Measure.sum_apply _ (measurableSet_cell a b r)]
  apply tsum_congr
  intro q
  by_cases hr : Representative (driftedReflectionPath lambda p.1) q
  · by_cases hp : 0 < lengthValue lambda q p.1
    · by_cases hb : lengthValue lambda q p.1 ∈ Icc a b
      · by_cases hm : rationalCount p.2 q = r <;>
          simp [active,pathInput,hg,hr,hp,
            cell,positiveWindowSet,ambientEmbedding,ComponentWindowPointMeasures.windowSet,
            atom,positiveSize,sourceEvent,contribution,hb,hm]
      · simp [active,pathInput,hg,hr,hp,
          cell,positiveWindowSet,ambientEmbedding,ComponentWindowPointMeasures.windowSet,
          atom,positiveSize,sourceEvent,contribution,hb]
    · have hb : ¬ lengthValue lambda q p.1 ∈ Icc a b := fun h ↦ hp (ha.trans_le h.1)
      simp [active,pathInput,hg,hp,sourceEvent,contribution,hb]
  · simp [active,pathInput,hr,sourceEvent,contribution]

theorem ae_process_cell_eq_statistic (lambda a b : ℝ) (r : ℕ) (ha : 0 < a) :
    ∀ᵐ p ∂pathJointLaw lambda,
      (process lambda (pathInput p) : Measure PositiveSizeSurplus) (cell a b r) = statistic lambda a b r p := by
  have hg : ∀ᵐ p ∂pathJointLaw lambda, Good lambda p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [pathJointLaw_source]
    exact ae_good lambda
  exact hg.mono (fun p hp ↦ process_cell_eq_statistic lambda a b r ha p hp)

/-- The actual compact weak-Borel window law's first extended moment is
exactly the complete Brownian excursion area-weighted Campbell sum. -/
theorem windowLaw_campbell_formula (lambda a b : ℝ) (r : ℕ) (ha : 0 < a) :
    (∫⁻ η : PointMeasure PositiveSizeSurplus,
      ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) univ
      ∂(BrownianExcursionCompactWindows.law lambda (cell a b r) (isCompact_cell a b r ha) : Measure _)) =
      ∫⁻ f, ∑' q : ℚ, weight lambda a b r q f ∂pathLaw := by
  change (∫⁻ η : PointMeasure PositiveSizeSurplus,
    ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) univ
    ∂((pathJointLaw lambda).map (BrownianExcursionCompactWindows.window lambda (cell a b r) ∘ pathInput))) = _
  rw [lintegral_map (FinitePointMeasureMeasurable.measurable_eval MeasurableSet.univ)
    ((BrownianExcursionCompactWindows.measurable_window lambda (cell a b r)
      (measurableSet_cell a b r)).comp measurable_pathInput)]
  calc
    _ = ∫⁻ p, statistic lambda a b r p ∂pathJointLaw lambda := by
      apply lintegral_congr_ae
      filter_upwards [ae_process_cell_eq_statistic lambda a b r ha] with p hp
      have he := congrArg (fun μ : Measure PositiveSizeSurplus ↦ μ univ)
        (BrownianExcursionCompactWindows.window_eq_restrict_process lambda (cell a b r)
          (isCompact_cell a b r ha) (pathInput p))
      rw [Measure.restrict_apply MeasurableSet.univ,univ_inter] at he
      exact he.trans hp
    _ = _ := joint_expectation_eq_source_weights lambda a b r

theorem windowLaw_campbell_formula_original_source (lambda a b : ℝ) (r : ℕ) (ha : 0 < a) :
    (∫⁻ η : PointMeasure PositiveSizeSurplus,
      ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) univ
      ∂(BrownianExcursionCompactWindows.law lambda (cell a b r) (isCompact_cell a b r ha) : Measure _)) =
      ∫⁻ x, ∑' q : ℚ, weight lambda a b r q (measurablePath x)
        ∂BrownianGaussianSkeleton.rationalLaw := by
  rw [windowLaw_campbell_formula lambda a b r ha,pathLaw,
    lintegral_map (Measurable.tsum (fun q ↦ measurable_weight lambda a b r q)) measurable_measurablePath]

end PerronWright.BrownianExcursionCampbellWeights
