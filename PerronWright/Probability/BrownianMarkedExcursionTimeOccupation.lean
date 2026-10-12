import PerronWright.Probability.BrownianExcursionOccupationCampbell
import PerronWright.Probability.BrownianExcursionCampbellWeights

/-! # Actual marked-window moments as inverse-length time occupation

The mark is the literal Poisson probability of the reflected area between
the actual left endpoint and left endpoint plus duration. The genuine
marked compact-window first moment therefore has a time-occupation source
formula. No excursion intensity or Palm deletion identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMarkedExcursionTimeOccupation

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianFullHorizonExcursionAreas BrownianExcursionTuplePoissonWeights
open BrownianExcursionOccupationCampbell BrownianExcursionCampbellWeights
open BrownianExcursionWindowPointMeasure ComponentGlobalPointProcess FinitePointMeasureCompact

def intervalArea (lambda : ℝ) (p : Path × ℝ × ℝ) : ℝ≥0 :=
  BrownianReflectedAreaCounts.area lambda (Real.toNNReal p.2.1)
    (Real.toNNReal (p.2.1+p.2.2)) p.1

theorem measurable_intervalArea (lambda : ℝ) : Measurable (intervalArea lambda) := by
  have hmap : Measurable (fun p : Path × ℝ × ℝ ↦
      ((lambda,p.1),(Real.toNNReal p.2.1,Real.toNNReal (p.2.1+p.2.2)))) :=
    (measurable_const.prodMk measurable_fst).prodMk
      ((continuous_real_toNNReal.measurable.comp measurable_snd.fst).prodMk
        (continuous_real_toNNReal.measurable.comp (measurable_snd.fst.add measurable_snd.snd)))
  exact BrownianReflectedAreaCounts.measurable_area_all_parameters.comp hmap

theorem intervalArea_at_component (lambda q : ℝ) (f : Path) :
    intervalArea lambda (f,leftEndpoint q (driftedReflectionPath lambda f),
      length q (driftedReflectionPath lambda f)) = excursionArea q lambda f := by
  unfold intervalArea excursionArea leftTime rightTime length
  have he : leftEndpoint q (driftedReflectionPath lambda f) +
      (rightEndpoint q (driftedReflectionPath lambda f) -
        leftEndpoint q (driftedReflectionPath lambda f)) =
        rightEndpoint q (driftedReflectionPath lambda f) := by ring
  simp only [he]

def windowPoissonMark (lambda a b : ℝ) (r : ℕ) (p : Path × ℝ × ℝ) : ℝ≥0∞ :=
  if p.2.2 ∈ Icc a b then poissonWeight (intervalArea lambda p) r else 0

theorem measurable_windowPoissonMark (lambda a b : ℝ) (r : ℕ) :
    Measurable (windowPoissonMark lambda a b r) :=
  Measurable.ite (measurable_snd.snd measurableSet_Icc)
    ((measurable_poissonWeight r).comp (measurable_intervalArea lambda)) measurable_const

theorem source_weight_eq_endpoint_mark (lambda a b : ℝ) (r : ℕ) (q : ℚ) (f : Path) :
    BrownianExcursionCampbellWeights.weight lambda a b r q f =
      if Representative (driftedReflectionPath lambda f) q then
        windowPoissonMark lambda a b r (f,leftEndpoint (q : ℝ) (driftedReflectionPath lambda f),
          length (q : ℝ) (driftedReflectionPath lambda f)) else 0 := by
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · simp only [BrownianExcursionCampbellWeights.weight,
      BrownianExcursionCampbellWeights.sourceEvent,hq,true_and,if_true,
      lengthValue,windowPoissonMark,intervalArea_at_component]
  · simp only [BrownianExcursionCampbellWeights.weight,
      BrownianExcursionCampbellWeights.sourceEvent,hq,false_and,if_false]

theorem actual_windowLaw_timeOccupation (lambda a b : ℝ) (r : ℕ) (ha : 0 < a) :
    (∫⁻ η : PointMeasure PositiveSizeSurplus,
      ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) univ
      ∂(BrownianExcursionCompactWindows.law lambda (cell a b r)
        (isCompact_cell a b r ha) : Measure _)) =
      ∫⁻ t : ℝ, ∫⁻ f : Path,
        BrownianExcursionOccupationCampbell.occupation lambda
          (fun p ↦ windowPoissonMark lambda a b r p / ENNReal.ofReal p.2.2) (f,t) ∂pathLaw := by
  rw [windowLaw_campbell_formula lambda a b r ha,
    lintegral_tsum (fun q ↦ (BrownianExcursionCampbellWeights.measurable_weight lambda a b r q).aemeasurable)]
  simpa only [source_weight_eq_endpoint_mark] using
    (actual_campbell_inverse_length lambda (windowPoissonMark lambda a b r)
      (measurable_windowPoissonMark lambda a b r)).symm

end PerronWright.BrownianMarkedExcursionTimeOccupation
