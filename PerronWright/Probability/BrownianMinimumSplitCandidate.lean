import PerronWright.Probability.BrownianMinimumFuturePostUnit
import PerronWright.Probability.BrownianFirstPassagePastTimeMarginal
import PerronWright.Probability.BrownianMinimumSplitWindowLevelIntegral

/-! # Literal finite candidate for the full Brownian minimum split

Its stopped past is the actual negative-level first-passage stopped past.
Its future is a duration-scaled actual minimum-future source. The scalar
weight is explicit, and the proved time marginal gives genuine finite
mass. No probability normalization or minimum-split identity is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitCandidate

open BrownianPathLaw BrownianFirstPassageUncappedLaw BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit
open BrownianMinimumSplitWindowLevelIntegral BrownianFirstPassageMinimumWindowPastFutureLaw
open BrownianFirstPassagePastTimeMarginal BrownianFirstPassageEndpointGeometry

def entranceCoefficient : ℝ := Real.sqrt (2/Real.pi)

private def taggedPast (q : ℝ × Path) : ℝ≥0 × Path := passagePast (-q.1) q.2

private theorem measurable_taggedPast : Measurable taggedPast :=
  measurable_joint_passagePast.comp (measurable_fst.neg.prodMk measurable_snd)

private def pastBase : Measure (ℝ × Path) := (volume.restrict (Ioi (0 : ℝ))).prod pathLaw

private def inverseWeight (T : ℝ≥0) (q : ℝ × Path) : ℝ≥0∞ :=
  if (taggedPast q).1 < T then
    ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-((taggedPast q).1 : ℝ))) else 0

private theorem measurable_inverseWeight (T : ℝ≥0) : Measurable (inverseWeight T) :=
  Measurable.ite (measurableSet_lt measurable_taggedPast.fst measurable_const)
    ((measurable_const.div (Real.continuous_sqrt.measurable.comp
      (measurable_const.sub (NNReal.continuous_coe.measurable.comp
        measurable_taggedPast.fst)))).ennreal_ofReal) measurable_const

def sourcePastWeight (T : ℝ≥0) (q : ℝ × Path) : ℝ≥0∞ :=
  ENNReal.ofReal entranceCoefficient*inverseWeight T q

theorem measurable_sourcePastWeight (T : ℝ≥0) : Measurable (sourcePastWeight T) :=
  measurable_const.mul (measurable_inverseWeight T)

private theorem lintegral_inverseWeight (T : ℝ≥0) :
    (∫⁻ q, inverseWeight T q ∂pastBase) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))) ∂passagePastLaw (-a) := by
  rw [pastBase,lintegral_prod _ (measurable_inverseWeight T).aemeasurable]
  apply lintegral_congr
  intro a
  have hS : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} := measurable_fst measurableSet_Iio
  let H : ℝ≥0 × Path → ℝ≥0∞ :=
    {p : ℝ≥0 × Path | p.1 < T}.indicator
      (fun p ↦ ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))
  have hH : Measurable H := (by fun_prop : Measurable
    (fun p : ℝ≥0 × Path ↦ ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))).indicator hS
  rw [← lintegral_indicator hS,passagePastLaw,lintegral_map hH (measurable_passagePast (-a))]
  rfl

private theorem lintegral_sourcePastWeight_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ q, sourcePastWeight T q ∂pastBase) ≠ ⊤ := by
  change (∫⁻ q, ENNReal.ofReal entranceCoefficient*inverseWeight T q ∂pastBase) ≠ ⊤
  rw [lintegral_const_mul _ (measurable_inverseWeight T),lintegral_inverseWeight]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_level_past_time_inverse_sqrt_ne_top T hT)

def sourcePoint (T : ℝ≥0) (q : (ℝ × Path) × Path) : (ℝ≥0 × Path) × (ℝ × Path) :=
  (taggedPast q.1,-q.1.1,
    brownianDilation (remainingTime T ((taggedPast q.1).1 : ℝ)) q.2)

theorem measurable_sourcePoint (T : ℝ≥0) : Measurable (sourcePoint T) :=
  (measurable_taggedPast.comp measurable_fst).prodMk
    (measurable_fst.fst.neg.prodMk (measurable_joint_brownianDilation.comp
      (((continuous_remainingTime T).measurable.comp
        (NNReal.continuous_coe.measurable.comp (measurable_taggedPast.comp measurable_fst).fst)).prodMk
          measurable_snd)))

def candidateLaw (T : ℝ≥0) : Measure ((ℝ≥0 × Path) × (ℝ × Path)) :=
  (((pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw).map (sourcePoint T))

theorem candidateLaw_isFinite (T : ℝ≥0) (hT : 0 < T) : IsFiniteMeasure (candidateLaw T) := by
  let := isFiniteMeasure_withDensity (lintegral_sourcePastWeight_ne_top T hT)
  exact Measure.isFiniteMeasure_map
    ((pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw) (sourcePoint T)

theorem lintegral_candidateLaw (T : ℝ≥0) (Φ : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ p, Φ p ∂candidateLaw T) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, Φ (p,-a,brownianDilation (remainingTime T (p.1 : ℝ)) g) ∂unitSourceLaw)
            ∂passagePastLaw (-a) := by
  have hi : Measurable (fun q : ℝ × Path ↦ ∫⁻ g, Φ (sourcePoint T (q,g)) ∂unitSourceLaw) :=
    (hΦ.comp (measurable_sourcePoint T)).lintegral_prod_right'
  have hw := (measurable_sourcePastWeight T).mul hi
  rw [candidateLaw,lintegral_map hΦ (measurable_sourcePoint T)]
  change (∫⁻ z, (Φ ∘ sourcePoint T) z
    ∂(pastBase.withDensity (sourcePastWeight T)).prod unitSourceLaw) = _
  rw [lintegral_prod _ (hΦ.comp (measurable_sourcePoint T)).aemeasurable]
  change (∫⁻ q, (∫⁻ g, Φ (sourcePoint T (q,g)) ∂unitSourceLaw)
    ∂pastBase.withDensity (sourcePastWeight T)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_sourcePastWeight T) hi,
    pastBase,lintegral_prod _ hw.aemeasurable]
  apply lintegral_congr
  intro a
  let K : ℝ≥0 × Path → ℝ≥0∞ := fun p ↦
    (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
      (∫⁻ g, Φ (p,-a,brownianDilation (remainingTime T (p.1 : ℝ)) g) ∂unitSourceLaw)
  have hpoint : Measurable (fun q : (ℝ≥0 × Path) × Path ↦
      (q.1,-a,brownianDilation (remainingTime T (q.1.1 : ℝ)) q.2)) :=
    measurable_fst.prodMk (measurable_const.prodMk (measurable_joint_brownianDilation.comp
      (((continuous_remainingTime T).measurable.comp
        (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd)))
  have hK : Measurable K :=
    (measurable_const.mul (by fun_prop)).mul ((hΦ.comp hpoint).lintegral_prod_right')
  have hS : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} := measurable_fst measurableSet_Iio
  rw [← lintegral_indicator hS,passagePastLaw,
    lintegral_map (hK.indicator hS) (measurable_passagePast (-a))]
  apply lintegral_congr
  intro f
  dsimp only [Pi.mul_apply]
  by_cases hp : (passagePast (-a) f).1 < T
  · simp only [sourcePastWeight,inverseWeight,taggedPast,sourcePoint,
      Set.indicator,mem_ofPred_eq,hp,if_true,K]
  · simp only [sourcePastWeight,inverseWeight,taggedPast,mul_zero,zero_mul,
      Set.indicator,mem_ofPred_eq,hp,if_false]

end PerronWright.BrownianMinimumSplitCandidate
