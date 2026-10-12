import PerronWright.Probability.BrownianParabolicMinimumSplitLaw
import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull

/-! # Genuine parabolic first-passage source for the full minimum split

The literal density cocycle factors at the actual minimum. The proved
uncapped stopped-driver Radon--Nikodym identity changes the actual outer
negative-level Brownian passage law to the actual parabolic passage law.
Both stopped past and entire residual future remain in arbitrary Borel
tests; no minimum or excursion conditional law is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumSplitPassageLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathLeastMinimum ContinuousPathMinimumSplitBandAverage
open BrownianMinimumSplitLaw BrownianMinimumSplitCandidate BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianFirstPassageEndpointGeometry
open BrownianMinimumFuturePostUnit
open BrownianParabolicWholePathTilt BrownianParabolicDriftTiltGeometry
open BrownianParabolicStoppedTiltGeometry BrownianParabolicFirstPassageStoppedTilt
open BrownianParabolicFirstPassageStoppedTiltFull BrownianParabolicMinimumSplitLaw

private def densityFactor (lambda : ℝ) (T : ℝ≥0)
    (z : (ℝ≥0 × Path) × (ℝ × Path)) : ℝ≥0∞ :=
  stoppedDensity lambda z.1*density (lambda-(z.1.1 : ℝ)) (T-z.1.1) z.2.2

private theorem measurable_densityFactor (lambda : ℝ) (T : ℝ≥0) :
    Measurable (densityFactor lambda T) :=
  ((measurable_stoppedDensity lambda).comp measurable_fst).mul
    (measurable_joint_density.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk
        ((measurable_const.sub measurable_fst.fst).prodMk measurable_snd.snd)))

private theorem splitDensity_minimumPoint (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    splitDensity lambda T (minimumPoint T f) = densityFactor lambda T (minimumPoint T f) := by
  change density lambda T (splicePath (minimumPoint T f).1.1
    ((minimumPoint T f).1.2,(minimumPoint T f).2.2)) = _
  rw [minimumPoint_reconstruct]
  have h := density_add lambda (leastMinimizer T f) (T-leastMinimizer T f) f
  rw [add_tsub_cancel_of_le (leastMinimizer_le_time T f),
    ← density_past lambda (leastMinimizer T f) f] at h
  exact h

theorem ae_splitDensity_eq_stopped_future (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ z ∂candidateLaw T, splitDensity lambda T z =
      stoppedDensity lambda z.1*density (lambda-(z.1.1 : ℝ)) (T-z.1.1) z.2.2 := by
  change ∀ᵐ z ∂candidateLaw T, splitDensity lambda T z = densityFactor lambda T z
  rw [← actual_minimum_split_law T hT]
  apply (ae_map_iff (measurable_minimumPoint T).aemeasurable
    (measurableSet_eq_fun (measurable_splitDensity lambda T) (measurable_densityFactor lambda T))).mpr
  exact Eventually.of_forall (splitDensity_minimumPoint lambda T)

theorem actual_parabolic_passage_source_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Φ : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (minimumPoint T (driftPath lambda f)) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, density (lambda-(p.1 : ℝ)) (T-p.1)
            (brownianDilation (remainingTime T (p.1 : ℝ)) g)*
              Φ (p,-a,wholeLift (lambda-(p.1 : ℝ)) (T-p.1)
                (brownianDilation (remainingTime T (p.1 : ℝ)) g)) ∂unitSourceLaw)
            ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  let F : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0∞ := fun z ↦
    density (lambda-(z.1.1 : ℝ)) (T-z.1.1) z.2.2*Φ (liftSplit lambda T z)
  have hF : Measurable F :=
    (measurable_joint_density.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk
        ((measurable_const.sub measurable_fst.fst).prodMk measurable_snd.snd))).mul
      (hΦ.comp (measurable_liftSplit lambda T))
  have hd := BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda
  change (∫⁻ f, Φ ((minimumPoint T ∘ driftPath lambda) f) ∂pathLaw) = _
  rw [← lintegral_map hΦ ((measurable_minimumPoint T).comp hd)]
  change (∫⁻ z, Φ z ∂pathLaw.map (fun f ↦ minimumPoint T (driftPath lambda f))) = _
  rw [actual_parabolic_minimum_split_law lambda T hT,
    lintegral_map hΦ (measurable_liftSplit lambda T)]
  change (∫⁻ z, (Φ ∘ liftSplit lambda T) z
    ∂(candidateLaw T).withDensity (splitDensity lambda T)) = _
  rw [
    lintegral_withDensity_eq_lintegral_mul _ (measurable_splitDensity lambda T)
      (hΦ.comp (measurable_liftSplit lambda T))]
  calc
    _ = ∫⁻ z, stoppedDensity lambda z.1*F z ∂candidateLaw T := by
      apply lintegral_congr_ae
      filter_upwards [ae_splitDensity_eq_stopped_future lambda T hT] with z hz
      simp only [Pi.mul_apply,Function.comp_def]
      rw [hz]
      exact mul_assoc _ _ _
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, stoppedDensity lambda p*
            F (p,-a,brownianDilation (remainingTime T (p.1 : ℝ)) g) ∂unitSourceLaw)
            ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a) :=
      lintegral_candidateLaw T _ (((measurable_stoppedDensity lambda).comp measurable_fst).mul hF)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      let J : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦
        F (z.1,-a,brownianDilation (remainingTime T (z.1.1 : ℝ)) z.2)
      have hpoint : Measurable (fun z : (ℝ≥0 × Path) × Path ↦
          (z.1,-a,brownianDilation (remainingTime T (z.1.1 : ℝ)) z.2)) :=
        measurable_fst.prodMk (measurable_const.prodMk (measurable_joint_brownianDilation.comp
          (((continuous_remainingTime T).measurable.comp
            (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd)))
      have hJ : Measurable J := hF.comp hpoint
      let H : ℝ≥0 × Path → ℝ≥0∞ := fun p ↦
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          ∫⁻ g, J (p,g) ∂unitSourceLaw
      have hH : Measurable H :=
        (measurable_const.mul (by fun_prop)).mul (hJ.lintegral_prod_right' (ν := unitSourceLaw))
      have hS : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} := measurable_fst measurableSet_Iio
      have he (p : ℝ≥0 × Path) :
          (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
            (∫⁻ g, stoppedDensity lambda p*J (p,g) ∂unitSourceLaw) = stoppedDensity lambda p*H p := by
        have hjp : Measurable (fun g : Path ↦ J (p,g)) :=
          hJ.comp ((measurable_const : Measurable (fun _ : Path ↦ p)).prodMk measurable_id)
        rw [lintegral_const_mul _ hjp]
        exact mul_left_comm _ _ _
      change (∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, stoppedDensity lambda p*J (p,g) ∂unitSourceLaw)
            ∂pathLaw.map (BrownianFirstPassageUncappedLaw.passagePast (-a))) =
        ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T}, H p ∂pathLaw.map (actualDriverPassagePast lambda (-a))
      rw [lintegral_congr he,actual_parabolic_passage_law lambda (-a) (neg_neg_of_pos ha)]
      rw [← lintegral_indicator hS,← lintegral_indicator hS,
        lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity lambda) (hH.indicator hS)]
      apply lintegral_congr
      intro p
      by_cases hp : p.1 < T <;> simp only [Pi.mul_apply,Set.indicator,mem_ofPred_eq,hp,if_true,if_false,mul_zero]

end PerronWright.BrownianParabolicMinimumSplitPassageLaw
