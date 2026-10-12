import PerronWright.Probability.BrownianCompletedMinimumCampbellSource
import PerronWright.Probability.BrownianCompletedExcursionCandidateScaling
import PerronWright.Probability.BrownianCompletedExcursionScaledLaw

/-! # Literal complete-excursion shape in the actual minimum source

The true completed-return law is transported at the remaining source scale.
The lifetime Jacobian cancels the entrance normalization, leaving the
physical duration and the actual unit entrance shape in arbitrary Borel
tests. The retained future is the full residual parabolic driver.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedMinimumShapeSource

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianPathDilationLaw BrownianMinimumFuturePostUnit
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicCompletedMinimumSource BrownianMinimumFutureScaledStrongMarkov
open BrownianParabolicMinimumCompletedPassageLaw BrownianCompletedMinimumCampbellSource
open BrownianCompletedExcursionCandidateScaling BrownianMinimumFutureReturnPathGeometry
open BrownianCompletedExcursionScaledLaw
open BrownianParabolicFirstPassageStoppedTiltFull ContinuousPathMinimumSplitBandAverage
open FullHorizonExcursionSection

def shapeFactor (l : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*l*Real.sqrt l))

theorem measurable_shapeFactor : Measurable shapeFactor := by
  unfold shapeFactor
  fun_prop

private def sourceTest (lambda : ℝ) (p : ℝ≥0 × Path) (a : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (q : ℝ≥0 × Path) : ℝ≥0∞ :=
  density (lambda-(p.1 : ℝ)) q.1 q.2*
    (∫⁻ h : Path, Ψ (p,-a,q,driftPath (lambda-(p.1 : ℝ)-(q.1 : ℝ)) h) ∂pathLaw)

private theorem measurable_sourceTest (lambda : ℝ) (p : ℝ≥0 × Path) (a : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (sourceTest lambda p a Ψ) := by
  have hm : Measurable (fun z : (ℝ≥0 × Path) × Path ↦
      Ψ (p,-a,z.1,driftPath (lambda-(p.1 : ℝ)-(z.1.1 : ℝ)) z.2)) :=
    hΨ.comp (measurable_const.prodMk (measurable_const.prodMk
      (measurable_fst.prodMk (continuous_driftPath.measurable.comp
        ((measurable_const.sub
          (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd)))))
  exact (measurable_joint_density.comp (measurable_const.prodMk measurable_id)).mul
    hm.lintegral_prod_right'

private theorem measurable_shapeTest (lambda : ℝ) (p : ℝ≥0 × Path) (a : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (fun l : ℝ ↦ ∫⁻ e : Path,
      sourceTest lambda p a Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
        ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  exact ((measurable_sourceTest lambda p a Ψ hΨ).comp
    (measurable_fst.real_toNNReal.prodMk (measurable_joint_brownianDilation.comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)))).lintegral_prod_right'

private theorem candidate_shape_exchange (lambda : ℝ) (T : ℝ≥0) (p : ℝ≥0 × Path)
    (hp : p.1 < T) (a : ℝ) (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
      ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
      (∫⁻ q, sourceTest lambda p a Ψ q ∂scaledCandidateLaw (T-p.1)) =
        ∫⁻ l : ℝ in Ioi ((T-p.1 : ℝ≥0) : ℝ), shapeFactor l*
          (∫⁻ e : Path,
            sourceTest lambda p a Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
              ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  have hr : 0 < T-p.1 := tsub_pos_of_lt hp
  have hm := measurable_shapeTest lambda p a Ψ hΨ
  rw [lintegral_scaledCandidateLaw (T-p.1) hr _ (measurable_sourceTest lambda p a Ψ hΨ)]
  have hmul : Measurable (fun l : ℝ ↦ lifetimeDensity (T-p.1) l*
      (∫⁻ e : Path,
        sourceTest lambda p a Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)) :=
    (measurable_lifetimeDensity (T-p.1)).mul hm
  rw [← lintegral_const_mul _ hmul,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro l
  rw [← mul_assoc,← NNReal.coe_sub hp.le,entrance_lifetime_weight_eq (T-p.1) hr]
  by_cases hl : ((T-p.1 : ℝ≥0) : ℝ) < l
  · rw [indicator_of_mem (show l ∈ Ioi ((T-p.1 : ℝ≥0) : ℝ) from hl),
      indicator_of_mem (show l ∈ Ioi ((T-p.1 : ℝ≥0) : ℝ) from hl)]
    rfl
  · rw [indicator_of_notMem (show l ∉ Ioi ((T-p.1 : ℝ≥0) : ℝ) from hl),
      indicator_of_notMem (show l ∉ Ioi ((T-p.1 : ℝ≥0) : ℝ) from hl),zero_mul]

theorem actual_parabolic_completed_shape_source_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (completion (minimumPoint T (driftPath lambda f))) ∂pathLaw) =
      ∫⁻ a : ℝ in Ioi 0, ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (∫⁻ l : ℝ in Ioi ((T-p.1 : ℝ≥0) : ℝ), shapeFactor l*
          (∫⁻ e : Path,
            density (lambda-(p.1 : ℝ)) (Real.toNNReal l) (brownianDilation (Real.toNNReal l) e)*
              (∫⁻ h : Path,
                Ψ (p,-a,(Real.toNNReal l,brownianDilation (Real.toNNReal l) e),
                  driftPath (lambda-(p.1 : ℝ)-(Real.toNNReal l : ℝ)) h) ∂pathLaw)
                  ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one))
                    ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  rw [actual_parabolic_completed_passage_source_lintegral lambda T hT Ψ hΨ]
  apply lintegral_congr
  intro a
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_fst measurableSet_Iio)] with p hp
  change (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
    ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
      (∫⁻ q, sourceTest lambda p a Ψ q ∂(sourceLaw (T-p.1)).map returnTaggedPast) = _
  rw [actual_scaled_returnTaggedPast_law (T-p.1) (tsub_pos_of_lt hp)]
  exact candidate_shape_exchange lambda T p hp a Ψ hΨ

theorem actual_completed_campbell_shape_source_lintegral (lambda : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        Ψ (componentState lambda (q : ℝ) f) else 0 ∂pathLaw) =
      ∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
        ∫⁻ p in {p : ℝ≥0 × Path | p.1 < Real.toNNReal t},
          (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ), shapeFactor l*
            (∫⁻ e : Path,
              density (lambda-(p.1 : ℝ)) (Real.toNNReal l) (brownianDilation (Real.toNNReal l) e)*
                (∫⁻ h : Path,
                  Ψ (p,-a,(Real.toNNReal l,brownianDilation (Real.toNNReal l) e),
                    driftPath (lambda-(p.1 : ℝ)-(Real.toNNReal l : ℝ)) h)/
                      (Real.toNNReal l : ℝ≥0∞) ∂pathLaw)
                        ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one))
                          ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  rw [actual_completed_campbell_inverse_length lambda Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  let Φ : CompletedState → ℝ≥0∞ := fun q ↦ Ψ q/(q.2.2.1.1 : ℝ≥0∞)
  have hΦ : Measurable Φ := hΨ.div measurable_snd.snd.fst.fst.coe_nnreal_ennreal
  exact actual_parabolic_completed_shape_source_lintegral lambda (Real.toNNReal t)
    (Real.toNNReal_pos.mpr ht) Φ hΦ

end PerronWright.BrownianCompletedMinimumShapeSource
