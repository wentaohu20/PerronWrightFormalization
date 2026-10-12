import PerronWright.Probability.BrownianMinimumSplitLaw
import PerronWright.Probability.BrownianMinimumSplitCandidateMarginals

/-! # True Brownian minimum depth/time laws

The full actual path split has been identified with its genuine source.
Its explicit source marginals therefore give the joint depth/time density
and the arcsine law of the actual minimum time, without marginal-law inputs.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumSplitActualMarginals

open BrownianPathLaw ContinuousPathLeastMinimum ContinuousPathMinimumSplitBandAverage
open BrownianMinimumSplitLaw BrownianMinimumSplitCandidateMarginals

theorem actual_depth_time_law (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f : Path ↦ (-minimumValue T f,(leastMinimizer T f : ℝ))) =
      volume.withDensity (depthTimeDensity T) := by
  let M : (ℝ≥0 × Path) × (ℝ × Path) → ℝ × ℝ :=
    fun q ↦ (-q.2.1,(q.1.1 : ℝ))
  have hM : Measurable M := measurable_snd.fst.neg.prodMk
    (NNReal.continuous_coe.measurable.comp measurable_fst.fst)
  have h := candidate_depth_time_map_eq_withDensity T
  rw [← actual_minimum_split_law T hT,Measure.map_map hM (measurable_minimumPoint T)] at h
  exact h

theorem actual_minimum_time_law (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f : Path ↦ (leastMinimizer T f : ℝ)) =
      volume.withDensity (arcsineDensity T) := by
  have hM : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦ (q.1.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst.fst
  have h := candidate_time_map_eq_withDensity T
  rw [← actual_minimum_split_law T hT,Measure.map_map hM (measurable_minimumPoint T)] at h
  exact h

theorem actual_depth_time_lintegral (T : ℝ≥0) (hT : 0 < T)
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f : Path, H (-minimumValue T f,(leastMinimizer T f : ℝ)) ∂pathLaw) =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
            ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-s)))*H (a,s) := by
  have hM : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦
      H (-q.2.1,(q.1.1 : ℝ))) :=
    hH.comp (measurable_snd.fst.neg.prodMk
      (NNReal.continuous_coe.measurable.comp measurable_fst.fst))
  change (∫⁻ f : Path, H (-(minimumPoint T f).2.1,((minimumPoint T f).1.1 : ℝ)) ∂pathLaw) = _
  rw [← lintegral_map hM (measurable_minimumPoint T),actual_minimum_split_law T hT]
  exact candidate_depth_time_lintegral T H hH

theorem actual_minimum_time_lintegral (T : ℝ≥0) (hT : 0 < T)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f : Path, H (leastMinimizer T f : ℝ) ∂pathLaw) =
      ∫⁻ s : ℝ, arcsineDensity T s*H s := by
  have hM : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦ H (q.1.1 : ℝ)) :=
    hH.comp (NNReal.continuous_coe.measurable.comp measurable_fst.fst)
  change (∫⁻ f : Path, H ((minimumPoint T f).1.1 : ℝ) ∂pathLaw) = _
  rw [← lintegral_map hM (measurable_minimumPoint T),actual_minimum_split_law T hT]
  exact candidate_time_lintegral T H hH

end PerronWright.BrownianMinimumSplitActualMarginals
