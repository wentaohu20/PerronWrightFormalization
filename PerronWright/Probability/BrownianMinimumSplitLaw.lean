import PerronWright.Probability.BrownianMinimumSplitCylinderLimit
import PerronWright.Probability.BrownianMinimumSplitSampling

/-! # Actual full Brownian minimum-split disintegration

The genuine joint finite-coordinate tests determine the two tagged whole
continuous paths. The resulting Borel disintegration retains the stopped
past, minimum time and level, and the entire future, including the future
beyond the fixed horizon. No path-law identity is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitLaw

open BrownianPathLaw ContinuousPathMinimumSplitBandAverage
open BrownianMinimumSplitCandidate BrownianFirstPassageEndpointGeometry BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource
open BrownianPathIndependentIncrements

theorem actual_minimum_split_law (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (minimumPoint T) = candidateLaw T := by
  let := candidateLaw_isFinite T hT
  apply BrownianMinimumSplitSampling.ext_of_finite_sample_tests
  intro m n σ τ Ψ
  simpa only [BrownianMinimumSplitSampling.sample] using
    BrownianMinimumSplitCylinderLimit.actual_finite_cylinder_nnreal_test T hT σ τ Ψ

theorem actual_minimum_split_lintegral (T : ℝ≥0) (hT : 0 < T)
    (Φ : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (minimumPoint T f) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, Φ (p,-a,brownianDilation (remainingTime T (p.1 : ℝ)) g) ∂unitSourceLaw)
            ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a) := by
  have hm := measurable_minimumPoint T
  calc
    _ = ∫⁻ z, Φ z ∂pathLaw.map (minimumPoint T) := (lintegral_map hΦ hm).symm
    _ = ∫⁻ z, Φ z ∂candidateLaw T := by rw [actual_minimum_split_law T hT]
    _ = _ := lintegral_candidateLaw T Φ hΦ

theorem actual_reconstructed_source_lintegral (T : ℝ≥0) (hT : 0 < T)
    (F : Path → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ f, F f ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, F (splicePath p.1
            (p.2,brownianDilation (remainingTime T (p.1 : ℝ)) g)) ∂unitSourceLaw)
            ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a) := by
  have hr : Continuous (fun z : (ℝ≥0 × Path) × (ℝ × Path) ↦
      splicePath z.1.1 (z.1.2,z.2.2)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.snd.eval
      (continuous_snd.min continuous_fst.fst.fst)).add
        (continuous_fst.snd.snd.eval (continuous_snd.sub continuous_fst.fst.fst))
  have h := actual_minimum_split_lintegral T hT
    (fun z ↦ F (splicePath z.1.1 (z.1.2,z.2.2))) (hF.comp hr.measurable)
  simpa only [minimumPoint_reconstruct] using h

end PerronWright.BrownianMinimumSplitLaw
