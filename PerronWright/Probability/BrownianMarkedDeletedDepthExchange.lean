import PerronWright.Probability.BrownianMarkedDeletedCampbellTest

/-! # Full-area marks in the actual completed depth exchange

For each complete zero-endpoint excursion, arbitrary Borel tests of the
deleted Brownian noise survive the proved actual stopped-density exchange.
The literal Poisson mark remains the full-area weight, at every surplus.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMarkedDeletedDepthExchange

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianBridgeCyclicArea BrownianParabolicDriftTiltGeometry
open BrownianParabolicFirstPassageStoppedTiltFull
open BrownianParabolicCompletedMinimumSource BrownianCompletedMinimumDeletionSource
open BrownianCompletedMinimumNoiseCoordinates BrownianMarkedDeletedCampbellTest
open BrownianExcursionTuplePoissonWeights

theorem markedDeletedTest_depth_lintegral (lambda : ℝ) (l : ℝ≥0) (hl : 0 < l)
    (e : Path) (he : e l = 0) (r : ℕ) (H : ℝ × Path → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
      density (lambda-(p.1 : ℝ)) l e *
        (∫⁻ h : Path, markedDeletedTest lambda r H
          (p,-a,(l,e),driftPath (lambda-(p.1 : ℝ)-(l : ℝ)) h) ∂pathLaw)
            ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      poissonWeight (Real.toNNReal (pathArea l e)) r *
        (ENNReal.ofReal (Real.exp (pathArea l e-energy lambda l/2)) *
          ((l : ℝ≥0∞)⁻¹*(∫⁻ f : Path, H ((l : ℝ),f) ∂pathLaw))) := by
  let W := poissonWeight (Real.toNNReal (pathArea l e)) r
  have hW : W ≠ ⊤ := ENNReal.ofReal_ne_top
  let F : Path → ℝ≥0∞ := fun f ↦ H ((l : ℝ),f)
  have hF : Measurable F := hH.comp (measurable_const.prodMk measurable_id)
  have hh (p : ℝ≥0 × Path) (a : ℝ) :
      (∫⁻ h : Path, markedDeletedTest lambda r H
        (p,-a,(l,e),driftPath (lambda-(p.1 : ℝ)-(l : ℝ)) h) ∂pathLaw) =
        W*(∫⁻ h : Path, F (recoverNoise (lambda-(l : ℝ))
          (splicePath p.1 (p.2,driftPath (lambda-(l : ℝ)-(p.1 : ℝ)) h))) ∂pathLaw) := by
    have hp : lambda-(p.1 : ℝ)-(l : ℝ) = lambda-(l : ℝ)-(p.1 : ℝ) := by ring
    simp only [markedDeletedTest,completeArea,remainingDriver,hp]
    exact lintegral_const_mul' W _ hW
  calc
    _ = W*(∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
        density (lambda-(p.1 : ℝ)) l e *
          (∫⁻ h : Path, F (recoverNoise (lambda-(l : ℝ))
            (splicePath p.1 (p.2,driftPath (lambda-(l : ℝ)-(p.1 : ℝ)) h))) ∂pathLaw)
              ∂pathLaw.map (actualDriverPassagePast lambda (-a))) := by
      simp_rw [hh]
      have hc (d j : ℝ≥0∞) : d*(W*j) = W*(d*j) := by ac_rfl
      simp_rw [hc,lintegral_const_mul' W _ hW]
    _ = _ := by
      rw [actual_complete_excursion_integrated_noise_exchange lambda l hl e he F hF]

end PerronWright.BrownianMarkedDeletedDepthExchange
