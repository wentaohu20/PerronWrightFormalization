import PerronWright.Probability.BrownianMarkedCompletedShapeCollapse
import PerronWright.Probability.BrownianActualPassageAnchorExchange

/-! # The actual full-area marked excursion Palm deletion formula

The genuine nonrepeating complete excursion section, physical return
shape law, and depth-dependent actual driver-passage source are integrated
out. Arbitrary nonnegative Borel tests retain the literal deleted Brownian
path. No Palm, conditional-shape, or finiteness interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianActualMarkedPalm

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianFullHorizonExcursionAreas BrownianExcursionDeletionGeometry
open BrownianExcursionTuplePoissonWeights BrownianMarkedDeletedCampbellTest
open BrownianCompletedMinimumCampbellSource BrownianCompletedCampbellShapeKernel
open BrownianMarkedCompletedShapeCollapse BrownianActualPassageAnchorExchange
open FactorialDensity

theorem actual_marked_palm_lintegral (lambda : ℝ) (r : ℕ)
    (H : ℝ × Path → ℝ≥0∞) (hH : Measurable H) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        poissonWeight (excursionArea (q : ℝ) lambda f) r *
          H (length (q : ℝ) (driftedReflectionPath lambda f),deletedPath (q : ℝ) lambda f)
      else 0 ∂pathLaw) =
      ∫⁻ l : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda l)*sizeFactor 1 l r) *
          (∫⁻ f : Path, H (l,f) ∂pathLaw) := by
  let Ψ := markedDeletedTest lambda r H
  have hΨ : Measurable Ψ := measurable_markedDeletedTest lambda r H hH
  calc
    _ = ∑' q : ℚ, ∫⁻ f : Path,
        if Representative (driftedReflectionPath lambda f) q then
          Ψ (componentState lambda (q : ℝ) f) else 0 ∂pathLaw :=
      (actual_marked_deleted_campbell_lintegral lambda r H hH).trans
        (actual_completed_campbell_inverse_length lambda Ψ hΨ).symm
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
        ∫⁻ p : ℝ≥0 × Path in {p | p.1 < Real.toNNReal t},
          (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
            shapeKernel lambda Ψ ((a,p),l)/ENNReal.ofReal l)
          ∂pathLaw.map (BrownianParabolicFirstPassageStoppedTiltFull.actualDriverPassagePast lambda (-a)) :=
      actual_completed_campbell_normalized_shape_lintegral lambda Ψ hΨ
    _ = ∫⁻ l : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
        shapeKernel lambda Ψ ((a,p),l)
          ∂pathLaw.map (BrownianParabolicFirstPassageStoppedTiltFull.actualDriverPassagePast lambda (-a)) :=
      actual_passage_anchor_inverse_length_swapped_lintegral lambda _
        (measurable_shapeKernel lambda Ψ hΨ)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      have h := actual_marked_shapeKernel_at_length lambda (Real.toNNReal l)
        (Real.toNNReal_pos.mpr hl) r H hH
      simpa only [Real.coe_toNNReal l hl.le] using h

end PerronWright.BrownianActualMarkedPalm
