import PerronWright.Probability.BrownianBridgeMinimumStrictPositivity
import PerronWright.Probability.BrownianBridgeMinimumArea

/-! # Strict positivity of the actual minimum-shifted bridge area

The positive area is proved for the genuine transformed Gaussian bridge,
using its actual almost-sure minimum uniqueness. This does not identify
the area distribution with Wright constants.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal
noncomputable section

namespace PerronWright.BrownianBridgeMinimumAreaPositive

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeCyclicArea
open BrownianBridgeMinimumArea BrownianBridgeMinimumStrictPositivity

theorem pathArea_pos (T : ℝ≥0) (hT : 0 < T) (f : Path)
    (hn : ∀ t, 0 ≤ f t) (hp : ∀ t, 0 < t → t < T → 0 < f t) : 0 < pathArea T f := by
  apply intervalIntegral.integral_pos (show (0 : ℝ) < T from hT)
    ((continuous_path f).comp continuous_real_toNNReal).continuousOn
    (fun t _ ↦ hn (Real.toNNReal t))
  refine ⟨(T : ℝ)/2, ⟨by positivity, by linarith [T.coe_nonneg]⟩, ?_⟩
  apply hp
  · exact Real.toNNReal_pos.mpr (by positivity)
  · exact (Real.toNNReal_lt_iff_lt_coe (by positivity)).mpr (by linarith [show (0 : ℝ) < T from hT])

theorem ae_minimumShiftArea_pos (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, 0 < minimumShiftArea T hT f := by
  filter_upwards [ae_minimumShiftPath_strictly_positive T hT] with f hf
  exact pathArea_pos T hT _ (minimumShiftPath_nonnegative T hT f) hf

theorem ae_minimumShiftLaw_area_pos (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂minimumShiftLaw T hT, 0 < pathArea T f := by
  exact (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable
    (measurableSet_lt measurable_const (measurable_pathArea T))).mpr (ae_minimumShiftArea_pos T hT)

end PerronWright.BrownianBridgeMinimumAreaPositive
