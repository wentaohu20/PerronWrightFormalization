import PerronWright.Probability.BrownianBridgeMinimumDilationLaw
import PerronWright.Probability.BrownianBridgeMinimumArea
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Actual minimum-shift bridge area has duration power three-halves

Ordinary change of variables proves the literal path-area identity.
The true whole-path law dilation then proves the actual area law
pushforward. This does not identify unit-duration minimum-shift area
with positive-excursion area or with Wright constants.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumAreaDilation

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianBridgeMinimumShift BrownianBridgeMinimumArea BrownianBridgeDilationGeometry
open BrownianBridgeMinimumDilationLaw

theorem pathArea_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (f : Path) :
    pathArea T (dilatePath T c f) = (T : ℝ)*c*pathArea 1 f := by
  have htime (t : ℝ) : Real.toNNReal t/T = Real.toNNReal (t/(T : ℝ)) := by
    rw [Real.toNNReal_div' T.coe_nonneg,Real.toNNReal_coe]
  unfold pathArea
  change (∫ t in 0..(T : ℝ), c*f (Real.toNNReal t/T)) = _
  simp_rw [htime]
  rw [intervalIntegral.integral_const_mul]
  have hchange := intervalIntegral.integral_comp_div (fun x : ℝ ↦ f (Real.toNNReal x))
    (a := 0) (b := (T : ℝ)) (ne_of_gt (show 0 < (T : ℝ) from hT))
  rw [hchange]
  simp only [zero_div,div_self (ne_of_gt (show 0 < (T : ℝ) from hT)),NNReal.coe_one,smul_eq_mul]
  ring

theorem minimumShiftArea_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    minimumShiftArea T hT (dilatePath T c f) = (T : ℝ)*c*minimumShiftArea 1 zero_lt_one f := by
  unfold minimumShiftArea
  rw [minimumShiftPath_dilatePath T hT c hc f,pathArea_dilatePath T hT c]

theorem duration_mul_sqrt_eq_rpow (T : ℝ≥0) (hT : 0 < T) :
    (T : ℝ)*Real.sqrt (T : ℝ) = (T : ℝ)^(3/2 : ℝ) := by
  calc (T : ℝ)*Real.sqrt (T : ℝ) = (T : ℝ)^(1 : ℝ)*(T : ℝ)^(1/2 : ℝ) := by
        rw [Real.rpow_one,Real.sqrt_eq_rpow]
    _ = (T : ℝ)^(1+1/2 : ℝ) := (Real.rpow_add (show 0 < (T : ℝ) from hT) _ _).symm
    _ = (T : ℝ)^(3/2 : ℝ) := by norm_num

theorem minimumShiftArea_brownianDilation (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftArea T hT (brownianDilation T f) =
      (T : ℝ)^(3/2 : ℝ)*minimumShiftArea 1 zero_lt_one f := by
  unfold brownianDilation
  calc minimumShiftArea T hT (dilatePath T (Real.sqrt (T : ℝ)) f) =
        (T : ℝ)*Real.sqrt (T : ℝ)*minimumShiftArea 1 zero_lt_one f :=
        minimumShiftArea_dilatePath T hT (Real.sqrt (T : ℝ))
          (Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT)) f
    _ = (T : ℝ)^(3/2 : ℝ)*minimumShiftArea 1 zero_lt_one f := by
        rw [duration_mul_sqrt_eq_rpow T hT]

def minimumShiftAreaLaw (T : ℝ≥0) (hT : 0 < T) : Measure ℝ :=
  pathLaw.map (minimumShiftArea T hT)

instance (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (minimumShiftAreaLaw T hT) :=
  Measure.isProbabilityMeasure_map (measurable_minimumShiftArea T hT).aemeasurable

theorem minimumShiftAreaLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftAreaLaw T hT =
      (minimumShiftAreaLaw 1 zero_lt_one).map (fun x ↦ (T : ℝ)^(3/2 : ℝ)*x) := by
  calc minimumShiftAreaLaw T hT = (pathLaw.map (brownianDilation T)).map (minimumShiftArea T hT) := by
        rw [pathLaw_brownianDilation T hT]
        rfl
    _ = pathLaw.map ((fun x ↦ (T : ℝ)^(3/2 : ℝ)*x) ∘ minimumShiftArea 1 zero_lt_one) := by
        rw [Measure.map_map (measurable_minimumShiftArea T hT) (measurable_brownianDilation T)]
        congr 1
        exact funext (minimumShiftArea_brownianDilation T hT)
    _ = (minimumShiftAreaLaw 1 zero_lt_one).map (fun x ↦ (T : ℝ)^(3/2 : ℝ)*x) := by
        rw [minimumShiftAreaLaw,Measure.map_map (by fun_prop) (measurable_minimumShiftArea 1 zero_lt_one)]

/-- Exact duration scaling for arbitrary nonnegative Borel area tests,
without assuming finite moments or exponential integrability. -/
theorem lintegral_minimumShiftArea_duration_scaling (T : ℝ≥0) (hT : 0 < T)
    (Φ : ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (minimumShiftArea T hT f) ∂pathLaw) =
      ∫⁻ f, Φ ((T : ℝ)^(3/2 : ℝ)*minimumShiftArea 1 zero_lt_one f) ∂pathLaw := by
  calc (∫⁻ f, Φ (minimumShiftArea T hT f) ∂pathLaw) =
        ∫⁻ f, Φ (minimumShiftArea T hT f) ∂(pathLaw.map (brownianDilation T)) := by
        rw [pathLaw_brownianDilation T hT]
    _ = ∫⁻ f, Φ (minimumShiftArea T hT (brownianDilation T f)) ∂pathLaw :=
        lintegral_map (hΦ.comp (measurable_minimumShiftArea T hT)) (measurable_brownianDilation T)
    _ = ∫⁻ f, Φ ((T : ℝ)^(3/2 : ℝ)*minimumShiftArea 1 zero_lt_one f) ∂pathLaw := by
        apply lintegral_congr
        intro f
        rw [minimumShiftArea_brownianDilation T hT]

end PerronWright.BrownianBridgeMinimumAreaDilation
