import PerronWright.Probability.BrownianFirstPassageBridgeLaw
import PerronWright.Probability.BrownianBridgeCyclicArea
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Literal finite-horizon parabolic drift and its exponential density

The source score is the actual Brownian endpoint plus its interval area.
Splitting off the genuine pinned bridge gives two independent Gaussian
coordinates. The normalization polynomial and stopped drift are literal.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicDriftTiltGeometry

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeArea
open BrownianGaussianSkeleton
open BrownianBridgeCyclicArea BrownianBridgeAreaTiltPathLaw
open BrownianFirstPassageBridgeLaw

def score (lambda : ℝ) (T : ℝ≥0) (f : Path) : ℝ :=
  (lambda-(T : ℝ))*f T+pathArea T f

def energy (lambda : ℝ) (T : ℝ≥0) : ℝ :=
  lambda^2*(T : ℝ)-lambda*(T : ℝ)^2+(T : ℝ)^3/3

def density (lambda : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (score lambda T f-energy lambda T/2))

def stoppedParabolicPath (lambda : ℝ) (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ f (min t T)+lambda*(min t T : ℝ≥0)-(min t T : ℝ≥0)^2/2,
    (((continuous_path f).comp (continuous_id.min continuous_const)).add
      ((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul lambda)).sub
        (((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).pow 2).div_const 2)⟩

theorem measurable_stoppedParabolicPath (lambda : ℝ) (T : ℝ≥0) :
    Measurable (stoppedParabolicPath lambda T) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ f (min (rationalTimeReal q) T)+
    lambda*(min (rationalTimeReal q) T : ℝ≥0)-(min (rationalTimeReal q) T : ℝ≥0)^2/2)
  exact measurable_pi_lambda _ (fun q ↦
    ((continuous_eval (min (rationalTimeReal q) T)).measurable.add_const _).sub_const _)

theorem measurable_score (lambda : ℝ) (T : ℝ≥0) : Measurable (score lambda T) :=
  ((continuous_eval T).measurable.const_mul _).add (measurable_pathArea T)

theorem measurable_density (lambda : ℝ) (T : ℝ≥0) : Measurable (density lambda T) :=
  ((measurable_score lambda T).sub_const _).exp.ennreal_ofReal

theorem energy_eq_bridge_endpoint_variance (lambda : ℝ) (T : ℝ≥0) :
    energy lambda T = (T : ℝ)*(lambda-(T : ℝ)/2)^2+(T : ℝ)^3/12 := by
  unfold energy
  ring

theorem energy_pos (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) : 0 < energy lambda T := by
  rw [energy_eq_bridge_endpoint_variance]
  have ht : 0 < (T : ℝ) := hT
  positivity

theorem pathArea_stoppedBridgePath (T : ℝ≥0) (f : Path) :
    pathArea T (stoppedBridgePath T f) = area T f := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 (T : ℝ) := by simpa only [uIcc_of_le T.coe_nonneg] using ht
  have htNN : Real.toNNReal t ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht'.2
  change bridge T (min (Real.toNNReal t) T) f = bridge T (Real.toNNReal t) f
  rw [min_eq_left htNN]

theorem area_eq_pathArea_sub_endpoint (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    area T f = pathArea T f-(T : ℝ)/2*f T := by
  have ht : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hi : (∫ t in 0..(T : ℝ), bridge T (Real.toNNReal t) f) =
      (∫ t in 0..(T : ℝ), f (Real.toNNReal t)-t/(T : ℝ)*f T) := by
    apply intervalIntegral.integral_congr
    intro t ht'
    have ht'' : t ∈ Icc 0 (T : ℝ) := by simpa only [uIcc_of_le T.coe_nonneg] using ht'
    simp only [bridge,Real.coe_toNNReal t ht''.1]
  change (∫ t in 0..(T : ℝ), bridge T (Real.toNNReal t) f) = _
  have hfi : IntervalIntegrable (fun t : ℝ ↦ f (Real.toNNReal t)) volume 0 T :=
    ((continuous_path f).comp continuous_real_toNNReal).intervalIntegrable 0 T
  have hli : IntervalIntegrable (fun t : ℝ ↦ t/(T : ℝ)*f T) volume 0 T := by
    exact ((continuous_id.div_const (T : ℝ)).mul continuous_const).intervalIntegrable 0 T
  rw [hi,intervalIntegral.integral_sub hfi hli,
    intervalIntegral.integral_mul_const,intervalIntegral.integral_div,integral_id]
  change pathArea T f-((T : ℝ)^2-0^2)/2/(T : ℝ)*f T = _
  field_simp
  ring

theorem score_eq_bridge_endpoint (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    score lambda T f = area T f+(lambda-(T : ℝ)/2)*f T := by
  rw [area_eq_pathArea_sub_endpoint T hT]
  unfold score
  ring

def bridgeDensity (T : ℝ≥0) (g : Path) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (pathArea T g-(T : ℝ)^3/24))

def endpointDensity (lambda : ℝ) (T : ℝ≥0) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((lambda-(T : ℝ)/2)*z-(T : ℝ)*(lambda-(T : ℝ)/2)^2/2))

theorem measurable_bridgeDensity (T : ℝ≥0) : Measurable (bridgeDensity T) :=
  ((measurable_pathArea T).sub_const _).exp.ennreal_ofReal

theorem measurable_endpointDensity (lambda : ℝ) (T : ℝ≥0) :
    Measurable (endpointDensity lambda T) := by
  unfold endpointDensity
  fun_prop

theorem density_eq_bridge_endpoint_product (lambda : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (f : Path) :
    density lambda T f = bridgeDensity T (stoppedBridgePath T f)*endpointDensity lambda T (f T) := by
  unfold density bridgeDensity endpointDensity
  rw [pathArea_stoppedBridgePath,score_eq_bridge_endpoint lambda T hT,
    energy_eq_bridge_endpoint_variance,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

def bridgeShift (T : ℝ≥0) (g : Path) : Path :=
  ⟨fun t ↦ g t+meanPath T 1 t,(continuous_path g).add (continuous_path (meanPath T 1))⟩

theorem measurable_bridgeShift (T : ℝ≥0) : Measurable (bridgeShift T) :=
  rationalEval_measurableEmbedding.measurable_comp_iff.mp
    (measurable_pi_lambda _ (fun q ↦ (continuous_eval (rationalTimeReal q)).measurable.add_const _))

theorem bridgeShift_stoppedBridgePath (T : ℝ≥0) (f : Path) :
    bridgeShift T (stoppedBridgePath T f) = shiftedBridgePath T 1 f := by
  apply ContinuousMap.ext
  intro t
  rfl

theorem reconstruct_shift_eq_stoppedParabolic (lambda : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (f : Path) :
    reconstruct T (bridgeShift T (stoppedBridgePath T f),f T+(lambda-(T : ℝ)/2)*(T : ℝ)) =
      stoppedParabolicPath lambda T f := by
  apply ContinuousMap.ext
  intro t
  have ht : (T : ℝ) ≠ 0 := ne_of_gt hT
  change bridge T (min t T) f+1*BrownianBridgeAreaCrossKernel.crossMean T (min t T)+
    (min t T : ℝ≥0)/(T : ℝ)*(f T+(lambda-(T : ℝ)/2)*(T : ℝ)) =
    f (min t T)+lambda*(min t T : ℝ≥0)-(min t T : ℝ≥0)^2/2
  unfold bridge BrownianBridgeAreaCrossKernel.crossMean
  field_simp
  ring

end PerronWright.BrownianParabolicDriftTiltGeometry
