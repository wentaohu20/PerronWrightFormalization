import PerronWright.Probability.BrownianBridgeCyclicArea
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The literal path area is continuous in path and duration

Joint evaluation and the parametric interval integral prove compact-open
continuity of the actual area functional. No quadrature convergence or
probability-law hypothesis is inserted into these deterministic results.
-/

open MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section

namespace PerronWright.ContinuousPathAreaContinuity

open BrownianPathLaw BrownianBridgeCyclicArea

theorem continuous_pathArea (T : ℝ≥0) : Continuous (pathArea T) := by
  unfold pathArea
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (g : Path) (t : ℝ) ↦ g (Real.toNNReal t))
    (continuous_joint_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))) 0 T

theorem continuous_joint_pathArea :
    Continuous (fun p : ℝ≥0 × Path ↦ pathArea p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact continuous_joint_eval.comp
      (continuous_fst.snd.prodMk (continuous_real_toNNReal.comp continuous_snd))
  · exact NNReal.continuous_coe.comp continuous_fst

end PerronWright.ContinuousPathAreaContinuity
