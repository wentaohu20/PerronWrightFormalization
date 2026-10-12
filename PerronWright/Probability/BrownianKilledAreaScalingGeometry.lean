import PerronWright.Probability.BrownianKilledAreaGeometry
import PerronWright.Probability.BrownianPathDilationLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Literal killed-path Brownian scaling geometry

Time dilation and positive spatial dilation transform genuine survival,
endpoint and boundary-shifted area pathwise, including zero duration.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaScalingGeometry

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianKilledAreaGeometry ContinuousPathFirstPassage

theorem dilatePath_eval_scaled_duration (c t : ℝ≥0) (hc : 0 < c) (a : ℝ) (f : Path) :
    dilatePath c a f (c*t) = a*f t := by
  change a*f ((c*t)/c) = _
  rw [mul_div_cancel_left₀ t (ne_of_gt hc)]

theorem survival_dilatePath_scaled_duration (level : ℝ) (c t : ℝ≥0) (hc : 0 < c)
    (a : ℝ) (ha : 0 < a) (f : Path) :
    dilatePath c a f ∈ survival (a*level) (c*t) ↔ f ∈ survival level t := by
  rw [mem_survival_iff,mem_survival_iff]
  constructor
  · intro h s hs
    have hd := h (c*s) (mul_le_mul_of_nonneg_left hs c.coe_nonneg)
    rw [dilatePath_eval_scaled_duration c s hc a f] at hd
    exact (mul_lt_mul_iff_right₀ ha).mp hd
  · intro h s hs
    have hd := h (s/c) ((div_le_iff₀ hc).mpr (by simpa only [mul_comm t c] using hs))
    change a*level < a*f (s/c)
    exact mul_lt_mul_of_pos_left hd ha

theorem pathArea_dilatePath_scaled_duration (c t : ℝ≥0) (hc : 0 < c)
    (a : ℝ) (f : Path) :
    pathArea (c*t) (dilatePath c a f) = (c : ℝ)*a*pathArea t f := by
  have htime (s : ℝ) : Real.toNNReal s/c = Real.toNNReal (s/(c : ℝ)) := by
    rw [Real.toNNReal_div' c.coe_nonneg,Real.toNNReal_coe]
  unfold pathArea
  change (∫ s in 0..((c*t : ℝ≥0) : ℝ), a*f (Real.toNNReal s/c)) = _
  simp_rw [htime]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun s : ℝ ↦ f (Real.toNNReal s))
      (ne_of_gt (show 0 < (c : ℝ) from hc))]
  simp only [zero_div,NNReal.coe_mul,mul_div_cancel_left₀ _ (ne_of_gt (show 0 < (c : ℝ) from hc)),smul_eq_mul]
  ring

theorem shiftedArea_dilatePath_scaled_duration (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c)
    (a : ℝ) (f : Path) :
    shiftedArea (a*level) (a*x) (c*t) (dilatePath c a f) =
      (c : ℝ)*a*shiftedArea level x t f := by
  unfold shiftedArea
  rw [pathArea_dilatePath_scaled_duration c t hc a f,NNReal.coe_mul]
  ring

theorem duration_mul_sqrt_eq_rpow (c : ℝ≥0) (hc : 0 < c) :
    (c : ℝ)*Real.sqrt (c : ℝ) = (c : ℝ)^(3/2 : ℝ) := by
  calc (c : ℝ)*Real.sqrt (c : ℝ) = (c : ℝ)^(1 : ℝ)*(c : ℝ)^(1/2 : ℝ) := by
        rw [Real.rpow_one,Real.sqrt_eq_rpow]
    _ = (c : ℝ)^(1+1/2 : ℝ) :=
      (Real.rpow_add (show 0 < (c : ℝ) from hc) _ _).symm
    _ = (c : ℝ)^(3/2 : ℝ) := by norm_num

theorem survival_brownianDilation_scaled_duration (level x : ℝ) (c t : ℝ≥0)
    (hc : 0 < c) (f : Path) :
    brownianDilation c f ∈ survival (Real.sqrt (c : ℝ)*level-Real.sqrt (c : ℝ)*x) (c*t) ↔
      f ∈ survival (level-x) t := by
  rw [← mul_sub]
  exact survival_dilatePath_scaled_duration (level-x) c t hc _ (Real.sqrt_pos.mpr hc) f

theorem shiftedArea_brownianDilation_scaled_duration (level x : ℝ) (c t : ℝ≥0)
    (hc : 0 < c) (f : Path) :
    shiftedArea (Real.sqrt (c : ℝ)*level) (Real.sqrt (c : ℝ)*x) (c*t) (brownianDilation c f) =
      (c : ℝ)^(3/2 : ℝ)*shiftedArea level x t f := by
  rw [brownianDilation,shiftedArea_dilatePath_scaled_duration level x c t hc,
    duration_mul_sqrt_eq_rpow c hc]

theorem endpoint_brownianDilation_scaled_duration (x : ℝ) (c t : ℝ≥0) (hc : 0 < c)
    (f : Path) :
    Real.sqrt (c : ℝ)*x+brownianDilation c f (c*t) = Real.sqrt (c : ℝ)*(x+f t) := by
  rw [brownianDilation,dilatePath_eval_scaled_duration c t hc]
  ring

end PerronWright.BrownianKilledAreaScalingGeometry
