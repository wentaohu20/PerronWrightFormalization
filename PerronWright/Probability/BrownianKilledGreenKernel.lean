import PerronWright.Probability.BrownianHeatResolvent
import PerronWright.Probability.BrownianKilledAreaMomentResolvent

/-! # The true absorbing-zero Green kernel

This is an evaluation of order-zero resolvents of the already identified
surviving Brownian moment measures. Gaussian reflection and the proved
heat duration transform give the exact formula, including zero initial
and target states. No Green-kernel identity is a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledGreenKernel

open BrownianHeatPassageTail BrownianHeatResolvent PositiveTimeConvolutionLaplace
open BrownianKilledAreaMomentResolvent BrownianKilledAreaMomentDensity

theorem realDensity_zero_add_heat (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    realDensity 0 t x y+heat t (x+y) = heat t (y-x) := by
  by_cases ht : 0 < t
  · have he := congrFun (BrownianPositiveKilledEndpoint.density_add_reflected x hx
      (Real.toNNReal t) (Real.toNNReal_pos.mpr ht)) y
    simp only [Pi.add_apply,indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)] at he
    rw [realDensity,if_pos ht,density_zero]
    have hp : heat t (y-x) = gaussianPDF x (Real.toNNReal t) y := by
      unfold heat heatReal gaussianPDF
      rw [gaussianPDFReal_sub,zero_add]
    have hn : heat t (x+y) = gaussianPDF (-x) (Real.toNNReal t) y := by
      unfold heat heatReal gaussianPDF
      rw [add_comm x y,gaussianPDFReal_add,zero_sub]
    rw [hp,hn]
    exact he
  · have hz : Real.toNNReal t = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_gt ht)
    simp only [realDensity,if_neg ht,heat,heatReal,hz,gaussianPDFReal_zero_var,
      Pi.zero_apply,ENNReal.ofReal_zero,add_zero]

theorem resolvent_zero_add_heatResolvent (p x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    resolvent 0 p x y+heatResolvent p (x+y) = heatResolvent p (y-x) := by
  have hk : Measurable (fun t : ℝ ↦ laplaceWeight p t*realDensity 0 t x y) :=
    (measurable_laplaceWeight p).mul ((measurable_realDensity 0).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const)))
  have hh : Measurable (fun t : ℝ ↦ laplaceWeight p t*heat t (x+y)) :=
    (measurable_laplaceWeight p).mul (measurable_heat.comp (measurable_id.prodMk measurable_const))
  unfold BrownianKilledAreaMomentResolvent.resolvent heatResolvent
  rw [← lintegral_add_aux hk hh]
  apply lintegral_congr
  intro t
  rw [← mul_add,realDensity_zero_add_heat t x y hx hy]

def greenReal (p x y : ℝ) : ℝ :=
  (Real.exp (-|y-x| * Real.sqrt (2*p))-Real.exp (-(x+y)*Real.sqrt (2*p)))/Real.sqrt (2*p)

theorem greenReal_nonneg (p x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ greenReal p x y := by
  have ha : |y-x| ≤ x+y := by
    apply abs_le.mpr
    constructor <;> linarith
  have he : Real.exp (-(x+y)*Real.sqrt (2*p)) ≤ Real.exp (-|y-x| * Real.sqrt (2*p)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg ha) (Real.sqrt_nonneg _)
  exact div_nonneg (sub_nonneg.mpr he) (Real.sqrt_nonneg _)

theorem resolvent_zero_eq_green (p : ℝ) (hp : 0 < p) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    resolvent 0 p x y = ENNReal.ofReal (greenReal p x y) := by
  have he := resolvent_zero_add_heatResolvent p x y hx hy
  rw [heatResolvent_eq p hp (x+y) (by linarith),heatResolvent_eq_abs p hp (y-x)] at he
  apply (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal (Real.exp (-|y-x| * Real.sqrt (2*p))/Real.sqrt (2*p)) := he
    _ = ENNReal.ofReal (greenReal p x y)+
        ENNReal.ofReal (Real.exp (-(x+y)*Real.sqrt (2*p))/Real.sqrt (2*p)) := by
      rw [← ENNReal.ofReal_add (greenReal_nonneg p x y hx hy) (by positivity)]
      congr 1
      unfold greenReal
      ring

def green (p x y : ℝ) : ℝ≥0∞ :=
  if 0 < x ∧ 0 < y then ENNReal.ofReal (greenReal p x y) else 0

theorem resolvent_zero_eq (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent 0 p x y = green p x y := by
  by_cases hxy : 0 < x ∧ 0 < y
  · rw [green,if_pos hxy]
    exact resolvent_zero_eq_green p hp x y hxy.1 hxy.2
  · rw [green,if_neg hxy]
    rcases not_and_or.mp hxy with hx | hy
    · exact resolvent_zero_of_nonpos_initial 0 p x y (le_of_not_gt hx)
    · exact resolvent_zero_of_nonpos_target 0 p x y (le_of_not_gt hy)

theorem resolvent_zero_ne_top (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent 0 p x y ≠ ⊤ := by
  rw [resolvent_zero_eq p hp]
  unfold green
  split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

end PerronWright.BrownianKilledGreenKernel
