import PerronWright.Probability.BrownianFirstPassageDensityGeometry
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The genuine Gaussian heat kernel as a passage-density level tail

For a fixed positive duration, integration of the explicitly differentiated
Gaussian over positive passage levels recovers the heat kernel. The
identity is deterministic and proves all integrability used in it.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianHeatPassageTail

open BrownianFirstPassageDensityGeometry

def heatReal (t x : ℝ) : ℝ := gaussianPDFReal 0 (Real.toNNReal t) x

def heat (t x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (heatReal t x)

theorem measurable_heat : Measurable (fun p : ℝ × ℝ ↦ heat p.1 p.2) := by
  unfold heat heatReal
  exact (measurable_uncurry_gaussianPDFReal.comp
    (measurable_const.prodMk ((measurable_fst.real_toNNReal).prodMk measurable_snd))).ennreal_ofReal

theorem densityReal_eq_heat (a t : ℝ) (ht : 0 < t) :
    densityReal a t = a/t*heatReal t a := by
  rw [densityReal_explicit a t ht,heatReal,gaussianPDFReal,sub_zero,
    Real.coe_toNNReal _ ht.le,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]
  have hpi : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp

theorem hasDerivAt_neg_heatReal (t : ℝ) (ht : 0 < t) (a : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -heatReal t x) (densityReal a t) a := by
  rw [densityReal_eq_heat a t ht]
  unfold heatReal
  simp only [gaussianPDFReal,sub_zero,Real.coe_toNNReal _ ht.le]
  convert! (((hasDerivAt_pow 2 a).neg.div_const (2*t)).exp.const_mul
    (1/Real.sqrt (2*Real.pi*t))).neg using 1
  · funext x
    dsimp
    ring
  · dsimp
    ring

theorem heatReal_tendsto_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (heatReal t) atTop (𝓝 0) := by
  have he : Tendsto (fun a : ℝ ↦ -(a^2)/(2*t)) atTop atBot := by
    have h := (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (show -(1/(2*t)) < 0 from neg_lt_zero.mpr (by positivity))
    convert h using 1
    funext a
    ring
  have h := (Real.tendsto_exp_atBot.comp he).const_mul (1/Real.sqrt (2*Real.pi*t))
  change Tendsto (fun a : ℝ ↦ gaussianPDFReal 0 (Real.toNNReal t) a) atTop (𝓝 0)
  simpa only [heatReal,gaussianPDFReal,sub_zero,Real.coe_toNNReal _ ht.le,mul_zero,
    Function.comp_def,one_div] using h

theorem integrableOn_level_densityReal (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun b : ℝ ↦ densityReal b t) (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun b _ ↦ hasDerivAt_neg_heatReal t ht b)
    (fun b hb ↦ densityReal_nonneg b (ha.trans hb.le) t)
    ((heatReal_tendsto_zero t ht).neg)

theorem integral_level_densityReal (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    (∫ b in Ioi a, densityReal b t) = heatReal t a := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun b _ ↦ hasDerivAt_neg_heatReal t ht b)
    (fun b hb ↦ densityReal_nonneg b (ha.trans hb.le) t)
    ((heatReal_tendsto_zero t ht).neg)
  simpa only [neg_zero,zero_sub,neg_neg] using h

theorem lintegral_level_density (t a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ b in Ioi a, density b t) = heat t a := by
  by_cases ht : 0 < t
  · change (∫⁻ b in Ioi a, ENNReal.ofReal (densityReal b t)) = ENNReal.ofReal (heatReal t a)
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_level_densityReal t ht a ha)]
    · rw [integral_level_densityReal t ht a ha]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      exact densityReal_nonneg b (ha.trans hb.le) t
  · have hz : Real.toNNReal t = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_gt ht)
    have he : (fun b : ℝ ↦ density b t) = 0 := by
      funext b
      simp only [density,densityReal_eq_zero_of_nonpos b t (le_of_not_gt ht),ENNReal.ofReal_zero]
      rfl
    rw [he]
    change (∫⁻ _b in Ioi a, (0 : ℝ≥0∞)) = heat t a
    rw [lintegral_zero]
    simp only [heat,heatReal,hz,gaussianPDFReal_zero_var,Pi.zero_apply,ENNReal.ofReal_zero]

end PerronWright.BrownianHeatPassageTail
