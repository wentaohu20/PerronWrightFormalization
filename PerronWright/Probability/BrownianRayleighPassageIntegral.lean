import PerronWright.Probability.BrownianMinimumFutureEndpointLaw
import PerronWright.Probability.BrownianFirstPassageDensityGeometry
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Exact integration of the genuine endpoint/passage mixture

The positive-height mixture is computed by the proved Gamma integral.
Both integrability and the numerical normalization are derived here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianRayleighPassageIntegral

open BrownianMinimumFutureEndpointLaw BrownianFirstPassageDensityGeometry

theorem integral_gaussian_square_Ioi (b : ℝ) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), x^2*Real.exp (-b*x^2)) =
      Real.sqrt Real.pi/(4*b*Real.sqrt b) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ))
    (q := (2 : ℝ)) (by norm_num) (by norm_num) hb
  simp only [Real.rpow_two] at h
  have hg : Real.Gamma (3/2 : ℝ) = Real.sqrt Real.pi/2 := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0),Real.Gamma_one_half_eq]
    ring
  have hp : b ^ (-(2+1)/2 : ℝ) = (b*Real.sqrt b)⁻¹ := by
    rw [show (-(2+1)/2 : ℝ) = -(1+1/2) by norm_num,
      Real.rpow_neg hb.le,Real.rpow_add hb,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hp,show ((2+1)/2 : ℝ) = 3/2 by norm_num,hg] at h
  rw [h]
  ring

private theorem rayleigh_density_product (x s : ℝ) (hx : 0 < x) (hs : 0 < s) :
    endpointDensity x*density x s = ENNReal.ofReal
      ((Real.sqrt (2*Real.pi)*s*Real.sqrt s)⁻¹ *
        (x^2*Real.exp (-((1+s)/(2*s))*x^2))) := by
  unfold endpointDensity density
  rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),densityReal_explicit x s hs,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : -x^2/2 + -x^2/(2*s) = -((1+s)/(2*s))*x^2 := by
    field_simp
    ring
  calc
    _ = (Real.sqrt (2*Real.pi)*s*Real.sqrt s)⁻¹*x^2*
        (Real.exp (-x^2/2)*Real.exp (-x^2/(2*s))) := by ring
    _ = _ := by rw [← Real.exp_add,he]; ring

theorem lintegral_endpoint_passage (s : ℝ) (hs : 0 < s) :
    (∫⁻ x : ℝ, endpointDensity x*density x s) =
      ENNReal.ofReal (1/(2*(1+s)*Real.sqrt (1+s))) := by
  let b : ℝ := (1+s)/(2*s)
  have hb : 0 < b := by dsimp [b]; positivity
  let c : ℝ := (Real.sqrt (2*Real.pi)*s*Real.sqrt s)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi : IntegrableOn (fun x : ℝ ↦ c*(x^2*Real.exp (-b*x^2))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num)
    simp only [Real.rpow_two] at h
    exact h.const_mul c
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (c*(x^2*Real.exp (-b*x^2))) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro x
      by_cases hx : 0 < x
      · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
        exact rayleigh_density_product x s hx hs
      · simp [endpointDensity,indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    _ = ENNReal.ofReal (c*(Real.sqrt Real.pi/(4*b*Real.sqrt b))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (fun _ ↦ mul_nonneg hc (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))),
        integral_const_mul,integral_gaussian_square_Ioi b hb]
    _ = _ := by
      congr 1
      have hsqrt : Real.sqrt b = Real.sqrt (1+s)/(Real.sqrt 2*Real.sqrt s) := by
        dsimp [b]
        rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsqrt]
      dsimp [b,c]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have htwo : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hs2 : (Real.sqrt s)^2 = s := Real.sq_sqrt hs.le
      have hn2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hns : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
      have hnpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
      have hnplus : Real.sqrt (1+s) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp
      nlinarith

theorem lintegral_endpoint_passage_nonpositive (s : ℝ) (hs : s ≤ 0) :
    (∫⁻ x : ℝ, endpointDensity x*density x s) = 0 := by
  simp only [density,densityReal_eq_zero_of_nonpos _ _ hs,ENNReal.ofReal_zero,mul_zero,lintegral_zero]

end PerronWright.BrownianRayleighPassageIntegral
