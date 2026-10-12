import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The first-passage Gaussian change of variables

These are deterministic derivative and image identities on positive real
times. They prove the candidate density's integrals, without assuming any
probability law or first-passage density identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageDensityGeometry

def argument (a t : ℝ) : ℝ := -a / Real.sqrt t

def densityReal (a : ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun t ↦ a / (t * Real.sqrt t) * gaussianPDFReal 0 1 (argument a t))

def density (a t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (densityReal a t)

theorem measurable_densityReal (a : ℝ) : Measurable (densityReal a) := by
  unfold densityReal argument
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

theorem measurable_density (a : ℝ) : Measurable (density a) :=
  ENNReal.measurable_ofReal.comp (measurable_densityReal a)

theorem densityReal_eq_zero_of_nonpos (a t : ℝ) (ht : t ≤ 0) : densityReal a t = 0 := by
  exact indicator_of_notMem (show t ∉ Ioi 0 from not_lt.mpr ht) _

theorem densityReal_nonneg (a : ℝ) (ha : 0 ≤ a) (t : ℝ) : 0 ≤ densityReal a t := by
  by_cases ht : 0 < t
  · rw [densityReal,indicator_of_mem (show t ∈ Ioi 0 from ht)]
    exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)
  · rw [densityReal_eq_zero_of_nonpos a t (le_of_not_gt ht)]

theorem densityReal_explicit (a t : ℝ) (ht : 0 < t) :
    densityReal a t = a / (Real.sqrt (2*Real.pi) * t * Real.sqrt t) *
      Real.exp (-a^2/(2*t)) := by
  have he : -(argument a t - 0)^2 / (2 * (1 : ℝ≥0)) = -a^2/(2*t) := by
    simp only [argument,sub_zero,NNReal.coe_one,mul_one,div_pow,neg_sq,Real.sq_sqrt ht.le]
    ring
  rw [densityReal,indicator_of_mem (show t ∈ Ioi 0 from ht),gaussianPDFReal,he]
  simp only [NNReal.coe_one,mul_one,div_eq_mul_inv,mul_inv_rev]
  ring

theorem densityReal_explicit_rpow (a t : ℝ) (ht : 0 < t) :
    densityReal a t = a / (Real.sqrt (2*Real.pi) * t ^ (3/2 : ℝ)) *
      Real.exp (-a^2/(2*t)) := by
  have hp : t ^ (3/2 : ℝ) = t*Real.sqrt t := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [densityReal_explicit a t ht,hp,mul_assoc]

theorem argument_inverse (a : ℝ) (ha : 0 < a) (y : ℝ) (hy : y < 0) :
    argument a ((a / y)^2) = y := by
  have ha0 : a ≠ 0 := ha.ne'
  have hy0 : y ≠ 0 := hy.ne
  have hq : a/y < 0 := div_neg_of_pos_of_neg ha hy
  rw [argument,Real.sqrt_sq_eq_abs,abs_of_neg hq]
  field_simp

theorem argument_injOn (a : ℝ) (ha : 0 < a) : InjOn (argument a) (Ioi 0) := by
  intro x hx y hy he
  have hx0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hy0 : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  unfold argument at he
  have hs : Real.sqrt x = Real.sqrt y := by
    have hc := (div_eq_div_iff hx0 hy0).mp he
    nlinarith
  have h := congrArg (fun r : ℝ ↦ r^2) hs
  simpa only [Real.sq_sqrt hx.le,Real.sq_sqrt hy.le] using h

theorem hasDerivAt_argument (a : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (argument a) (a / (2*t*Real.sqrt t)) t := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h := (hasDerivAt_const t (-a)).div (Real.hasDerivAt_sqrt ht.ne') hs
  have he : (0 * Real.sqrt t - -a*(1/(2*Real.sqrt t)))/(Real.sqrt t)^2 =
      a/(2*t*Real.sqrt t) := by
    rw [zero_mul,zero_sub,Real.sq_sqrt ht.le]
    field_simp
  rw [he] at h
  exact h

theorem argument_image_initial (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 < T) :
    argument a '' (Ioi 0 ∩ Iic T) = Iic (argument a T) := by
  ext y
  constructor
  · rintro ⟨t,⟨ht,htT⟩,rfl⟩
    have hs := Real.sqrt_le_sqrt htT
    unfold argument
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr hT)).mpr
    nlinarith
  · intro hy
    have harg : argument a T < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) (Real.sqrt_pos.mpr hT)
    have hy0 : y < 0 := lt_of_le_of_lt hy harg
    refine ⟨(a/y)^2,⟨sq_pos_of_ne_zero (div_ne_zero ha.ne' hy0.ne),?_⟩,
      argument_inverse a ha y hy0⟩
    have ht : 0 < (a/y)^2 := sq_pos_of_ne_zero (div_ne_zero ha.ne' hy0.ne)
    have hi := argument_inverse a ha y hy0
    rw [← hi] at hy
    have hc := (div_le_div_iff₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr hT)).mp hy
    have hs : Real.sqrt ((a/y)^2) ≤ Real.sqrt T := by nlinarith
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg ((a/y)^2)) hs
    change (a/y)^2 ≤ T
    simpa only [Real.mul_self_sqrt ht.le,Real.mul_self_sqrt hT.le] using hsq

theorem density_jacobian (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 < t) :
    density a t = 2 * ENNReal.ofReal (|a/(2*t*Real.sqrt t)|) *
      gaussianPDF 0 1 (argument a t) := by
  have hp : 0 ≤ a/(2*t*Real.sqrt t) := by positivity
  have he : a/(t*Real.sqrt t) = 2*(a/(2*t*Real.sqrt t)) := by field_simp
  simp only [density,densityReal,Set.indicator_of_mem (show t ∈ Ioi 0 from ht),
    abs_of_nonneg hp,gaussianPDF]
  rw [he,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_ofNat]

theorem density_integral_Iic (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 < T) :
    ∫⁻ t in Iic T, density a t = 2 * gaussianReal 0 1 (Iic (argument a T)) := by
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioi 0 ∩ Iic T)
    (measurableSet_Ioi.inter measurableSet_Iic)
    (fun t ht ↦ (hasDerivAt_argument a t ht.1).hasDerivWithinAt)
    ((argument_injOn a ha).mono inter_subset_left) (gaussianPDF 0 1)
  rw [argument_image_initial a ha T hT] at hj
  have hg : gaussianReal 0 1 (Iic (argument a T)) =
      ∫⁻ x in Iic (argument a T), gaussianPDF 0 1 x := by
    exact gaussianReal_apply 0 (by norm_num : (1 : ℝ≥0) ≠ 0) _
  rw [hg,hj,← lintegral_const_mul' 2 _ (by norm_num)]
  rw [← setLIntegral_indicator measurableSet_Ioi]
  apply setLIntegral_congr_fun measurableSet_Iic
  intro t ht
  by_cases hp : 0 < t
  · simp only [indicator_of_mem (show t ∈ Ioi 0 from hp)]
    simpa only [mul_assoc] using density_jacobian a ha t hp
  · simp only [indicator_of_notMem (show t ∉ Ioi 0 from hp),density,densityReal,ENNReal.ofReal_zero]

end PerronWright.BrownianFirstPassageDensityGeometry
