import PerronWright.Probability.BrownianPositiveKilledEndpoint
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Genuine killed Brownian boundary entrance density

The density belongs to the actual positive-start killed endpoint law
proved in the preceding leaf. Differentiating its Gaussian difference
proves the true small-start entrance limit. Explicit all-positive-start
bounds supply domination on every bounded size interval. This is not a
positive bridge finite-dimensional or Vervaat distribution identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledBoundaryEntrance

open BrownianPositiveKilledEndpoint

def entranceReal (T : ℝ≥0) : ℝ → ℝ :=
  (Ioi 0).indicator (fun y ↦ 2*y/(T : ℝ)*gaussianPDFReal 0 T y)

def entrance (T : ℝ≥0) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (entranceReal T y)

theorem measurable_entranceReal (T : ℝ≥0) : Measurable (entranceReal T) := by
  unfold entranceReal
  exact ((measurable_const.mul measurable_id).div_const (T : ℝ) |>.mul
    (measurable_gaussianPDFReal 0 T)).indicator measurableSet_Ioi

theorem measurable_entrance (T : ℝ≥0) : Measurable (entrance T) :=
  (measurable_entranceReal T).ennreal_ofReal

theorem entranceReal_nonneg (T : ℝ≥0) (y : ℝ) : 0 ≤ entranceReal T y := by
  exact Set.indicator_nonneg (fun z hz ↦ mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hz.le) T.coe_nonneg)
    (gaussianPDFReal_nonneg 0 T z)) y

theorem gaussianPDFReal_mean_hasDerivAt (T : ℝ≥0) (hT : 0 < T) (y a : ℝ) :
    HasDerivAt (fun x ↦ gaussianPDFReal x T y)
      ((y-a)/(T : ℝ)*gaussianPDFReal a T y) a := by
  have h := ((((hasDerivAt_const a y).sub (hasDerivAt_id a)).pow 2).neg.div_const
    (2*(T : ℝ))).exp.const_mul (Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹
  apply h.congr_deriv
  dsimp [gaussianPDFReal]
  field_simp [ne_of_gt (show 0 < (T : ℝ) from hT)]
  ring

theorem gaussian_difference_hasDerivAt_zero (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    HasDerivAt (fun a ↦ gaussianPDFReal a T y-gaussianPDFReal (-a) T y)
      (2*y/(T : ℝ)*gaussianPDFReal 0 T y) 0 := by
  have hp := gaussianPDFReal_mean_hasDerivAt T hT y 0
  have hn := (gaussianPDFReal_mean_hasDerivAt T hT y (-0)).comp 0 (hasDerivAt_id (0 : ℝ)).neg
  apply (hp.sub hn).congr_deriv
  simp only [neg_zero,sub_zero]
  field_simp [ne_of_gt (show 0 < (T : ℝ) from hT)]
  ring

theorem densityReal_div_start_tendsto (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    Tendsto (fun a ↦ densityReal a T y/a) (𝓝[>] (0 : ℝ)) (𝓝 (entranceReal T y)) := by
  by_cases hy : 0 < y
  · have he := (gaussian_difference_hasDerivAt_zero T hT y).tendsto_slope_zero_right
    simpa only [densityReal,entranceReal,Set.indicator,mem_Ioi,if_pos hy,
      zero_add,neg_zero,sub_self,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using he
  · simp only [densityReal,entranceReal,Set.indicator,mem_Ioi,if_neg hy,zero_div]
    exact tendsto_const_nhds

theorem density_div_start_tendsto (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    Tendsto (fun a ↦ ENNReal.ofReal (densityReal a T y/a))
      (𝓝[>] (0 : ℝ)) (𝓝 (entrance T y)) :=
  ENNReal.tendsto_ofReal (densityReal_div_start_tendsto T hT y)

theorem densityReal_eq_factor (a : ℝ) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) (hy : 0 < y) :
    densityReal a T y = gaussianPDFReal a T y*(1-Real.exp (-2*a*y/(T : ℝ))) := by
  have he := BrownianKilledGaussianAlgebra.gaussianPDFReal_reflected_difference (-a) T hT (y-a)
  rw [gaussianPDFReal_sub,gaussianPDFReal_sub,zero_add,show 2*(-a)+a = -a by ring] at he
  simp only [densityReal,Set.indicator,mem_Ioi,if_pos hy]
  rw [show 2*(-a)*(y-a-(-a))/(T : ℝ) = -2*a*y/(T : ℝ) by ring] at he
  exact he

theorem gaussianPDFReal_le_prefactor (a : ℝ) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    gaussianPDFReal a T y ≤ (Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹ := by
  have he : Real.exp (-(y-a)^2/(2*(T : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem densityReal_div_start_le (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (y : ℝ) (hy : 0 < y) :
    densityReal a T y/a ≤ (2*y/(T : ℝ))*(Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹ := by
  apply (div_le_iff₀ ha).mpr
  rw [densityReal_eq_factor a T hT y hy]
  have hf : 1-Real.exp (-2*a*y/(T : ℝ)) ≤ 2*a*y/(T : ℝ) := by
    have he := Real.add_one_le_exp (-2*a*y/(T : ℝ))
    rw [show -2*a*y/(T : ℝ) = -(2*a*y/(T : ℝ)) by ring] at he
    rw [show -2*a*y/(T : ℝ) = -(2*a*y/(T : ℝ)) by ring]
    linarith
  have hn : 0 ≤ 1-Real.exp (-2*a*y/(T : ℝ)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith) T.coe_nonneg)
  calc
    _ ≤ (Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹*(2*a*y/(T : ℝ)) :=
      mul_le_mul (gaussianPDFReal_le_prefactor a T hT y) hf hn (by positivity)
    _ = _ := by ring

theorem densityReal_div_start_le_window (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (b y : ℝ) (hb : 0 ≤ b) (hy : y ≤ b) :
    densityReal a T y/a ≤ (2*b/(T : ℝ))*(Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹ := by
  by_cases hy0 : 0 < y
  · exact (densityReal_div_start_le a ha T hT y hy0).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by norm_num)) T.coe_nonneg) (by positivity))
  · simp only [densityReal,Set.indicator,mem_Ioi,if_neg hy0,zero_div]
    positivity

end PerronWright.BrownianKilledBoundaryEntrance
