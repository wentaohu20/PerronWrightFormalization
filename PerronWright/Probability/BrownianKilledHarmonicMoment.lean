import PerronWright.Probability.BrownianPositiveKilledEndpoint

/-! # Genuine first harmonic moment of the positive killed Brownian kernel

The actual killed endpoint law is obtained from Brownian path survival.
Its first positive moment is exactly its initial point. This follows
from the proved reflection identity and the actual Gaussian mean and
reflection laws, not an assumed martingale or Doob transform interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledHarmonicMoment

open BrownianPositiveKilledEndpoint

theorem gaussian_id_integrable (a : ℝ) (t : ℝ≥0) :
    Integrable (fun y : ℝ ↦ y) (gaussianReal a t) :=
  memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by norm_num))

theorem positive_part_gaussian_mean (a : ℝ) (t : ℝ≥0) :
    (∫ y : ℝ, max y 0 ∂gaussianReal a t)-
      (∫ y : ℝ, max y 0 ∂gaussianReal (-a) t) = a := by
  have he : (∫ y : ℝ, max y 0 ∂gaussianReal (-a) t) =
      ∫ y : ℝ, max (-y) 0 ∂gaussianReal a t := by
    rw [← gaussianReal_map_neg,integral_map (by fun_prop) (by fun_prop)]
  rw [he,← integral_sub (gaussian_id_integrable a t).pos_part (gaussian_id_integrable a t).neg_part]
  have hf : (fun y : ℝ ↦ max y 0-max (-y) 0) = fun y ↦ y := by
    funext y
    rcases le_total 0 y with hy | hy
    · rw [max_eq_left hy,max_eq_right (neg_nonpos.mpr hy),sub_zero]
    · rw [max_eq_right hy,max_eq_left (neg_nonneg.mpr hy),zero_sub,neg_neg]
  rw [hf,integral_id_gaussianReal]

theorem lintegral_positive_gaussian (a : ℝ) (t : ℝ≥0) :
    (∫⁻ y : ℝ, ENNReal.ofReal y ∂gaussianReal a t) =
      ENNReal.ofReal (∫ y : ℝ, max y 0 ∂gaussianReal a t) := by
  have hfun : (fun y : ℝ ↦ ENNReal.ofReal y) = fun y ↦ ENNReal.ofReal (max y 0) := by
    funext y
    rcases le_total 0 y with hy | hy
    · rw [max_eq_left hy]
    · rw [max_eq_right hy,ENNReal.ofReal_zero,ENNReal.ofReal_eq_zero.mpr hy]
  rw [hfun,← ofReal_integral_eq_lintegral_ofReal (gaussian_id_integrable a t).pos_part
    (ae_of_all _ (fun y : ℝ ↦ le_max_right y 0))]

theorem setLIntegral_positive_part (μ : Measure ℝ) :
    (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal y ∂μ) = ∫⁻ y : ℝ, ENNReal.ofReal y ∂μ := by
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro y
  by_cases hy : 0 < y
  · rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
  · rw [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hy)]

theorem law_first_moment (a : ℝ) (ha : 0 < a) (t : ℝ≥0) :
    (∫⁻ y : ℝ, ENNReal.ofReal y ∂law a t) = ENNReal.ofReal a := by
  have he := congrArg (fun μ : Measure ℝ ↦ ∫⁻ y : ℝ, ENNReal.ofReal y ∂μ)
    (law_add_reflected a ha t)
  rw [lintegral_add_measure,setLIntegral_positive_part,setLIntegral_positive_part,
    lintegral_positive_gaussian,lintegral_positive_gaussian] at he
  have hpos : 0 ≤ ∫ y : ℝ, max y 0 ∂gaussianReal (-a) t :=
    integral_nonneg (fun y ↦ le_max_right y 0)
  have hm := positive_part_gaussian_mean a t
  have hsum : ENNReal.ofReal (∫ y : ℝ, max y 0 ∂gaussianReal a t) =
      ENNReal.ofReal a+ENNReal.ofReal (∫ y : ℝ, max y 0 ∂gaussianReal (-a) t) := by
    rw [show (∫ y : ℝ, max y 0 ∂gaussianReal a t) =
      a+(∫ y : ℝ, max y 0 ∂gaussianReal (-a) t) by linarith,ENNReal.ofReal_add ha.le hpos]
  rw [hsum] at he
  exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp he

theorem density_first_moment (a : ℝ) (ha : 0 < a) (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ y : ℝ, ENNReal.ofReal y*density a t y) = ENNReal.ofReal a := by
  have hm : Measurable (fun y : ℝ ↦ ENNReal.ofReal y) := measurable_id.ennreal_ofReal
  have he := law_first_moment a ha t
  rw [law_eq_withDensity a ha t ht,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density a t) hm] at he
  simpa only [Pi.mul_apply,mul_comm] using he

theorem normalized_density_first_moment (a : ℝ) (ha : 0 < a) (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ y : ℝ, ENNReal.ofReal y*(density a t y/ENNReal.ofReal a)) = 1 := by
  have hm : Measurable (fun y : ℝ ↦ ENNReal.ofReal y*density a t y) :=
    measurable_id.ennreal_ofReal.mul (measurable_density a t)
  simp only [div_eq_mul_inv,← mul_assoc]
  rw [lintegral_mul_const _ hm,density_first_moment a ha t ht]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top

end PerronWright.BrownianKilledHarmonicMoment
