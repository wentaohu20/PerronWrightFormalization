import PerronWright.Probability.BrownianGaussianCenteredWeightedMoments
import PerronWright.Probability.BrownianKilledSurvivalMoment
import PerronWright.Probability.BrownianPositiveBridgeBoundaryKernelBounds

/-! # Boundary-centered fourth moment of the genuine entrance kernel

This estimate is uniform over all positive starts and all positive times.
The two cases compare the start with the square root of the time; only
proved killed-Gaussian and actual Gaussian moment bounds are used.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledCenteredEntranceMoments

open BrownianPositiveKilledEndpoint BrownianKilledSurvivalMoment
open BrownianGaussianCenteredWeightedMoments BrownianPositiveBridgeTwoPointKernelBounds

def entranceFourthCoefficient : ℝ := centeredCoefficient 4+centeredCoefficient 5+
  4*centeredCoefficient 4+4*centeredCoefficient 6

theorem entranceFourthCoefficient_nonneg : 0 ≤ entranceFourthCoefficient := by
  have h4 := centeredCoefficient_nonneg 4
  have h5 := centeredCoefficient_nonneg 5
  have h6 := centeredCoefficient_nonneg 6
  unfold entranceFourthCoefficient
  positivity

theorem gaussian_positive_weight_fourth_real_bound (x : ℝ) (hx : 0 ≤ x)
    (s : ℝ≥0) (hs : 0 < s) :
    (∫⁻ y : ℝ, gaussianPDF x s y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) ≤
      ENNReal.ofReal (x*(s : ℝ)^2*centeredCoefficient 4+
        (s : ℝ)^2*Real.sqrt (s : ℝ)*centeredCoefficient 5) := by
  have h4 := centeredCoefficient_nonneg 4
  have h5 := centeredCoefficient_nonneg 5
  have he : ENNReal.ofReal (x*(s : ℝ)^2*centeredCoefficient 4+
      (s : ℝ)^2*Real.sqrt (s : ℝ)*centeredCoefficient 5) =
      ENNReal.ofReal x*centeredBound s 4+centeredBound s 5 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity : 0 ≤ x*(s : ℝ)^2),
      ENNReal.ofReal_mul hx,ENNReal.ofReal_mul (by positivity : 0 ≤ (s : ℝ)^2*Real.sqrt (s : ℝ)),
      ENNReal.ofReal_mul (sq_nonneg _),centeredBound_fourth,centeredBound_fifth]
    simp only [mul_assoc]
  rw [he]
  exact positive_weight_centered_fourth_bound x hx s hs

theorem gaussian_square_weight_fourth_real_bound (x : ℝ) (s : ℝ≥0) (hs : 0 < s) :
    (∫⁻ y : ℝ, gaussianPDF x s y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-x|^4)) ≤
      ENNReal.ofReal (2*x^2*(s : ℝ)^2*centeredCoefficient 4+
        2*(s : ℝ)^3*centeredCoefficient 6) := by
  have h4 := centeredCoefficient_nonneg 4
  have h6 := centeredCoefficient_nonneg 6
  have he : ENNReal.ofReal (2*x^2*(s : ℝ)^2*centeredCoefficient 4+
      2*(s : ℝ)^3*centeredCoefficient 6) =
      ENNReal.ofReal (2*x^2)*centeredBound s 4+2*centeredBound s 6 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2*x^2*(s : ℝ)^2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2*x^2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(s : ℝ)^3),
      centeredBound_fourth,centeredBound_sixth]
    have he2 : ENNReal.ofReal (2*(s : ℝ)^3) = 2*ENNReal.ofReal ((s : ℝ)^3) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    rw [he2]
    simp only [mul_assoc]
  rw [he]
  exact square_weight_centered_fourth_bound x s hs

theorem normalized_entrance_centered_fourth_bound (a : ℝ) (ha : 0 < a)
    (s : ℝ≥0) (hs : 0 < s) :
    (∫⁻ y : ℝ, (density a s y/ENNReal.ofReal a)*ENNReal.ofReal y*
      ENNReal.ofReal (|y-a|^4)) ≤ ENNReal.ofReal ((s : ℝ)^2*entranceFourthCoefficient) := by
  have hsR : (0 : ℝ) < s := hs
  have hroot := Real.sqrt_pos.mpr hsR
  have hsq : (Real.sqrt (s : ℝ))^2 = (s : ℝ) := Real.sq_sqrt s.property
  have h4 := centeredCoefficient_nonneg 4
  have h5 := centeredCoefficient_nonneg 5
  have h6 := centeredCoefficient_nonneg 6
  by_cases hlarge : Real.sqrt (s : ℝ) ≤ a
  · have hm : Measurable (fun y : ℝ ↦ gaussianPDF a s y*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4)) := by fun_prop
    calc
      _ ≤ ∫⁻ y : ℝ, (gaussianPDF a s y*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4))/ENNReal.ofReal a := by
        apply lintegral_mono
        intro y
        simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using
          mul_le_mul' (mul_le_mul' (ENNReal.div_le_div_right (density_le_gaussian a y s) _) le_rfl) (le_refl (ENNReal.ofReal (|y-a|^4)))
      _ = (∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4))/ENNReal.ofReal a := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const _ hm
      _ ≤ ENNReal.ofReal (a*(s : ℝ)^2*centeredCoefficient 4+
          (s : ℝ)^2*Real.sqrt (s : ℝ)*centeredCoefficient 5)/ENNReal.ofReal a :=
        ENNReal.div_le_div_right (gaussian_positive_weight_fourth_real_bound a ha.le s hs) _
      _ = ENNReal.ofReal ((a*(s : ℝ)^2*centeredCoefficient 4+
          (s : ℝ)^2*Real.sqrt (s : ℝ)*centeredCoefficient 5)/a) :=
        (ENNReal.ofReal_div_of_pos ha).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ ha).mpr
        unfold entranceFourthCoefficient
        have he := mul_le_mul_of_nonneg_left hlarge (mul_nonneg (sq_nonneg (s : ℝ)) h5)
        nlinarith [mul_nonneg (mul_nonneg ha.le (sq_nonneg (s : ℝ))) h4,
          mul_nonneg (mul_nonneg ha.le (sq_nonneg (s : ℝ))) h6]
  · have hsmall : a ≤ Real.sqrt (s : ℝ) := (lt_of_not_ge hlarge).le
    have hasq : a^2 ≤ (s : ℝ) := by nlinarith
    have hm : Measurable (fun y : ℝ ↦ gaussianPDF a s y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-a|^4)) := by fun_prop
    have hpoint (y : ℝ) : (density a s y/ENNReal.ofReal a)*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4) ≤
        ENNReal.ofReal (2/(s : ℝ))*(gaussianPDF a s y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-a|^4)) := by
      have hb := mul_le_mul' (mul_le_mul' (normalized_density_le_first_gaussian a ha s hs y) (le_refl (ENNReal.ofReal y)))
        (le_refl (ENNReal.ofReal (|y-a|^4)))
      have hy : ENNReal.ofReal |y| * ENNReal.ofReal y ≤ ENNReal.ofReal (y^2) := by
        rcases le_total 0 y with hy | hy
        · rw [abs_of_nonneg hy,← ENNReal.ofReal_mul hy,pow_two]
        · rw [ENNReal.ofReal_eq_zero.mpr hy,mul_zero]; exact zero_le
      calc
        _ ≤ _ := hb
        _ = ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y*
            (ENNReal.ofReal |y| * ENNReal.ofReal y)*ENNReal.ofReal (|y-a|^4) := by ac_rfl
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul'
            (mul_le_mul' (le_refl (ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y)) hy) le_rfl
    calc
      _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2/(s : ℝ))*
          (gaussianPDF a s y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-a|^4)) := lintegral_mono hpoint
      _ = ENNReal.ofReal (2/(s : ℝ))*(∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-a|^4)) :=
        lintegral_const_mul _ hm
      _ ≤ ENNReal.ofReal (2/(s : ℝ))*ENNReal.ofReal (2*a^2*(s : ℝ)^2*centeredCoefficient 4+
          2*(s : ℝ)^3*centeredCoefficient 6) :=
        mul_le_mul' le_rfl (gaussian_square_weight_fourth_real_bound a s hs)
      _ = ENNReal.ofReal ((2/(s : ℝ))*(2*a^2*(s : ℝ)^2*centeredCoefficient 4+
          2*(s : ℝ)^3*centeredCoefficient 6)) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : (2/(s : ℝ))*(2*a^2*(s : ℝ)^2*centeredCoefficient 4+
            2*(s : ℝ)^3*centeredCoefficient 6) =
            4*a^2*(s : ℝ)*centeredCoefficient 4+4*(s : ℝ)^2*centeredCoefficient 6 := by
          field_simp [ne_of_gt hsR]
          ring
        rw [he]
        have hm4 := mul_le_mul_of_nonneg_right hasq (mul_nonneg (by positivity : 0 ≤ 4*(s : ℝ)) h4)
        unfold entranceFourthCoefficient
        nlinarith [mul_nonneg (sq_nonneg (s : ℝ)) h4,mul_nonneg (sq_nonneg (s : ℝ)) h5]

end PerronWright.BrownianKilledCenteredEntranceMoments
