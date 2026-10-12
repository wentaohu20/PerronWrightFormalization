import PerronWright.Probability.BrownianPositiveBridgeBoundaryIncrementMoments
import PerronWright.Probability.BrownianPositiveBridgeBoundaryCenteredMoments

/-! # All actual left-side increments, including the initial endpoint

Two genuine kernel estimates cover the two geometric cases `h ≤ s`
and `s < h`. The latter uses fourth moments centered at the actual
bridge endpoint, with the elementary fourth-power triangle inequality.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeLeftIncrementMoments

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeBoundaryIncrementMoments BrownianPositiveBridgeBoundaryCenteredMoments

def leftCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  fourthBoundaryCoefficient δ T+40*centeredBoundaryCoefficient δ T

theorem leftCoefficient_ne_top (δ T : ℝ≥0) (hT : 0 < T) : leftCoefficient δ T ≠ ∞ :=
  ENNReal.add_ne_top.mpr ⟨fourthBoundaryCoefficient_ne_top δ T hT,
    ENNReal.mul_ne_top (by norm_num) (centeredBoundaryCoefficient_ne_top δ T hT)⟩

theorem fourth_triangle_centered (x y a : ℝ) :
    ENNReal.ofReal (‖y-x‖^4) ≤ 8*(ENNReal.ofReal (‖y-a‖^4)+ENNReal.ofReal (‖x-a‖^4)) := by
  have htriangle : ‖y-x‖ ≤ ‖y-a‖+‖x-a‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (y-a) (x-a)
  have hpow := (pow_le_pow_left₀ (norm_nonneg _) htriangle 4).trans
    (add_pow_le (norm_nonneg (y-a)) (norm_nonneg (x-a)) 4)
  have hb : ‖y-x‖^4 ≤ 8*(‖y-a‖^4+‖x-a‖^4) := by norm_num at hpow ⊢; exact hpow
  have he : ENNReal.ofReal (8*(‖y-a‖^4+‖x-a‖^4)) =
      8*(ENNReal.ofReal (‖y-a‖^4)+ENNReal.ofReal (‖x-a‖^4)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [← he]
  exact ENNReal.ofReal_le_ofReal hb

theorem increment_le_centered_moments (μ : Measure Path) (a : ℝ) (s h : ℝ≥0) :
    (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂μ) ≤
      8*((∫⁻ g, ENNReal.ofReal (‖g (s+h)-a‖^4) ∂μ)+
        (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂μ)) := by
  have hm1 : Measurable (fun g : Path ↦ ENNReal.ofReal (‖g (s+h)-a‖^4)) :=
    ((continuous_eval (s+h)).measurable.sub_const a |>.norm.pow_const 4).ennreal_ofReal
  have hm2 : Measurable (fun g : Path ↦ ENNReal.ofReal (‖g s-a‖^4)) :=
    ((continuous_eval s).measurable.sub_const a |>.norm.pow_const 4).ennreal_ofReal
  calc
    _ ≤ ∫⁻ g : Path, 8*(ENNReal.ofReal (‖g (s+h)-a‖^4)+ENNReal.ofReal (‖g s-a‖^4)) ∂μ :=
      lintegral_mono (fun g ↦ fourth_triangle_centered (g s) (g (s+h)) a)
    _ = _ := by
      have hm : Measurable (fun g : Path ↦ ENNReal.ofReal (‖g (s+h)-a‖^4)+ENNReal.ofReal (‖g s-a‖^4)) := hm1.add hm2
      rw [lintegral_const_mul _ hm,lintegral_add_left hm1]

theorem eventually_uniform_left_fourth_increment (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), δ ≤ t → s+h+t = T →
      (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a T) ≤
        leftCoefficient δ T*ENNReal.ofReal ((h : ℝ)^2) := by
  filter_upwards [eventually_uniform_boundary_fourth_increment δ T hδ hT,
    eventually_uniform_boundary_centered_fourth δ T hδ hT] with a hinc hcenter
  intro s h t ht hsum
  by_cases hh : h = 0
  · simp only [hh,add_zero,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),
      ENNReal.ofReal_zero,lintegral_zero,NNReal.coe_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,le_refl]
  have hhpos : 0 < h := (zero_le : (0 : ℝ≥0) ≤ h).lt_of_ne (Ne.symm hh)
  by_cases hhs : h ≤ s
  · have hs : 0 < s := hhpos.trans_le hhs
    exact (hinc s h t hs hhs ht hsum).trans (mul_le_mul'
      (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ 40*centeredBoundaryCoefficient δ T)) le_rfl)
  · have hsh : s ≤ h := (lt_of_not_ge hhs).le
    have ht' : δ ≤ h+t := ht.trans (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ h))
    have hsum' : s+(h+t) = T := by simpa only [add_assoc] using hsum
    have hb1 := hcenter (s+h) t ht hsum
    have hb2 := hcenter s (h+t) ht' hsum'
    have hsmall : ENNReal.ofReal ((s : ℝ)^2) ≤ ENNReal.ofReal ((h : ℝ)^2) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ s.property hsh 2)
    have hlarge : ENNReal.ofReal ((s+h : ℝ≥0)^2 : ℝ) ≤ 4*ENNReal.ofReal ((h : ℝ)^2) := by
      have hb : ((s+h : ℝ≥0) : ℝ)^2 ≤ 4*(h : ℝ)^2 := by
        have hshR : (s : ℝ) ≤ h := hsh
        simp only [NNReal.coe_add]
        nlinarith [s.property,h.property]
      have he : ENNReal.ofReal (4*(h : ℝ)^2) = 4*ENNReal.ofReal ((h : ℝ)^2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),ENNReal.ofReal_ofNat]
      rw [← he]
      exact ENNReal.ofReal_le_ofReal hb
    calc
      _ ≤ 8*((∫⁻ g, ENNReal.ofReal (‖g (s+h)-a‖^4) ∂positiveBridgeLaw a T)+
          (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a T)) :=
        increment_le_centered_moments _ a s h
      _ ≤ 8*(centeredBoundaryCoefficient δ T*(4*ENNReal.ofReal ((h : ℝ)^2))+
          centeredBoundaryCoefficient δ T*ENNReal.ofReal ((h : ℝ)^2)) :=
        mul_le_mul' le_rfl (add_le_add (hb1.trans (mul_le_mul' le_rfl hlarge))
          (hb2.trans (mul_le_mul' le_rfl hsmall)))
      _ = (40*centeredBoundaryCoefficient δ T)*ENNReal.ofReal ((h : ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul' (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ fourthBoundaryCoefficient δ T)) le_rfl

end PerronWright.BrownianPositiveBridgeLeftIncrementMoments
