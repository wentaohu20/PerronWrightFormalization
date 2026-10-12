import PerronWright.Probability.BrownianPositiveBridgeIncrementMoments
import PerronWright.Probability.BrownianPositiveBridgeAllTimeMoments

/-! # Genuine time reversal of positive-bridge fourth moments

The identity is derived from actual one- and two-point laws and the
symmetric killed Gaussian density. Endpoint cases use the proved actual
endpoint values, so there is no bridge-reversibility interface premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMomentReversal

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianPositiveBridgeTwoPointKernelBounds BrownianPositiveBridgeIncrementMoments
open BrownianPositiveBridgeAllTimeMoments

theorem endpoint_centered_fourth_zero (a : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (s : ℝ≥0) (hs : s = 0 ∨ s = T) :
    (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a T) = 0 := by
  calc
    _ = ∫⁻ _ : Path, (0 : ℝ≥0∞) ∂positiveBridgeLaw a T := by
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
      rcases hs with rfl | rfl <;>
        simp only [hg.1,hg.2,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),ENNReal.ofReal_zero]
    _ = 0 := lintegral_zero

theorem actual_centered_fourth_time_reversal (a : ℝ) (ha : 0 < a) (s t : ℝ≥0) (hT : 0 < s+t) :
    (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a (s+t)) =
      ∫⁻ g, ENNReal.ofReal (‖g t-a‖^4) ∂positiveBridgeLaw a (s+t) := by
  by_cases hs : s = 0
  · rw [endpoint_centered_fourth_zero a (s+t) hT s (Or.inl hs),
      endpoint_centered_fourth_zero a (s+t) hT t (Or.inr (by rw [hs,zero_add]))]
  by_cases ht : t = 0
  · rw [endpoint_centered_fourth_zero a (s+t) hT s (Or.inr (by rw [ht,add_zero])),
      endpoint_centered_fourth_zero a (s+t) hT t (Or.inl ht)]
  have hspos : 0 < s := (zero_le : (0 : ℝ≥0) ≤ s).lt_of_ne (Ne.symm hs)
  have htpos : 0 < t := (zero_le : (0 : ℝ≥0) ≤ t).lt_of_ne (Ne.symm ht)
  have hΦ : Measurable (fun y : ℝ ↦ ENNReal.ofReal (‖y-a‖^4)) := by fun_prop
  have hleft := onePoint_lintegral a ha s t hspos htpos _ hΦ
  have hright := onePoint_lintegral a ha t s htpos hspos _ hΦ
  rw [add_comm t s] at hright
  rw [hleft,hright]
  exact lintegral_congr (fun y ↦ by rw [onePointDensity_time_symm a s t hspos htpos y])

theorem twoPointDensity_time_symm (a : ℝ) (s h t : ℝ≥0)
    (hs : 0 < s) (hh : 0 < h) (ht : 0 < t) (x y : ℝ) :
    twoPointDensity a s h t x y = twoPointDensity a t h s y x := by
  have hsum : s+h+t = t+h+s := by ac_rfl
  unfold twoPointDensity
  rw [hsum,density_symm a x s hs,density_symm x y h hh,density_symm y a t ht]
  ac_rfl

theorem actual_fourth_increment_time_reversal (a : ℝ) (ha : 0 < a)
    (s h t : ℝ≥0) (hT : 0 < s+h+t) :
    (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a (s+h+t)) =
      ∫⁻ g, ENNReal.ofReal (‖g (t+h)-g t‖^4) ∂positiveBridgeLaw a (s+h+t) := by
  have hsum : t+h+s = s+h+t := by ac_rfl
  by_cases hh : h = 0
  · simp only [hh,add_zero,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),ENNReal.ofReal_zero,lintegral_zero]
  have hhpos : 0 < h := (zero_le : (0 : ℝ≥0) ≤ h).lt_of_ne (Ne.symm hh)
  by_cases hs : s = 0
  · have hleft : (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a (s+h+t)) =
        ∫⁻ g, ENNReal.ofReal (‖g h-a‖^4) ∂positiveBridgeLaw a (h+t) := by
      rw [hs,zero_add]
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_endpoints a (h+t) (by simpa only [hs,zero_add] using hT)] with g hg
      rw [hg.1]
    have hright : (∫⁻ g, ENNReal.ofReal (‖g (t+h)-g t‖^4) ∂positiveBridgeLaw a (s+h+t)) =
        ∫⁻ g, ENNReal.ofReal (‖g t-a‖^4) ∂positiveBridgeLaw a (h+t) := by
      rw [hs,zero_add]
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_endpoints a (h+t) (by simpa only [hs,zero_add] using hT)] with g hg
      rw [add_comm t h,hg.2,norm_sub_rev]
    rw [hleft,hright]
    exact actual_centered_fourth_time_reversal a ha h t (by simpa only [hs,zero_add] using hT)
  by_cases ht : t = 0
  · have hleft : (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a (s+h+t)) =
        ∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a (s+h) := by
      rw [ht,add_zero]
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_endpoints a (s+h) (by simpa only [ht,add_zero] using hT)] with g hg
      rw [hg.2,norm_sub_rev]
    have hright : (∫⁻ g, ENNReal.ofReal (‖g (t+h)-g t‖^4) ∂positiveBridgeLaw a (s+h+t)) =
        ∫⁻ g, ENNReal.ofReal (‖g h-a‖^4) ∂positiveBridgeLaw a (s+h) := by
      rw [ht,zero_add,add_zero]
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_endpoints a (s+h) (by simpa only [ht,add_zero] using hT)] with g hg
      rw [hg.1]
    rw [hleft,hright]
    exact actual_centered_fourth_time_reversal a ha s h (by simpa only [ht,add_zero] using hT)
  have hspos : 0 < s := (zero_le : (0 : ℝ≥0) ≤ s).lt_of_ne (Ne.symm hs)
  have htpos : 0 < t := (zero_le : (0 : ℝ≥0) ≤ t).lt_of_ne (Ne.symm ht)
  have hΦ : Measurable (fun p : ℝ×ℝ ↦ ENNReal.ofReal (‖p.2-p.1‖^4)) := by fun_prop
  have hleft := actual_twoPoint_lintegral a ha s h t hspos hhpos htpos _ hΦ
  have hright := actual_twoPoint_lintegral a ha t h s htpos hhpos hspos _ hΦ
  rw [hsum] at hright
  rw [hleft,hright]
  have hm : Measurable (fun p : ℝ×ℝ ↦ twoPointDensity a s h t p.1 p.2*ENNReal.ofReal (‖p.2-p.1‖^4)) :=
    (measurable_twoPointDensity a s h t).mul hΦ
  calc
    _ = ∫⁻ y : ℝ, ∫⁻ x : ℝ, twoPointDensity a s h t x y*ENNReal.ofReal (‖y-x‖^4) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro x
      rw [twoPointDensity_time_symm a s h t hspos hhpos htpos x y,norm_sub_rev]

end PerronWright.BrownianPositiveBridgeMomentReversal
