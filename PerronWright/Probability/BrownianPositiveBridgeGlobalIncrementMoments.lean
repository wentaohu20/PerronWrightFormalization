import PerronWright.Probability.BrownianPositiveBridgeLeftIncrementMoments
import PerronWright.Probability.BrownianPositiveBridgeMomentReversal

/-! # Actual common fourth increments on the full closed interval

Both endpoints are included. Short increments use the genuine killed
entrance/exit bounds, with actual FDD time reversal on the right. A long
increment is controlled by the already proved all-time marginal moments.
The model supplies all constants; no tightness or excursion premise is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeGlobalIncrementMoments

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeAllTimeMoments
open BrownianPositiveBridgeLeftIncrementMoments BrownianPositiveBridgeMomentReversal

def globalCoefficient (T : ℝ≥0) : ℝ≥0∞ :=
  leftCoefficient (T/4) T+64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2)

theorem globalCoefficient_ne_top (T : ℝ≥0) (hT : 0 < T) : globalCoefficient T ≠ ∞ := by
  have hTR : (0 : ℝ) < T := hT
  unfold globalCoefficient
  exact ENNReal.add_ne_top.mpr ⟨leftCoefficient_ne_top (T/4) T hT,
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) (coordinateBound_lt_top T hT 2).ne)
      (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hTR))⟩

theorem large_gap_coefficient_bound (T h : ℝ≥0) (hT : 0 < T) (hgap : T/2 ≤ h) :
    16*coordinateBound T 2 ≤
      (64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2))*ENNReal.ofReal ((h : ℝ)^2) := by
  have hTR : (0 : ℝ) < T := hT
  have hden : ENNReal.ofReal ((T : ℝ)^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hTR)
  have hcomp : ENNReal.ofReal ((T : ℝ)^2) ≤ 4*ENNReal.ofReal ((h : ℝ)^2) := by
    have hgapR : (T : ℝ)/2 ≤ h := by exact_mod_cast hgap
    have hb : (T : ℝ)^2 ≤ 4*(h : ℝ)^2 := by nlinarith [T.property,h.property]
    have he : ENNReal.ofReal (4*(h : ℝ)^2) = 4*ENNReal.ofReal ((h : ℝ)^2) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),ENNReal.ofReal_ofNat]
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hb
  have he : (64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2))*ENNReal.ofReal ((h : ℝ)^2) =
      (64*coordinateBound T 2*ENNReal.ofReal ((h : ℝ)^2))/ENNReal.ofReal ((T : ℝ)^2) := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [he]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden) (Or.inl ENNReal.ofReal_ne_top)).mpr
  calc
    _ ≤ (16*coordinateBound T 2)*(4*ENNReal.ofReal ((h : ℝ)^2)) := mul_le_mul' le_rfl hcomp
    _ = _ := by ring

theorem eventually_uniform_fourth_increment (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), s+h+t = T →
      (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a T) ≤
        globalCoefficient T*ENNReal.ofReal ((h : ℝ)^2) := by
  have hδ : 0 < T/4 := div_pos hT (by norm_num)
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_left_fourth_increment (T/4) T hδ hT,
    eventually_uniform_coordinate_moment_bound T hT 2] with a ha hleft hmarginal
  intro s h t hsum
  by_cases ht : T/4 ≤ t
  · exact (hleft s h t ht hsum).trans (mul_le_mul'
      (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ 64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2))) le_rfl)
  by_cases hs : T/4 ≤ s
  · have he := actual_fourth_increment_time_reversal a ha s h t (by rw [hsum]; exact hT)
    rw [hsum] at he
    rw [he]
    have hsum' : t+h+s = T := by
      calc
        _ = s+h+t := by ac_rfl
        _ = T := hsum
    exact (hleft t h s hs hsum').trans (mul_le_mul'
      (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ 64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2))) le_rfl)
  have hgap : T/2 ≤ h := by
    have hsR : (s : ℝ) < (T : ℝ)/4 := by exact_mod_cast lt_of_not_ge hs
    have htR : (t : ℝ) < (T : ℝ)/4 := by exact_mod_cast lt_of_not_ge ht
    have hsumR : (s : ℝ)+(h : ℝ)+(t : ℝ) = (T : ℝ) := by exact_mod_cast hsum
    have hgR : (T : ℝ)/2 ≤ h := by linarith
    exact_mod_cast hgR
  have hsT : s ≤ T := by rw [← hsum]; exact (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ h)).trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t))
  have hshT : s+h ≤ T := by rw [← hsum]; exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)
  have hb1 : (∫⁻ g, ENNReal.ofReal (‖g (s+h)‖^4) ∂positiveBridgeLaw a T) ≤ coordinateBound T 2 := by
    simpa only [Real.norm_eq_abs,Nat.reduceMul] using hmarginal (s+h) hshT
  have hb2 : (∫⁻ g, ENNReal.ofReal (‖g s‖^4) ∂positiveBridgeLaw a T) ≤ coordinateBound T 2 := by
    simpa only [Real.norm_eq_abs,Nat.reduceMul] using hmarginal s hsT
  calc
    _ ≤ 8*((∫⁻ g, ENNReal.ofReal (‖g (s+h)‖^4) ∂positiveBridgeLaw a T)+
        (∫⁻ g, ENNReal.ofReal (‖g s‖^4) ∂positiveBridgeLaw a T)) := by
      simpa only [sub_zero] using increment_le_centered_moments (positiveBridgeLaw a T) 0 s h
    _ ≤ 8*(coordinateBound T 2+coordinateBound T 2) := mul_le_mul' le_rfl (add_le_add hb1 hb2)
    _ = 16*coordinateBound T 2 := by ring
    _ ≤ (64*coordinateBound T 2/ENNReal.ofReal ((T : ℝ)^2))*ENNReal.ofReal ((h : ℝ)^2) := large_gap_coefficient_bound T h hT hgap
    _ ≤ _ := mul_le_mul' (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ leftCoefficient (T/4) T)) le_rfl

theorem eventually_uniform_pair_fourth_increment (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (u v : ℝ≥0), u ≤ T → v ≤ T →
      (∫⁻ g, ENNReal.ofReal (‖g v-g u‖^4) ∂positiveBridgeLaw a T) ≤
        globalCoefficient T*ENNReal.ofReal (|((v : ℝ)-(u : ℝ))|^2) := by
  filter_upwards [eventually_uniform_fourth_increment T hT] with a ha
  intro u v huT hvT
  have hordered : ∀ u v : ℝ≥0, u ≤ v → v ≤ T →
      (∫⁻ g, ENNReal.ofReal (‖g v-g u‖^4) ∂positiveBridgeLaw a T) ≤
        globalCoefficient T*ENNReal.ofReal (|((v : ℝ)-(u : ℝ))|^2) := by
    intro u v huv hvT
    have hsum : u+(v-u)+(T-v) = T := by rw [add_tsub_cancel_of_le huv,add_tsub_cancel_of_le hvT]
    have he := ha u (v-u) (T-v) hsum
    rw [add_tsub_cancel_of_le huv] at he
    simpa only [NNReal.coe_sub huv,abs_of_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤ v from huv))] using he
  rcases le_total u v with huv | hvu
  · exact hordered u v huv hvT
  · simpa only [norm_sub_rev,abs_sub_comm] using hordered v u hvu huT

end PerronWright.BrownianPositiveBridgeGlobalIncrementMoments
