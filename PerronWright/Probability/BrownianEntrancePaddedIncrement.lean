import PerronWright.Probability.BrownianEntranceMomentTransfer

/-! # Literal endpoint padding costs a vanishing fourth-moment error

The actual positive bridge has both endpoint values a almost everywhere.
Replacing them by zero changes a single increment by at most |a|. The
proved fourth-power inequality thus controls the genuine padded source
used in the entrance finite-dimensional limits.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntrancePaddedIncrement

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianEntranceMomentTransfer

theorem boundary_eval_eq (T t : ℝ≥0) (ht : t ≤ T) (f : Path) (a : ℝ)
    (h0 : f 0 = a) (hT : f T = a) (hout : ¬ (0 < t ∧ t < T)) : f t = a := by
  by_cases he : t = 0
  · simpa only [he] using h0
  have hp : 0 < t := (zero_le : (0 : ℝ≥0) ≤ t).lt_of_ne (Ne.symm he)
  have hle : T ≤ t := le_of_not_gt (fun hlt ↦ hout ⟨hp,hlt⟩)
  simpa only [le_antisymm ht hle] using hT

theorem padded_increment_norm_le (T u v : ℝ≥0) (hu : u ≤ T) (hv : v ≤ T)
    (f : Path) (a : ℝ) (h0 : f 0 = a) (hT : f T = a) :
    ‖paddedValue T v f-paddedValue T u f‖ ≤ ‖f v-f u‖+|a| := by
  by_cases hui : 0 < u ∧ u < T
  · by_cases hvi : 0 < v ∧ v < T
    · simp only [paddedValue,if_pos hui,if_pos hvi]
      exact le_add_of_nonneg_right (abs_nonneg a)
    · have he := boundary_eval_eq T v hv f a h0 hT hvi
      have hn := norm_add_le (f u-f v) (f v)
      rw [sub_add_cancel] at hn
      simpa only [paddedValue,if_pos hui,if_neg hvi,zero_sub,norm_neg,norm_sub_rev,he,
        Real.norm_eq_abs] using hn
  · by_cases hvi : 0 < v ∧ v < T
    · have he := boundary_eval_eq T u hu f a h0 hT hui
      have hn := norm_add_le (f v-f u) (f u)
      rw [sub_add_cancel] at hn
      simpa only [paddedValue,if_neg hui,if_pos hvi,sub_zero,he,Real.norm_eq_abs] using hn
    · simp only [paddedValue,if_neg hui,if_neg hvi,sub_self,norm_zero]
      exact add_nonneg (norm_nonneg _) (abs_nonneg _)

theorem padded_increment_fourth_le (T u v : ℝ≥0) (hu : u ≤ T) (hv : v ≤ T)
    (f : Path) (a : ℝ) (h0 : f 0 = a) (hT : f T = a) :
    ENNReal.ofReal (‖paddedValue T v f-paddedValue T u f‖^4) ≤
      8*(ENNReal.ofReal (‖f v-f u‖^4)+ENNReal.ofReal (|a|^4)) := by
  have hn := padded_increment_norm_le T u v hu hv f a h0 hT
  have hp := (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans
    (add_pow_le (norm_nonneg (f v-f u)) (abs_nonneg a) 4)
  norm_num at hp
  have he : ENNReal.ofReal (8*(‖f v-f u‖^4+|a|^4)) =
      8*(ENNReal.ofReal (‖f v-f u‖^4)+ENNReal.ofReal (|a|^4)) := by
    rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_add
      (pow_nonneg (norm_nonneg _) _) (pow_nonneg (abs_nonneg _) _)]
    norm_num
  exact (ENNReal.ofReal_le_ofReal hp).trans_eq he

theorem padded_fourth_lintegral_le (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (u v : ℝ≥0) (hu : u ≤ T) (hv : v ≤ T) :
    (∫⁻ f, ENNReal.ofReal (‖paddedValue T v f-paddedValue T u f‖^4) ∂positiveBridgeLaw a T) ≤
      8*(∫⁻ f, ENNReal.ofReal (‖f v-f u‖^4) ∂positiveBridgeLaw a T)+8*ENNReal.ofReal (|a|^4) := by
  let := positiveBridgeLaw_isProbability a ha T hT
  have hm : Measurable (fun f : Path ↦ ENNReal.ofReal (‖f v-f u‖^4)) := by fun_prop
  have he : ∀ᵐ f ∂positiveBridgeLaw a T,
      ENNReal.ofReal (‖paddedValue T v f-paddedValue T u f‖^4) ≤
        8*(ENNReal.ofReal (‖f v-f u‖^4)+ENNReal.ofReal (|a|^4)) := by
    filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with f hf
    exact padded_increment_fourth_le T u v hu hv f a hf.1 hf.2
  apply (lintegral_mono_ae he).trans_eq
  have hsum : Measurable (fun f : Path ↦ ENNReal.ofReal (‖f v-f u‖^4)+ENNReal.ofReal (|a|^4)) :=
    hm.add measurable_const
  rw [lintegral_const_mul _ hsum,lintegral_add_left hm,
    lintegral_const,measure_univ,mul_one,mul_add]

theorem vanishing_padding_error :
    Tendsto (fun a : ℝ ↦ (8 : ℝ≥0∞)*ENNReal.ofReal (|a|^4)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ ↦ |a|^4) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun a : ℝ ↦ |a|^4) := continuous_abs.pow 4
    simpa only [abs_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun a : ℝ ↦ ENNReal.ofReal (|a|^4)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  simpa only [mul_zero] using
    ENNReal.Tendsto.const_mul he (Or.inr (show (8 : ℝ≥0∞) ≠ ∞ by simp))

end PerronWright.BrownianEntrancePaddedIncrement
