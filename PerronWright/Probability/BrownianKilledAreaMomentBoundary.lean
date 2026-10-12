import PerronWright.Probability.BrownianKilledAreaMomentRealRecursion

/-! # Actual boundary support and literal-height real Kac formula

The surviving endpoint is strictly above the killing boundary. Hence the
positive-part height in the ENN-to-real conversion is the literal height
under the genuine transition law. Starting at or below the boundary gives
zero actual moment measure, and positive-order zero-duration moments vanish.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentBoundary

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledAreaMomentKernel
open BrownianKilledAreaMomentFiniteness BrownianKilledAreaMomentRealKernel
open BrownianKilledAreaMomentRealRecursion BrownianKilledAreaMomentRecursion
open BrownianKilledSemigroup

theorem momentLaw_Iic_boundary (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    momentLaw level n T x (Iic level) = 0 := by
  have h := momentLaw_lintegral level n T x
    (measurable_const.indicator measurableSet_Iic :
      Measurable ((Iic level).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))
  simp only [lintegral_indicator measurableSet_Iic,lintegral_one,Measure.restrict_apply_univ] at h
  rw [h]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Eventually.of_forall (fun f ↦ by
    by_cases hf : f ∈ survival (level-x) T
    · have hx : level < x+f T := by
        have hs := (mem_survival_iff (level-x) T f).mp hf T le_rfl
        linarith
      simp only [indicator_of_notMem (show x+f T ∉ Iic level from not_le.mpr hx),mul_zero,Pi.zero_apply]
    · simp only [momentWeight,indicator_of_notMem hf,zero_mul,Pi.zero_apply])

theorem momentLaw_ae_above_boundary (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    ∀ᵐ y ∂momentLaw level n T x, level < y := by
  rw [ae_iff]
  simpa only [not_lt,Iic,mem_ofPred_eq] using momentLaw_Iic_boundary level n T x

theorem transitionLaw_ae_above_boundary (level : ℝ) (T : ℝ≥0) (x : ℝ) :
    ∀ᵐ y ∂transitionLaw level T x, level < y := by
  rw [← momentLaw_zero level T x]
  exact momentLaw_ae_above_boundary level 0 T x

theorem momentWeight_eq_zero_ae_of_le (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (hx : x ≤ level) : momentWeight level n T x =ᵐ[pathLaw] 0 := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  have hnot : f ∉ survival (level-x) T := by
    intro hs
    have h0 := (mem_survival_iff (level-x) T f).mp hs 0 (show (0 : ℝ≥0) ≤ T from bot_le)
    rw [hf] at h0
    linarith
  simp only [momentWeight,indicator_of_notMem hnot,Pi.zero_apply]

theorem momentLaw_eq_zero_of_le (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (hx : x ≤ level) : momentLaw level n T x = 0 := by
  unfold momentLaw
  rw [withDensity_congr_ae (momentWeight_eq_zero_ae_of_le level n T x hx)]
  simp

theorem realInsertion_eq_literal_height (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (F : ℝ → ℝ) (s : ℝ) : realInsertion level n T x F s =
      ∫ z, (z-level) * (∫ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
        ∂transitionLaw level (Real.toNNReal s) x := by
  apply integral_congr_ae
  filter_upwards [transitionLaw_ae_above_boundary level (Real.toNNReal s) x] with z hz
  rw [max_eq_left (sub_nonneg.mpr hz.le)]

theorem integrable_literal_height_insertion (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    IntegrableOn (fun s ↦ ∫ z, (z-level) *
      (∫ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
        ∂transitionLaw level (Real.toNNReal s) x) (Ioc (0 : ℝ) (T : ℝ)) := by
  have he := funext (realInsertion_eq_literal_height level n T x F)
  rw [← he]
  exact integrable_realInsertion level n T x hF hC

/-- Genuine finite, signed, literal-height Kac recurrence at every order. -/
theorem momentLaw_integral_literal_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫ y, F y ∂momentLaw level (n+1) T x) =
      (n+1 : ℝ) * ∫ s in Ioc (0 : ℝ) (T : ℝ),
        ∫ z, (z-level) * (∫ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
          ∂transitionLaw level (Real.toNNReal s) x := by
  rw [momentLaw_integral_insertion level T x n hF hC]
  simp_rw [realInsertion_eq_literal_height]

theorem momentKernel_integral_literal_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    (∫ y, F y ∂momentKernel level (n+1) T x) =
      (n+1 : ℝ) * ∫ s in Ioc (0 : ℝ) (T : ℝ),
        ∫ z, (z-level) * (∫ y, F y ∂momentKernel level n (T-Real.toNNReal s) z)
          ∂killedKernel level (Real.toNNReal s) x :=
  momentLaw_integral_literal_insertion level T x n hF hC

theorem momentLaw_integral_succ_zero_duration (level x : ℝ) (n : ℕ) (F : ℝ → ℝ) :
    (∫ y, F y ∂momentLaw level (n+1) 0 x) = 0 := by
  rw [momentLaw_succ_zero_duration]
  simp

end PerronWright.BrownianKilledAreaMomentBoundary
