import PerronWright.Probability.BrownianKilledAreaDuhamel
import PerronWright.Probability.BrownianKilledAreaMomentKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Actual area-parameter continuity and moment domination

The actual killed area law is antitone and continuous in its nonnegative
area parameter against every bounded Borel test. The first-order error
is bounded by the actual first surviving area moment, without supposing
that moment finite or assuming a stochastic differentiation formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaParameter

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledAreaGeometry
open BrownianKilledAreaKernel BrownianKilledAreaSemigroup BrownianKilledAreaMomentKernel

theorem continuous_parameter_weight (level : ℝ) (T : ℝ≥0) (x : ℝ) (f : Path) :
    Continuous (fun u : ℝ≥0 ↦ weight level u T x f) := by
  by_cases hf : f ∈ survival (level-x) T
  · simp only [weight,indicator_of_mem hf]
    exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (NNReal.continuous_coe.neg.mul continuous_const))
  · simp only [weight,indicator_of_notMem hf]
    exact continuous_const

theorem antitone_parameter_weight (level : ℝ) (T : ℝ≥0) (x : ℝ) (f : Path) :
    Antitone (fun u : ℝ≥0 ↦ weight level u T x f) := by
  intro u v huv
  by_cases hf : f ∈ survival (level-x) T
  · simp only [weight,indicator_of_mem hf]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (show (u : ℝ) ≤ v from huv))
      (shiftedArea_nonneg_of_survival level x T f hf)
  · simp only [weight,indicator_of_notMem hf,le_refl]

theorem antitone_parameter_law (level : ℝ) (T : ℝ≥0) (x : ℝ) :
    Antitone (fun u : ℝ≥0 ↦ law level u T x) := by
  intro u v huv
  exact Measure.map_mono (withDensity_mono (Eventually.of_forall
    (fun f ↦ antitone_parameter_weight level T x f huv)))
    (measurable_const.add (continuous_eval T).measurable)

theorem law_le_transitionLaw (level : ℝ) (u T : ℝ≥0) (x : ℝ) :
    law level u T x ≤ BrownianKilledSemigroup.transitionLaw level T x := by
  rw [← law_zero level T x]
  exact antitone_parameter_law level T x (zero_le : (0 : ℝ≥0) ≤ u)

theorem continuous_parameter_lintegral (level : ℝ) (T : ℝ≥0) (x C : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) (hbound : ∀ y, F y ≤ ENNReal.ofReal C) :
    Continuous (fun u : ℝ≥0 ↦ ∫⁻ y, F y ∂law level u T x) := by
  have he : (fun u : ℝ≥0 ↦ ∫⁻ y, F y ∂law level u T x) =
      (fun u : ℝ≥0 ↦ ∫⁻ f, weight level u T x f*F (x+f T) ∂pathLaw) :=
    funext (fun u ↦ law_lintegral level u T x hF)
  rw [he,continuous_iff_continuousAt]
  intro u
  apply tendsto_lintegral_filter_of_dominated_convergence
    (μ := pathLaw) (fun _f : Path ↦ ENNReal.ofReal C)
  · exact Eventually.of_forall (fun v ↦ (measurable_weight level v T x).mul
      (hF.comp (measurable_const.add (continuous_eval T).measurable)))
  · exact Eventually.of_forall (fun v ↦ Eventually.of_forall (fun f ↦
      (mul_le_mul' (weight_le_one level v T x f) (hbound (x+f T))).trans_eq (one_mul _)))
  · simp only [lintegral_const,measure_univ,mul_one]
    exact ENNReal.ofReal_ne_top
  · exact Eventually.of_forall (fun f ↦ ENNReal.Tendsto.mul_const
      (continuous_parameter_weight level T x f).continuousAt
      (Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound (x+f T)))))

theorem continuous_parameter_apply (level : ℝ) (T : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    Continuous (fun u : ℝ≥0 ↦ law level u T x B) := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    continuous_parameter_lintegral level T x 1
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))
      (fun y ↦ by by_cases hy : y ∈ B <;> simp [Set.indicator,hy])

theorem weight_first_moment_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ) (f : Path) :
    weight level 0 T x f ≤ weight level u T x f+
      ENNReal.ofReal (u : ℝ)*momentWeight level 1 T x f := by
  by_cases hf : f ∈ survival (level-x) T
  · rw [weight,weight,momentWeight,indicator_of_mem hf,indicator_of_mem hf,indicator_of_mem hf]
    simp only [NNReal.coe_zero,neg_zero,zero_mul,Real.exp_zero,ENNReal.ofReal_one,pow_one]
    have hA := shiftedArea_nonneg_of_survival level x T f hf
    have hR : 1 ≤ Real.exp (-(u : ℝ)*shiftedArea level x T f)+
        (u : ℝ)*shiftedArea level x T f := by
      have he := Real.add_one_le_exp (-(u : ℝ)*shiftedArea level x T f)
      linarith
    rw [← ENNReal.ofReal_mul u.coe_nonneg,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg u.coe_nonneg hA)]
    exact (ENNReal.ofReal_le_ofReal hR).trans' (by simp)
  · simp only [weight,momentWeight,indicator_of_notMem hf,mul_zero,zero_add,le_refl]

/-- Actual first surviving area-moment control for every nonnegative Borel test. -/
theorem law_lintegral_first_moment_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law level 0 T x) ≤ (∫⁻ y, F y ∂law level u T x)+
      ENNReal.ofReal (u : ℝ)*(∫⁻ y, F y ∂momentLaw level 1 T x) := by
  have hm : Measurable (fun f : Path ↦ momentWeight level 1 T x f*F (x+f T)) :=
    (measurable_momentWeight level 1 T x).mul
      (hF.comp (measurable_const.add (continuous_eval T).measurable))
  have hw : Measurable (fun f : Path ↦ weight level u T x f*F (x+f T)) :=
    (measurable_weight level u T x).mul
      (hF.comp (measurable_const.add (continuous_eval T).measurable))
  rw [law_lintegral level 0 T x hF,law_lintegral level u T x hF,
    momentLaw_lintegral level 1 T x hF]
  calc
    _ ≤ ∫⁻ f, (weight level u T x f*F (x+f T)+
        ENNReal.ofReal (u : ℝ)*(momentWeight level 1 T x f*F (x+f T))) ∂pathLaw := by
      apply lintegral_mono
      intro f
      simpa only [add_mul,mul_assoc] using
        mul_le_mul' (weight_first_moment_bound level u T x f) (le_refl (F (x+f T)))
    _ = _ := by rw [lintegral_add_left hw,lintegral_const_mul _ hm]

theorem law_apply_first_moment_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    law level 0 T x B ≤ law level u T x B+
      ENNReal.ofReal (u : ℝ)*momentLaw level 1 T x B := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    law_lintegral_first_moment_bound level u T x
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

end PerronWright.BrownianKilledAreaParameter
