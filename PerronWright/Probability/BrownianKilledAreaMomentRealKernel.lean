import PerronWright.Probability.BrownianKilledAreaMomentFiniteness
import PerronWright.Probability.BrownianKilledAreaTimeKernel

/-! # Duration/state measurability and real tests of actual finite moments

The measures are the original surviving-path area moments. Time and state
measurability are proved directly from their joint path densities. Bounded
real endpoint tests are integrable at every duration and starting state.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentRealKernel

open BrownianPathLaw BrownianKilledAreaGeometry BrownianKilledAreaMomentKernel
open BrownianKilledAreaMomentFiniteness BrownianKilledAreaMomentSegments
open BrownianKilledAreaDuhamelGeometry BrownianKilledSemigroup

theorem measurable_time_state_momentWeight (level : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ≥0 × (ℝ × Path) ↦ momentWeight level n p.1 p.2.1 p.2.2) := by
  have he : (fun p : ℝ≥0 × (ℝ × Path) ↦ momentWeight level n p.1 p.2.1 p.2.2) =
      fun p ↦ BrownianKilledAreaKernel.weight level 0 p.1 p.2.1 p.2.2 *
        ENNReal.ofReal (shiftedArea level p.2.1 p.1 p.2.2)^n :=
    funext (fun p ↦ momentWeight_eq_survivalWeight_mul level n p.1 p.2.1 p.2.2)
  rw [he]
  exact (measurable_time_state_weight level 0).mul
    ((measurable_time_state_shiftedArea level).ennreal_ofReal.pow_const n)

theorem measurable_time_state_momentLaw_lintegral (level : ℝ) (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ≥0 × ℝ ↦ ∫⁻ y, F y ∂momentLaw level n p.1 p.2) := by
  have hw : Measurable (fun p : (ℝ≥0 × ℝ) × Path ↦ momentWeight level n p.1.1 p.1.2 p.2) :=
    (measurable_time_state_momentWeight level n).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hy : Measurable (fun p : (ℝ≥0 × ℝ) × Path ↦ p.1.2+p.2 p.1.1) :=
    (measurable_snd.comp measurable_fst).add
      (continuous_joint_eval.measurable.comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have he : (fun p : ℝ≥0 × ℝ ↦ ∫⁻ y, F y ∂momentLaw level n p.1 p.2) =
      fun p ↦ ∫⁻ f, momentWeight level n p.1 p.2 f * F (p.2+f p.1) ∂pathLaw :=
    funext (fun p ↦ momentLaw_lintegral level n p.1 p.2 hF)
  rw [he]
  exact (hw.mul (hF.comp hy)).lintegral_prod_right'

theorem measurable_time_state_momentLaw_apply (level : ℝ) (n : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ≥0 × ℝ ↦ momentLaw level n p.1 p.2 B) := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    measurable_time_state_momentLaw_lintegral level n
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

def timeMomentKernel (level : ℝ) (n : ℕ) : Kernel (ℝ≥0 × ℝ) ℝ :=
  ⟨fun p ↦ momentLaw level n p.1 p.2,Measure.measurable_measure.mpr
    (fun _ hB ↦ measurable_time_state_momentLaw_apply level n hB)⟩

@[simp] theorem timeMomentKernel_apply (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    timeMomentKernel level n (T,x) = momentLaw level n T x := rfl

instance timeMomentKernel_zero_isFinite (level : ℝ) : IsFiniteKernel (timeMomentKernel level 0) :=
  ⟨⟨1,ENNReal.one_lt_top,fun p ↦ by
    rw [timeMomentKernel_apply,momentLaw_zero]
    exact transitionLaw_univ_le_one level p.1 p.2⟩⟩

theorem integrable_bounded_endpoint_test (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    Integrable F (momentLaw level n T x) :=
  (integrable_const C).mono' hF.aestronglyMeasurable (Eventually.of_forall hC)

theorem momentLaw_integral_eq_path_integral (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ y, F y ∂momentLaw level n T x) =
      ∫ f : Path, (momentWeight level n T x f).toReal * F (x+f T) ∂pathLaw := by
  have hy : Measurable (fun f : Path ↦ x+f T) :=
    measurable_const.add (continuous_eval T).measurable
  rw [momentLaw,integral_map hy.aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_momentWeight level n T x)
      (Eventually.of_forall (fun f ↦ (momentWeight_ne_top level n T x f).lt_top))]
  rfl

theorem measurable_time_state_momentLaw_integral (level : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, ‖F y‖ ≤ C) :
    Measurable (fun p : ℝ≥0 × ℝ ↦ ∫ y, F y ∂momentLaw level n p.1 p.2) := by
  have he : (fun p : ℝ≥0 × ℝ ↦ ∫ y, F y ∂momentLaw level n p.1 p.2) =
      fun p ↦ (∫⁻ y, ENNReal.ofReal (F y) ∂momentLaw level n p.1 p.2).toReal -
        (∫⁻ y, ENNReal.ofReal (-F y) ∂momentLaw level n p.1 p.2).toReal :=
    funext (fun p ↦ integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (integrable_bounded_endpoint_test level n p.1 p.2 hF hC))
  rw [he]
  exact (measurable_time_state_momentLaw_lintegral level n hF.ennreal_ofReal).ennreal_toReal.sub
    (measurable_time_state_momentLaw_lintegral level n hF.neg.ennreal_ofReal).ennreal_toReal

end PerronWright.BrownianKilledAreaMomentRealKernel
