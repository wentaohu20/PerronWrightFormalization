import PerronWright.Probability.BrownianKilledAreaMomentKernel

/-!
# Actual independent-segment disintegration for killed area moments

Only the future area carries a power.  The insertion is the actual height
at the splitting time, and both path segments are constrained by genuine
survival events.  Whole-past/future independence is used directly.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentSegments

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledSemigroup BrownianKilledTransitionKernel
open BrownianKilledAreaMomentKernel

theorem momentWeight_eq_survivalWeight_mul (level : ℝ) (n : ℕ) (t : ℝ≥0)
    (x : ℝ) (f : Path) :
    momentWeight level n t x f =
      BrownianKilledAreaKernel.weight level 0 t x f *
        ENNReal.ofReal (shiftedArea level x t f) ^ n := by
  by_cases hf : f ∈ survival (level-x) t
  · simp only [momentWeight,
      BrownianKilledAreaSemigroup.weight_zero,indicator_of_mem hf,one_mul]
  · simp only [momentWeight,
      BrownianKilledAreaSemigroup.weight_zero,indicator_of_notMem hf,zero_mul]

theorem measurable_segment_moment_test (level : ℝ) (n : ℕ) (s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : Path × Path ↦
      BrownianKilledAreaKernel.weight level 0 s x p.1 * ENNReal.ofReal (x+p.1 s-level) *
        momentWeight level n t (x+p.1 s) p.2 * F (x+p.1 s+p.2 t)) := by
  have hx : Measurable (fun p : Path × Path ↦ x+p.1 s) :=
    measurable_const.add ((continuous_eval s).measurable.comp measurable_fst)
  exact (((BrownianKilledAreaKernel.measurable_weight level 0 s x).comp measurable_fst).mul
    (hx.sub_const level).ennreal_ofReal).mul
      ((measurable_joint_momentWeight level n t).comp (hx.prodMk measurable_snd)) |>.mul
        (hF.comp (hx.add ((continuous_eval t).measurable.comp measurable_snd)))

theorem lintegral_surviving_future_moment_eq_past_future
    (level : ℝ) (n : ℕ) (s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, BrownianKilledAreaKernel.weight level 0 (s+t) x f *
      ENNReal.ofReal (x+f s-level) *
      ENNReal.ofReal (shiftedArea level (x+f s) t (futurePath s f)) ^ n *
      F (x+f (s+t)) ∂pathLaw) =
    ∫⁻ p, ∫⁻ g, BrownianKilledAreaKernel.weight level 0 s x p *
      ENNReal.ofReal (x+p s-level) * momentWeight level n t (x+p s) g *
      F (x+p s+g t) ∂pathLaw ∂pastLaw s := by
  have hm := measurable_segment_moment_test level n s t x hF
  rw [← lintegral_prod _ hm.aemeasurable,← past_future_jointLaw s,
    lintegral_map hm ((measurable_pastPath s).prodMk (measurable_futurePath s))]
  apply lintegral_congr
  intro f
  dsimp only
  rw [BrownianKilledAreaKernel.weight_past,pastPath_eval,min_self,
    momentWeight_eq_survivalWeight_mul,BrownianKilledAreaKernel.weight_add,endpoint_add]
  simp only [add_assoc]
  ring

theorem lintegral_past_survivalWeight_eq_transition (level : ℝ) (s : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, BrownianKilledAreaKernel.weight level 0 s x p*F (x+p s) ∂pastLaw s) =
      ∫⁻ z, F z ∂transitionLaw level s x := by
  rw [← BrownianKilledAreaSemigroup.law_zero level s x]
  exact BrownianKilledAreaSemigroup.lintegral_past_weight level 0 s x hF

/-- Genuine surviving future-area moment disintegration, for every
nonnegative Borel endpoint test and without finite-moment assumptions. -/
theorem lintegral_surviving_future_moment (level : ℝ) (n : ℕ) (s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, BrownianKilledAreaKernel.weight level 0 (s+t) x f *
      ENNReal.ofReal (x+f s-level) *
      ENNReal.ofReal (shiftedArea level (x+f s) t (futurePath s f)) ^ n *
      F (x+f (s+t)) ∂pathLaw) =
    ∫⁻ z, ENNReal.ofReal (z-level) *
      (∫⁻ y, F y ∂momentLaw level n t z) ∂transitionLaw level s x := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z-level) *
      ∫⁻ y, F y ∂momentLaw level n t z) :=
    (measurable_id.sub_const level).ennreal_ofReal.mul
      (measurable_momentLaw_lintegral level n t hF)
  rw [lintegral_surviving_future_moment_eq_past_future level n s t x hF,
    ← lintegral_past_survivalWeight_eq_transition level s x hm]
  apply lintegral_congr
  intro p
  rw [momentLaw_lintegral level n t (x+p s) hF]
  have hg : Measurable (fun g : Path ↦ momentWeight level n t (x+p s) g *
      F (x+p s+g t)) :=
    (measurable_momentWeight level n t (x+p s)).mul
      (hF.comp (measurable_const.add (continuous_eval t).measurable))
  simpa only [mul_assoc] using lintegral_const_mul
    (BrownianKilledAreaKernel.weight level 0 s x p * ENNReal.ofReal (x+p s-level)) hg

end PerronWright.BrownianKilledAreaMomentSegments
