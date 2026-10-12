import PerronWright.Probability.BrownianKilledAreaKernel

/-! # Actual killed-area kernel composition from independent Brownian segments

The literal area splits additively across consecutive segments. Its
survival-gated exponential weight therefore splits multiplicatively.
Whole-past/future independence proves the weighted kernel semigroup for
arbitrary nonnegative Borel endpoint tests, including zero durations.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaSemigroup

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledAreaKernel BrownianKilledSemigroup
open BrownianKilledTransitionKernel

theorem lintegral_past_weight (level : ℝ) (u s : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, weight level u s x p*F (x+p s) ∂pastLaw s) =
      ∫⁻ y, F y ∂law level u s x := by
  have hm : Measurable (fun p : Path ↦ weight level u s x p*F (x+p s)) :=
    (measurable_weight level u s x).mul
      (hF.comp (measurable_const.add (continuous_eval s).measurable))
  rw [pastLaw,lintegral_map hm (measurable_pastPath s),law_lintegral level u s x hF]
  apply lintegral_congr
  intro f
  rw [weight_past,pastPath_eval,min_self]

theorem measurable_segment_test (level : ℝ) (u s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : Path × Path ↦
      weight level u s x p.1*weight level u t (x+p.1 s) p.2*F (x+p.1 s+p.2 t)) := by
  have hx : Measurable (fun p : Path × Path ↦ x+p.1 s) :=
    measurable_const.add ((continuous_eval s).measurable.comp measurable_fst)
  exact ((measurable_weight level u s x).comp measurable_fst).mul
    ((measurable_joint_weight level u t).comp (hx.prodMk measurable_snd)) |>.mul
      (hF.comp (hx.add ((continuous_eval t).measurable.comp measurable_snd)))

/-- Exact full-segment area-weighted past/future disintegration. -/
theorem law_lintegral_eq_past_future (level : ℝ) (u s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law level u (s+t) x) =
      ∫⁻ p, ∫⁻ g, weight level u s x p*weight level u t (x+p s) g*F (x+p s+g t)
        ∂pathLaw ∂pastLaw s := by
  have hm := measurable_segment_test level u s t x hF
  rw [← lintegral_prod _ hm.aemeasurable,← past_future_jointLaw s,
    lintegral_map hm ((measurable_pastPath s).prodMk (measurable_futurePath s)),
    law_lintegral level u (s+t) x hF]
  apply lintegral_congr
  intro f
  dsimp only
  rw [weight_past,pastPath_eval,min_self,weight_add,endpoint_add,add_assoc]

/-- Genuine area-weighted transition composition, with no analytic
or Markov composition identity supplied as a premise. -/
theorem law_lintegral_composition (level : ℝ) (u s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law level u (s+t) x) =
      ∫⁻ z, ∫⁻ y, F y ∂law level u t z ∂law level u s x := by
  rw [law_lintegral_eq_past_future level u s t x hF,
    ← lintegral_past_weight level u s x (measurable_law_lintegral level u t hF)]
  apply lintegral_congr
  intro p
  rw [law_lintegral level u t (x+p s) hF]
  have hm : Measurable (fun g : Path ↦ weight level u t (x+p s) g*F (x+p s+g t)) :=
    (measurable_weight level u t (x+p s)).mul
      (hF.comp (measurable_const.add (continuous_eval t).measurable))
  simp only [mul_assoc]
  exact lintegral_const_mul _ hm

theorem law_composition (level : ℝ) (u s t : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    law level u (s+t) x B = ∫⁻ z, law level u t z B ∂law level u s x := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    law_lintegral_composition level u s t x
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

theorem areaKernel_semigroup (level : ℝ) (u s t : ℝ≥0) :
    areaKernel level u (s+t) = (areaKernel level u t) ∘ₖ (areaKernel level u s) := by
  ext x B hB
  rw [Kernel.comp_apply' _ _ _ hB]
  exact law_composition level u s t x hB

theorem weight_zero (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    weight level 0 t x = (survival (level-x) t).indicator (fun _ : Path ↦ 1) := by
  funext f
  simp only [weight,NNReal.coe_zero,neg_zero,zero_mul,Real.exp_zero,ENNReal.ofReal_one]

/-- At zero area parameter the literal weighted law is exactly the
actual unweighted absorbing Brownian transition law. -/
theorem law_zero (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    law level 0 t x = transitionLaw level t x := by
  rw [law,weight_zero]
  change (pathLaw.withDensity ((survival (level-x) t).indicator 1)).map
    (fun f : Path ↦ x+f t) = _
  rw [withDensity_indicator_one (measurableSet_survival _ _),transitionLaw,killedEndpointLaw]
  exact (Measure.map_map (measurable_const.add measurable_id :
    Measurable (fun y : ℝ ↦ x+y)) (continuous_eval t).measurable).symm

theorem areaKernel_zero (level : ℝ) (t : ℝ≥0) : areaKernel level 0 t = killedKernel level t := by
  ext x B hB
  rw [areaKernel_apply,killedKernel_apply,law_zero]

end PerronWright.BrownianKilledAreaSemigroup
