import PerronWright.Probability.BrownianKilledAreaSemigroup

/-!
# Actual surviving-path area moment kernels

These possibly infinite measures are defined directly from the real
boundary-shifted path area and the genuine Brownian path law.  No finite
moment or moment recursion is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentKernel

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledSemigroup BrownianKilledTransitionKernel

def momentWeight (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ) (f : Path) : ℝ≥0∞ :=
  (survival (level-x) t).indicator
    (fun g ↦ ENNReal.ofReal (shiftedArea level x t g) ^ n) f

theorem measurable_joint_momentWeight (level : ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (fun p : ℝ × Path ↦ momentWeight level n t p.1 p.2) := by
  change Measurable (fun p : ℝ × Path ↦ if p.2 ∈ survival (level-p.1) t then
    ENNReal.ofReal (shiftedArea level p.1 t p.2) ^ n else 0)
  have hs : MeasurableSet {p : ℝ × Path | p.2 ∈ survival (level-p.1) t} :=
    (isOpen_lt (continuous_const.sub continuous_fst)
      ((continuous_minimum_at t).comp continuous_snd)).measurableSet
  exact Measurable.ite hs
    ((measurable_joint_shiftedArea level t).ennreal_ofReal.pow_const n) measurable_const

theorem measurable_momentWeight (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ) :
    Measurable (momentWeight level n t x) :=
  (measurable_joint_momentWeight level n t).comp (measurable_const.prodMk measurable_id)

theorem momentWeight_past (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ) (f : Path) :
    momentWeight level n t x (pastPath t f) = momentWeight level n t x f := by
  by_cases hf : f ∈ survival (level-x) t
  · have hp := (past_survival_iff (level-x) t f).mpr hf
    rw [momentWeight,momentWeight,indicator_of_mem hp,indicator_of_mem hf,shiftedArea_past]
  · have hp := (past_survival_iff (level-x) t f).not.mpr hf
    simp only [momentWeight,indicator_of_notMem hp,indicator_of_notMem hf]

def momentLaw (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (pathLaw.withDensity (momentWeight level n t x)).map (fun f : Path ↦ x+f t)

theorem momentLaw_lintegral (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂momentLaw level n t x) =
      ∫⁻ f, momentWeight level n t x f*F (x+f t) ∂pathLaw := by
  have hm : Measurable (fun f : Path ↦ x+f t) :=
    measurable_const.add (continuous_eval t).measurable
  rw [momentLaw,lintegral_map hF hm]
  exact lintegral_withDensity_eq_lintegral_mul pathLaw
    (measurable_momentWeight level n t x) (hF.comp hm)

theorem measurable_momentLaw_lintegral (level : ℝ) (n : ℕ) (t : ℝ≥0)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun x : ℝ ↦ ∫⁻ y, F y ∂momentLaw level n t x) := by
  have hm : Measurable (fun p : ℝ × Path ↦ momentWeight level n t p.1 p.2*F (p.1+p.2 t)) :=
    (measurable_joint_momentWeight level n t).mul (hF.comp
      (measurable_fst.add ((continuous_eval t).measurable.comp measurable_snd)))
  have he : (fun x : ℝ ↦ ∫⁻ y, F y ∂momentLaw level n t x) =
      (fun x : ℝ ↦ ∫⁻ f, momentWeight level n t x f*F (x+f t) ∂pathLaw) :=
    funext (fun x ↦ momentLaw_lintegral level n t x hF)
  rw [he]
  exact hm.lintegral_prod_right'

theorem measurable_momentLaw_apply (level : ℝ) (n : ℕ) (t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun x : ℝ ↦ momentLaw level n t x B) := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    measurable_momentLaw_lintegral level n t (measurable_const.indicator hB :
      Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

def momentKernel (level : ℝ) (n : ℕ) (t : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨momentLaw level n t,Measure.measurable_measure.mpr
    (fun _ hB ↦ measurable_momentLaw_apply level n t hB)⟩

@[simp] theorem momentKernel_apply (level : ℝ) (n : ℕ) (t : ℝ≥0) (x : ℝ) :
    momentKernel level n t x = momentLaw level n t x := rfl

theorem momentWeight_zero (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    momentWeight level 0 t x = (survival (level-x) t).indicator (fun _ : Path ↦ 1) := by
  funext f
  simp only [momentWeight,pow_zero]

theorem momentLaw_zero (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    momentLaw level 0 t x = transitionLaw level t x := by
  rw [momentLaw,momentWeight_zero,← BrownianKilledAreaSemigroup.weight_zero level t x]
  exact BrownianKilledAreaSemigroup.law_zero level t x

theorem momentKernel_zero (level : ℝ) (t : ℝ≥0) :
    momentKernel level 0 t = killedKernel level t := by
  ext x B hB
  rw [momentKernel_apply,killedKernel_apply,momentLaw_zero]

end PerronWright.BrownianKilledAreaMomentKernel
