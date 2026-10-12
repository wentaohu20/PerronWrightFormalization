import PerronWright.Probability.BrownianKilledAreaTimeKernel

/-! # Actual two-segment area weights with an interior endpoint insertion

Different head and tail area parameters and an arbitrary nonnegative
Borel insertion are retained. Their actual path integral is evaluated
using the proved whole-past/future product law, not a Markov formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaDuhamelInsertion

open BrownianPathLaw BrownianPathIndependentIncrements BrownianKilledAreaKernel
open BrownianKilledAreaSemigroup BrownianKilledSemigroup

theorem measurable_mixed_segment_test (level : ℝ) (u v s t : ℝ≥0) (x : ℝ)
    {H F : ℝ → ℝ≥0∞} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun p : Path × Path ↦
      weight level u s x p.1*weight level v t (x+p.1 s) p.2*
        H (x+p.1 s)*F (x+p.1 s+p.2 t)) := by
  have hx : Measurable (fun p : Path × Path ↦ x+p.1 s) :=
    measurable_const.add ((continuous_eval s).measurable.comp measurable_fst)
  exact (((measurable_weight level u s x).comp measurable_fst).mul
    ((measurable_joint_weight level v t).comp (hx.prodMk measurable_snd))).mul
      (hH.comp hx) |>.mul
        (hF.comp (hx.add ((continuous_eval t).measurable.comp measurable_snd)))

theorem mixed_insertion_eq_past_future (level : ℝ) (u v s t : ℝ≥0) (x : ℝ)
    {H F : ℝ → ℝ≥0∞} (hH : Measurable H) (hF : Measurable F) :
    (∫⁻ f, weight level u s x f*weight level v t (x+f s) (futurePath s f)*
        H (x+f s)*F (x+f (s+t)) ∂pathLaw) =
      ∫⁻ p, ∫⁻ g, weight level u s x p*weight level v t (x+p s) g*
        H (x+p s)*F (x+p s+g t) ∂pathLaw ∂pastLaw s := by
  have hm := measurable_mixed_segment_test level u v s t x hH hF
  rw [← lintegral_prod _ hm.aemeasurable,← past_future_jointLaw s,
    lintegral_map hm ((measurable_pastPath s).prodMk (measurable_futurePath s))]
  apply lintegral_congr
  intro f
  dsimp only
  rw [weight_past,pastPath_eval,min_self,endpoint_add,add_assoc]

/-- The actual Brownian two-segment insertion formula, with independently
specified nonnegative head/tail area parameters and arbitrary Borel tests. -/
theorem mixed_insertion_eq_kernels (level : ℝ) (u v s t : ℝ≥0) (x : ℝ)
    {H F : ℝ → ℝ≥0∞} (hH : Measurable H) (hF : Measurable F) :
    (∫⁻ f, weight level u s x f*weight level v t (x+f s) (futurePath s f)*
        H (x+f s)*F (x+f (s+t)) ∂pathLaw) =
      ∫⁻ y, H y*(∫⁻ z, F z ∂law level v t y) ∂law level u s x := by
  have hg : Measurable (fun y : ℝ ↦ H y*(∫⁻ z, F z ∂law level v t y)) :=
    hH.mul (measurable_law_lintegral level v t hF)
  rw [mixed_insertion_eq_past_future level u v s t x hH hF,
    ← lintegral_past_weight level u s x hg]
  apply lintegral_congr
  intro p
  rw [law_lintegral level v t (x+p s) hF]
  have hm : Measurable (fun g : Path ↦ weight level v t (x+p s) g*F (x+p s+g t)) :=
    (measurable_weight level v t (x+p s)).mul
      (hF.comp (measurable_const.add (continuous_eval t).measurable))
  calc
    _ = ∫⁻ g, (weight level u s x p*H (x+p s))*
        (weight level v t (x+p s) g*F (x+p s+g t)) ∂pathLaw :=
      lintegral_congr (fun _ ↦ by ac_rfl)
    _ = _ := by rw [lintegral_const_mul _ hm,mul_assoc]

theorem height_insertion_eq_kernels (level : ℝ) (u s t : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, weight level u s x f*weight level 0 t (x+f s) (futurePath s f)*
        ENNReal.ofReal (x+f s-level)*F (x+f (s+t)) ∂pathLaw) =
      ∫⁻ y, ENNReal.ofReal (y-level)*(∫⁻ z, F z ∂law level 0 t y)
        ∂law level u s x :=
  mixed_insertion_eq_kernels level u 0 s t x
    (measurable_id.sub_const level).ennreal_ofReal hF

end PerronWright.BrownianKilledAreaDuhamelInsertion
