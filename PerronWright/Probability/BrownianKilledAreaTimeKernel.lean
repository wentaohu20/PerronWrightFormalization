import PerronWright.Probability.BrownianKilledAreaDuhamelGeometry

/-! # Actual jointly measurable duration/state area kernel

Joint path-area quadratures and endpoint evaluation prove duration/state
measurability of the literal area-weighted Brownian endpoint law. This
supplies the genuine measurable kernel needed for time-insertion integrals.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaTimeKernel

open BrownianPathLaw BrownianKilledAreaKernel BrownianKilledAreaDuhamelGeometry

theorem measurable_time_state_law_lintegral (level : ℝ) (u : ℝ≥0)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ≥0 × ℝ ↦ ∫⁻ y, F y ∂law level u p.1 p.2) := by
  have hw : Measurable (fun p : (ℝ≥0 × ℝ) × Path ↦ weight level u p.1.1 p.1.2 p.2) :=
    (measurable_time_state_weight level u).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hy : Measurable (fun p : (ℝ≥0 × ℝ) × Path ↦ p.1.2+p.2 p.1.1) :=
    (measurable_snd.comp measurable_fst).add
      (continuous_joint_eval.measurable.comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hm := hw.mul (hF.comp hy)
  have he : (fun p : ℝ≥0 × ℝ ↦ ∫⁻ y, F y ∂law level u p.1 p.2) =
      (fun p : ℝ≥0 × ℝ ↦ ∫⁻ f, weight level u p.1 p.2 f*F (p.2+f p.1) ∂pathLaw) :=
    funext (fun p ↦ law_lintegral level u p.1 p.2 hF)
  rw [he]
  exact hm.lintegral_prod_right'

theorem measurable_time_state_law_apply (level : ℝ) (u : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ≥0 × ℝ ↦ law level u p.1 p.2 B) := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    measurable_time_state_law_lintegral level u
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

def timeAreaKernel (level : ℝ) (u : ℝ≥0) : Kernel (ℝ≥0 × ℝ) ℝ :=
  ⟨fun p ↦ law level u p.1 p.2,Measure.measurable_measure.mpr
    (fun _ hB ↦ measurable_time_state_law_apply level u hB)⟩

@[simp] theorem timeAreaKernel_apply (level : ℝ) (u : ℝ≥0) (t : ℝ≥0) (x : ℝ) :
    timeAreaKernel level u (t,x) = law level u t x := rfl

instance timeAreaKernel_isFinite (level : ℝ) (u : ℝ≥0) : IsFiniteKernel (timeAreaKernel level u) :=
  ⟨⟨1,ENNReal.one_lt_top,fun p ↦ law_univ_le_one level u p.1 p.2⟩⟩

end PerronWright.BrownianKilledAreaTimeKernel
