import PerronWright.Probability.BrownianKilledAreaDuhamelPath
import PerronWright.Probability.BrownianKilledAreaDuhamelInsertion

/-! # Duhamel insertion for the actual killed Brownian area kernel

The survival-gated path identity is integrated against the actual Brownian
path law. Joint measurability and Tonelli justify the time swap, and the
proved past/future product law evaluates the insertion. No stochastic
insertion, bridge law, or finite-moment hypothesis is supplied as input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaDuhamel

open BrownianPathLaw BrownianPathIndependentIncrements BrownianKilledAreaKernel
open BrownianKilledAreaDuhamelGeometry BrownianKilledAreaDuhamelPath
open BrownianKilledAreaDuhamelInsertion BrownianKilledAreaTimeKernel

theorem measurable_insertionWeight (level : ℝ) (u T : ℝ≥0) (x : ℝ) :
    Measurable (fun p : ℝ × Path ↦ insertionWeight level u T x p.1 p.2) := by
  have hs : Measurable (fun p : ℝ × Path ↦ Real.toNNReal p.1) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hy : Measurable (fun p : ℝ × Path ↦ x+p.2 (Real.toNNReal p.1)) :=
    measurable_const.add (continuous_joint_eval.measurable.comp
      (measurable_snd.prodMk hs))
  have hg : Measurable (fun p : ℝ × Path ↦ futurePath (Real.toNNReal p.1) p.2) :=
    continuous_time_futurePath.measurable.comp (hs.prodMk measurable_snd)
  exact (((measurable_time_state_weight level u).comp
    (hs.prodMk (measurable_const.prodMk measurable_snd))).mul
    ((measurable_time_state_weight level 0).comp
      ((measurable_const.sub hs).prodMk (hy.prodMk hg)))).mul
        (hy.sub_const level).ennreal_ofReal

theorem measurable_insertion_test (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × Path ↦
      insertionWeight level u T x p.1 p.2*F (x+p.2 T)) :=
  (measurable_insertionWeight level u T x).mul (hF.comp
    (measurable_const.add ((continuous_eval T).measurable.comp measurable_snd)))

theorem weight_depletion_test (level : ℝ) (u T : ℝ≥0) (x : ℝ) (f : Path)
    (F : ℝ → ℝ≥0∞) :
    weight level 0 T x f*F (x+f T) = weight level u T x f*F (x+f T)+
      ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
        insertionWeight level u T x r f*F (x+f T) := by
  have hm := (measurable_insertionWeight level u T x).comp
    (measurable_id.prodMk measurable_const : Measurable (fun r : ℝ ↦ (r,f)))
  have he : (∫⁻ r in Ioc 0 (T : ℝ),
      insertionWeight level u T x r f*F (x+f T)) =
      (∫⁻ r in Ioc 0 (T : ℝ), insertionWeight level u T x r f)*F (x+f T) :=
    lintegral_mul_const _ hm
  rw [weight_depletion,add_mul,he]
  ac_rfl

theorem path_lintegral_depletion (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, weight level 0 T x f*F (x+f T) ∂pathLaw) =
      (∫⁻ f, weight level u T x f*F (x+f T) ∂pathLaw)+
        ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
          ∫⁻ f, insertionWeight level u T x r f*F (x+f T) ∂pathLaw := by
  have hm := measurable_insertion_test level u T x hF
  have hw : Measurable (fun f : Path ↦ weight level u T x f*F (x+f T)) :=
    (measurable_weight level u T x).mul
    (hF.comp (measurable_const.add (continuous_eval T).measurable))
  have hg : Measurable (fun f : Path ↦ ∫⁻ r in Ioc 0 (T : ℝ),
      insertionWeight level u T x r f*F (x+f T)) :=
    (hm.comp measurable_swap).lintegral_prod_right'
  calc
    _ = ∫⁻ f, (weight level u T x f*F (x+f T)+
        ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
          insertionWeight level u T x r f*F (x+f T)) ∂pathLaw :=
      lintegral_congr (fun f ↦ weight_depletion_test level u T x f F)
    _ = (∫⁻ f, weight level u T x f*F (x+f T) ∂pathLaw)+
        ENNReal.ofReal (u : ℝ)*(∫⁻ f, (∫⁻ r in Ioc 0 (T : ℝ),
          insertionWeight level u T x r f*F (x+f T)) ∂pathLaw) := by
      rw [lintegral_add_left hw,lintegral_const_mul _ hg]
    _ = _ := by
      rw [← lintegral_lintegral_swap
        (f := fun r : ℝ ↦ fun f : Path ↦ insertionWeight level u T x r f*F (x+f T))
        (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ))) (ν := pathLaw) hm.aemeasurable]

/-- The endpoint-test Duhamel equation for the literal Brownian kernel.
Nonnegative tests may be unbounded; Tonelli keeps the identity valid in
`ENNReal`, including zero duration and zero area parameter. -/
theorem law_lintegral_duhamel (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law level 0 T x) = (∫⁻ y, F y ∂law level u T x)+
      ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
        ∫⁻ y, ENNReal.ofReal (y-level)*
          (∫⁻ z, F z ∂law level 0 (T-Real.toNNReal r) y)
          ∂law level u (Real.toNNReal r) x := by
  rw [law_lintegral level 0 T x hF,law_lintegral level u T x hF,
    path_lintegral_depletion level u T x hF]
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hs : Real.toNNReal r ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
  have he := height_insertion_eq_kernels level u (Real.toNNReal r)
    (T-Real.toNNReal r) x hF
  rw [add_tsub_cancel_of_le hs] at he
  exact he

theorem law_apply_duhamel (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    law level 0 T x B = law level u T x B+
      ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
        ∫⁻ y, ENNReal.ofReal (y-level)*law level 0 (T-Real.toNNReal r) y B
          ∂law level u (Real.toNNReal r) x := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    law_lintegral_duhamel level u T x
      (measurable_const.indicator hB : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

end PerronWright.BrownianKilledAreaDuhamel
