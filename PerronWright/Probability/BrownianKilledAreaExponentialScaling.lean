import PerronWright.Probability.BrownianKilledAreaScalingGeometry
import PerronWright.Probability.BrownianKilledAreaKernel

/-! # Genuine Brownian scaling of the killed-area Laplace kernels

The physical area parameter changes by the actual three-halves duration
factor. The measure remains the original surviving Brownian path weight.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaExponentialScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianKilledAreaGeometry
open BrownianKilledAreaKernel BrownianKilledAreaScalingGeometry ContinuousPathFirstPassage

theorem weight_brownianDilation (level x : ℝ) (u c t : ℝ≥0) (hc : 0 < c) (f : Path) :
    weight (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x) (brownianDilation c f) =
      weight level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x f := by
  by_cases hf : f ∈ survival (level-x) t
  · have hd := (survival_brownianDilation_scaled_duration level x c t hc f).mpr hf
    rw [weight,indicator_of_mem hd,shiftedArea_brownianDilation_scaled_duration level x c t hc f,
      weight,indicator_of_mem hf,NNReal.coe_mul,
      Real.coe_toNNReal _ (Real.rpow_nonneg c.coe_nonneg _)]
    congr 2
    ring
  · have hd := (survival_brownianDilation_scaled_duration level x c t hc f).not.mpr hf
    simp only [weight,indicator_of_notMem hd,indicator_of_notMem hf]

theorem law_lintegral_scaling (level x : ℝ) (u c t : ℝ≥0) (hc : 0 < c)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂law (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x)) =
      ∫⁻ y, F (Real.sqrt (c : ℝ)*y) ∂law level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x := by
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  let G : Path → ℝ≥0∞ := fun f ↦
    weight (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x) f *
      F (Real.sqrt (c : ℝ)*x+f (c*t))
  have hG : Measurable G :=
    (measurable_weight _ u _ _).mul
      (hF.comp (measurable_const.add (continuous_eval (c*t)).measurable))
  have hbase := law_lintegral level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x (hF.comp hscale)
  simp only [Function.comp_def] at hbase
  rw [law_lintegral _ u _ _ hF,hbase]
  change (∫⁻ f, G f ∂pathLaw) = _
  calc
    (∫⁻ f, G f ∂pathLaw) = ∫⁻ f, G f ∂pathLaw.map (brownianDilation c) := by
      rw [pathLaw_brownianDilation c hc]
    _ = ∫⁻ f, G (brownianDilation c f) ∂pathLaw :=
      lintegral_map hG (measurable_brownianDilation c)
    _ = _ := by
      apply lintegral_congr
      intro f
      dsimp only [G]
      rw [weight_brownianDilation level x u c t hc f,
        endpoint_brownianDilation_scaled_duration x c t hc f]

theorem law_scaling (level x : ℝ) (u c t : ℝ≥0) (hc : 0 < c) :
    law (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x) =
      (law level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x).map
        (fun y ↦ Real.sqrt (c : ℝ)*y) := by
  ext B hB
  have hF : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hB
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  have h := law_lintegral_scaling level x u c t hc hF
  rw [← lintegral_map hF hscale] at h
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using h

theorem law_duration_scaling (level x : ℝ) (u T : ℝ≥0) (hT : 0 < T) :
    law level u T x =
      (law (level/Real.sqrt (T : ℝ)) (u*Real.toNNReal ((T : ℝ)^(3/2 : ℝ)))
        1 (x/Real.sqrt (T : ℝ))).map (fun y ↦ Real.sqrt (T : ℝ)*y) := by
  have hs : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hT)
  have hl : Real.sqrt (T : ℝ)*(level/Real.sqrt (T : ℝ)) = level := by field_simp
  have hx : Real.sqrt (T : ℝ)*(x/Real.sqrt (T : ℝ)) = x := by field_simp
  simpa only [hl,hx,mul_one] using
    law_scaling (level/Real.sqrt (T : ℝ)) (x/Real.sqrt (T : ℝ)) u T 1 hT

theorem areaKernel_scaling (level x : ℝ) (u c t : ℝ≥0) (hc : 0 < c) :
    areaKernel (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x) =
      (areaKernel level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x).map
        (fun y ↦ Real.sqrt (c : ℝ)*y) :=
  law_scaling level x u c t hc

theorem law_integral_scaling (level x : ℝ) (u c t : ℝ≥0) (hc : 0 < c)
    {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ y, F y ∂law (Real.sqrt (c : ℝ)*level) u (c*t) (Real.sqrt (c : ℝ)*x)) =
      ∫ y, F (Real.sqrt (c : ℝ)*y) ∂law level (u*Real.toNNReal ((c : ℝ)^(3/2 : ℝ))) t x := by
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  rw [law_scaling level x u c t hc,integral_map hscale.aemeasurable hF.aestronglyMeasurable]

end PerronWright.BrownianKilledAreaExponentialScaling
