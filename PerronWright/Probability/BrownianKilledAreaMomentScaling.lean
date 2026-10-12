import PerronWright.Probability.BrownianKilledAreaScalingGeometry
import PerronWright.Probability.BrownianKilledAreaMomentFiniteness

/-! # All-order scaling of the actual killed Brownian moment laws

The genuine whole Brownian path law under dilation is combined with
pathwise survival, area and endpoint identities. No area-law scaling
or moment-kernel scaling is provided as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianKilledAreaGeometry
open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentFiniteness
open BrownianKilledAreaScalingGeometry ContinuousPathFirstPassage

theorem momentWeight_brownianDilation (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c)
    (n : ℕ) (f : Path) :
    momentWeight (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x) (brownianDilation c f) =
      ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n * momentWeight level n t x f := by
  by_cases hf : f ∈ survival (level-x) t
  · have hd := (survival_brownianDilation_scaled_duration level x c t hc f).mpr hf
    rw [momentWeight,indicator_of_mem hd,shiftedArea_brownianDilation_scaled_duration level x c t hc f,
      ENNReal.ofReal_mul (Real.rpow_nonneg c.coe_nonneg _),mul_pow,
      momentWeight,indicator_of_mem hf]
  · have hd := (survival_brownianDilation_scaled_duration level x c t hc f).not.mpr hf
    simp only [momentWeight,indicator_of_notMem hd,indicator_of_notMem hf,mul_zero]

theorem momentLaw_lintegral_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂momentLaw (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x)) =
      ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n *
        ∫⁻ y, F (Real.sqrt (c : ℝ)*y) ∂momentLaw level n t x := by
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := measurable_id.const_mul _
  let G : Path → ℝ≥0∞ := fun f ↦
    momentWeight (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x) f *
      F (Real.sqrt (c : ℝ)*x+f (c*t))
  have hG : Measurable G :=
    (measurable_momentWeight _ n _ _).mul
      (hF.comp (measurable_const.add (continuous_eval (c*t)).measurable))
  have hbase : Measurable (fun f : Path ↦ momentWeight level n t x f * F (Real.sqrt (c : ℝ)*(x+f t))) :=
    (measurable_momentWeight level n t x).mul
      (hF.comp (hscale.comp (measurable_const.add (continuous_eval t).measurable)))
  have hbaseLaw := momentLaw_lintegral level n t x (hF.comp hscale)
  simp only [Function.comp_def] at hbaseLaw
  rw [momentLaw_lintegral _ n _ _ hF,hbaseLaw]
  change (∫⁻ f, G f ∂pathLaw) = _
  calc
    (∫⁻ f, G f ∂pathLaw) = ∫⁻ f, G f ∂pathLaw.map (brownianDilation c) := by
      rw [pathLaw_brownianDilation c hc]
    _ = ∫⁻ f, G (brownianDilation c f) ∂pathLaw :=
      lintegral_map hG (measurable_brownianDilation c)
    _ = ∫⁻ f, ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n *
        (momentWeight level n t x f * F (Real.sqrt (c : ℝ)*(x+f t))) ∂pathLaw := by
      apply lintegral_congr
      intro f
      dsimp only [G]
      rw [momentWeight_brownianDilation level x c t hc n f,
        endpoint_brownianDilation_scaled_duration x c t hc f,mul_assoc]
    _ = _ := lintegral_const_mul _ hbase

/-- Exact pushforward identity for the original surviving-path moment law.
It holds for every order and every duration, including duration zero. -/
theorem momentLaw_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ) :
    momentLaw (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x) =
      ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n •
        (momentLaw level n t x).map (fun y ↦ Real.sqrt (c : ℝ)*y) := by
  ext B hB
  have hF : Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hB
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  have h := momentLaw_lintegral_scaling level x c t hc n hF
  rw [← lintegral_map hF hscale] at h
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ,
    Measure.smul_apply,smul_eq_mul] using h

theorem momentLaw_apply_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    momentLaw (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x) B =
      ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n *
        momentLaw level n t x ((fun y ↦ Real.sqrt (c : ℝ)*y) ⁻¹' B) := by
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  rw [momentLaw_scaling level x c t hc n,Measure.smul_apply,
    Measure.map_apply hscale hB]
  rfl

theorem momentLaw_duration_scaling (level x : ℝ) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    momentLaw level n T x = ENNReal.ofReal ((T : ℝ)^(3/2 : ℝ))^n •
      (momentLaw (level/Real.sqrt (T : ℝ)) n 1 (x/Real.sqrt (T : ℝ))).map
        (fun y ↦ Real.sqrt (T : ℝ)*y) := by
  have hs : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hT)
  have hl : Real.sqrt (T : ℝ)*(level/Real.sqrt (T : ℝ)) = level := by field_simp
  have hx : Real.sqrt (T : ℝ)*(x/Real.sqrt (T : ℝ)) = x := by field_simp
  simpa only [hl,hx,mul_one] using
    momentLaw_scaling (level/Real.sqrt (T : ℝ)) (x/Real.sqrt (T : ℝ)) T 1 hT n

theorem momentKernel_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ) :
    momentKernel (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x) =
      ENNReal.ofReal ((c : ℝ)^(3/2 : ℝ))^n •
        (momentKernel level n t x).map (fun y ↦ Real.sqrt (c : ℝ)*y) :=
  momentLaw_scaling level x c t hc n

theorem momentLaw_integral_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ y, F y ∂momentLaw (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x)) =
      ((c : ℝ)^(3/2 : ℝ))^n * ∫ y, F (Real.sqrt (c : ℝ)*y) ∂momentLaw level n t x := by
  have hscale : Measurable (fun y : ℝ ↦ Real.sqrt (c : ℝ)*y) := by fun_prop
  rw [momentLaw_scaling level x c t hc n,integral_smul_measure,
    integral_map hscale.aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal (Real.rpow_nonneg c.coe_nonneg _)]
  rfl

theorem momentLaw_totalMass_scaling (level x : ℝ) (c t : ℝ≥0) (hc : 0 < c) (n : ℕ) :
    (momentLaw (Real.sqrt (c : ℝ)*level) n (c*t) (Real.sqrt (c : ℝ)*x)).real univ =
      ((c : ℝ)^(3/2 : ℝ))^n * (momentLaw level n t x).real univ := by
  have h := momentLaw_apply_scaling level x c t hc n MeasurableSet.univ
  simp only [preimage_univ] at h
  rw [Measure.real,h,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.rpow_nonneg c.coe_nonneg _)]
  rfl

end PerronWright.BrownianKilledAreaMomentScaling
