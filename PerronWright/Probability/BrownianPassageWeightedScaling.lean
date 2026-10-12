import PerronWright.Probability.BrownianPassageLevelFirstMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Actual square-root scaling of level-weighted passage densities

The level-weighted passage source has mass one half. Its literal
square-root scaling and concentration at zero are proved from the
Gaussian density, the Lebesgue Jacobian, and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPassageWeightedScaling

open BrownianFirstPassageDensityGeometry BrownianPassageLevelFirstMoment

def weight (s a : ℝ) : ℝ≥0∞ := ENNReal.ofReal a*density a s

theorem measurable_weight (s : ℝ) : Measurable (weight s) := by
  unfold weight density densityReal argument
  by_cases hs : 0 < s
  · simp only [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    fun_prop
  · simp only [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs),
      ENNReal.ofReal_zero,mul_zero]
    exact measurable_const

def weightedLaw (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (weight s)

theorem weightedLaw_mass (s : ℝ) (hs : 0 < s) :
    weightedLaw s univ = ENNReal.ofReal (1/2 : ℝ) := by
  rw [weightedLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact lintegral_weighted_level_density s hs

theorem lintegral_weightedLaw (s : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a, F a ∂weightedLaw s) = ∫⁻ a in Ioi (0 : ℝ), weight s a*F a := by
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_weight s) hF

private theorem real_sqrt_scaling (s : ℝ) (hs : 0 < s) (x : ℝ) :
    Real.sqrt s*(Real.sqrt s*x*densityReal (Real.sqrt s*x) s) = x*densityReal x 1 := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hpi : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hexp : -(Real.sqrt s*x)^2/(2*s) = -x^2/2 := by
    rw [mul_pow,Real.sq_sqrt hs.le]
    field_simp
  rw [densityReal_explicit _ s hs,densityReal_explicit _ 1 (by norm_num),hexp]
  simp only [Real.sqrt_one,mul_one]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

theorem weight_sqrt_scaling (s : ℝ) (hs : 0 < s) (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (Real.sqrt s)*weight s (Real.sqrt s*x) = weight 1 x := by
  have hxs : 0 ≤ Real.sqrt s*x := by positivity
  unfold weight density
  rw [← ENNReal.ofReal_mul hxs,← ENNReal.ofReal_mul (Real.sqrt_nonneg s),
    real_sqrt_scaling s hs x,ENNReal.ofReal_mul hx.le]

theorem lintegral_sqrt_scaling (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ≥0∞) :
    (∫⁻ a in Ioi (0 : ℝ), weight s a*F a) =
      ∫⁻ x in Ioi (0 : ℝ), weight 1 x*F (Real.sqrt s*x) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have himage : (fun x : ℝ ↦ Real.sqrt s*x) '' Ioi 0 = Ioi 0 := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mul_pos hr hx
    · intro ha
      exact ⟨a/Real.sqrt s,div_pos ha hr,mul_div_cancel₀ a hr.ne'⟩
  have hinj : InjOn (fun x : ℝ ↦ Real.sqrt s*x) (Ioi 0) := by
    intro x _ y _ h
    exact mul_left_cancel₀ hr.ne' h
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x _ ↦ ((hasDerivAt_id x).const_mul (Real.sqrt s)).hasDerivWithinAt)
    hinj (fun a : ℝ ↦ weight s a*F a)
  simp only [id_eq,mul_one] at hj
  rw [himage] at hj
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt s)*(weight s (Real.sqrt s*x)*F (Real.sqrt s*x)) := by
      simpa only [mul_one,abs_of_pos hr] using hj
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [← mul_assoc,weight_sqrt_scaling s hs x hx]

theorem weightedLaw_sqrt_lintegral (s : ℝ) (hs : 0 < s)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a, F a ∂weightedLaw s) =
      ∫⁻ x, F (Real.sqrt s*x) ∂weightedLaw 1 := by
  rw [lintegral_weightedLaw s F hF,lintegral_sqrt_scaling s hs]
  exact (lintegral_weightedLaw 1 (fun x ↦ F (Real.sqrt s*x))
    (by fun_prop)).symm

theorem weighted_boundedContinuous_tendsto (Φ : (ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun s : ℝ ↦ ∫⁻ a, ENNReal.ofReal (Φ (s,a)) ∂weightedLaw s)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (Φ (0,0)))) := by
  have hm (s : ℝ) : Measurable (fun x : ℝ ↦ ENNReal.ofReal (Φ (s,Real.sqrt s*x))) := by
    fun_prop
  have hb (s x : ℝ) : ENNReal.ofReal (Φ (s,Real.sqrt s*x)) ≤ ENNReal.ofReal ‖Φ‖ :=
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (s,Real.sqrt s*x)))
  have hfin : (∫⁻ _x, ENNReal.ofReal ‖Φ‖ ∂weightedLaw 1) ≠ ⊤ := by
    rw [lintegral_const,weightedLaw_mass 1 (by norm_num)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ x ∂weightedLaw 1, Tendsto
      (fun s : ℝ ↦ ENNReal.ofReal (Φ (s,Real.sqrt s*x))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Φ (0,0)))) := by
    apply Eventually.of_forall
    intro x
    apply ENNReal.tendsto_ofReal
    apply Φ.continuous.continuousAt.tendsto.comp
    have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [id_eq,Real.sqrt_zero,zero_mul] using
      (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds (hs.mul_const x)
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (μ := weightedLaw 1) (fun _x ↦ ENNReal.ofReal ‖Φ‖)
    (Eventually.of_forall hm) (Eventually.of_forall (fun s ↦ Eventually.of_forall (hb s))) hfin hlim
  simp only [lintegral_const,weightedLaw_mass 1 (by norm_num)] at ht
  have he : (fun s : ℝ ↦ ∫⁻ a, ENNReal.ofReal (Φ (s,a)) ∂weightedLaw s) =ᶠ[𝓝[>] 0]
      (fun s : ℝ ↦ ∫⁻ x, ENNReal.ofReal (Φ (s,Real.sqrt s*x)) ∂weightedLaw 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact weightedLaw_sqrt_lintegral s hs _ (by fun_prop)
  simpa only [mul_comm] using ht.congr' he.symm

end PerronWright.BrownianPassageWeightedScaling
