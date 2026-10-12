import PerronWright.Probability.BrownianPositiveBridgeAreaExponentialSquare

/-! # Genuine exponential area tails on one endpoint neighborhood

Completion of the square turns the proved actual Gaussian-square integral
into a uniform real-tilt tail bound, for every real tilt and every cutoff.
The limiting measure is the constructed entrance law, not an asserted
Vervaat law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveBridgeAreaExponentialTails

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaExponentialSquare BrownianPositiveBridgeAreaFactorialGrowth
open BrownianPositiveBridgeAreaMomentTails

theorem exponential_linear_square_bound (c u x : ℝ) (hc : 0 < c) :
    Real.exp (2*u*x) ≤ Real.exp (u^2/c)*Real.exp (c*x^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : 2*u*x ≤ (u^2+c^2*x^2)/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [sq_nonneg (c*x-u)]
  calc
    _ ≤ (u^2+c^2*x^2)/c := h
    _ = _ := by field_simp

theorem exponential_linear_tail_bound (c u x B : ℝ) (hc : 0 < c)
    (hB : 0 ≤ B) (hcut : B ≤ |x|) :
    Real.exp (u*x) ≤ Real.exp (u^2/(2*c)-c*B^2/2)*Real.exp (c*x^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx : B^2 ≤ x^2 := by
    calc _ ≤ |x|^2 := pow_le_pow_left₀ hB hcut 2
         _ = _ := sq_abs x
  have h : u*x ≤ (u^2+c^2*x^2)/(2*c) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
    nlinarith [sq_nonneg (c*x-u)]
  have he : (u^2+c^2*x^2)/(2*c) = u^2/(2*c)+c*x^2/2 := by
    field_simp
  rw [he] at h
  nlinarith

def areaLinearTailConstant (T : ℝ≥0) (u B : ℝ) : ℝ :=
  4*areaGrowthConstant T*Real.exp (u^2/(2*areaSquareParameter T)-areaSquareParameter T*B^2/2)

theorem areaLinearTailConstant_tendsto_zero (T : ℝ≥0) (u : ℝ) :
    Tendsto (areaLinearTailConstant T u) atTop (𝓝 0) := by
  have hc := areaSquareParameter_pos T
  have hp : Tendsto (fun B : ℝ ↦ (-areaSquareParameter T/2)*B^2) atTop atBot :=
    tendsto_neg_const_mul_pow_atTop (by decide) (by linarith)
  have he : Tendsto (fun B : ℝ ↦ u^2/(2*areaSquareParameter T)-areaSquareParameter T*B^2/2)
      atTop atBot := by
    apply tendsto_atBot.mpr
    intro r
    filter_upwards [(tendsto_atBot.mp hp) (r-u^2/(2*areaSquareParameter T))] with B hB
    linarith
  change Tendsto (fun B : ℝ ↦ 4*areaGrowthConstant T*Real.exp
    (u^2/(2*areaSquareParameter T)-areaSquareParameter T*B^2/2)) atTop (𝓝 0)
  simpa only [Function.comp_def,mul_zero] using
    (Real.tendsto_exp_atBot.comp he).const_mul (4*areaGrowthConstant T)

private theorem actual_linear_tail_bound_of_square_bound
    (T : ℝ≥0) (u : ℝ) (μ : Measure Path)
    (hs : (∫⁻ f, ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂μ)
      ≤ ENNReal.ofReal (4*areaGrowthConstant T)) (B : ℝ) (hB : 0 ≤ B) :
    (∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (Real.exp (u*pathArea T f)) ∂μ)
      ≤ ENNReal.ofReal (areaLinearTailConstant T u B) := by
  let K := Real.exp (u^2/(2*areaSquareParameter T)-areaSquareParameter T*B^2/2)
  calc
    _ ≤ ∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal K*
        ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_area_tail T B)] with f hf
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal
        (exponential_linear_tail_bound _ u _ B (areaSquareParameter_pos T) hB hf)
    _ ≤ ∫⁻ f, ENNReal.ofReal K*
        ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂μ :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal K*(∫⁻ f, ENNReal.ofReal
        (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (4*areaGrowthConstant T) := mul_le_mul' le_rfl hs
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      exact mul_comm _ _

theorem eventually_uniform_area_exp_tail_bound (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ B : ℝ, 0 ≤ B →
      (∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (Real.exp (u*pathArea T f))
        ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal (areaLinearTailConstant T u B) := by
  filter_upwards [eventually_uniform_area_exp_square_bound T hT] with a ha
  exact actual_linear_tail_bound_of_square_bound T u _ ha

theorem entrance_area_exp_tail_bound (T : ℝ≥0) (hT : 0 < T) (u B : ℝ) (hB : 0 ≤ B) :
    (∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (Real.exp (u*pathArea T f))
      ∂BrownianEntranceContinuousRealization.pathLaw T hT)
        ≤ ENNReal.ofReal (areaLinearTailConstant T u B) :=
  actual_linear_tail_bound_of_square_bound T u _ (entrance_area_exp_square_bound T hT) B hB

theorem eventually_area_exp_integrable (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      Integrable (fun f : Path ↦ Real.exp (u*pathArea T f)) (positiveBridgeLaw a T) := by
  filter_upwards [eventually_uniform_area_exp_tail_bound T hT u] with a ha
  refine ⟨((measurable_pathArea T).const_mul u).exp.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mpr
  have hb := ha 0 le_rfl
  have he : {f : Path | (0:ℝ) ≤ |pathArea T f|} = univ := by ext f; simp
  rw [he,Measure.restrict_univ] at hb
  exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top

theorem entrance_area_exp_integrable (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Integrable (fun f : Path ↦ Real.exp (u*pathArea T f))
      (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  refine ⟨((measurable_pathArea T).const_mul u).exp.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mpr
  have hb := entrance_area_exp_tail_bound T hT u 0 le_rfl
  have he : {f : Path | (0:ℝ) ≤ |pathArea T f|} = univ := by ext f; simp
  rw [he,Measure.restrict_univ] at hb
  exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top

theorem actual_area_exp_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ᶠ a : ℝ in 𝓝[>] 0,
        (∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (Real.exp (u*pathArea T f))
          ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal ε) ∧
      (∫⁻ f in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (Real.exp (u*pathArea T f))
        ∂BrownianEntranceContinuousRealization.pathLaw T hT) ≤ ENNReal.ofReal ε := by
  have he : ∀ᶠ B : ℝ in atTop, areaLinearTailConstant T u B < ε :=
    (areaLinearTailConstant_tendsto_zero T u).eventually (gt_mem_nhds hε)
  obtain ⟨B,hB,hsmall⟩ := (he.and (eventually_ge_atTop 0)).exists
  refine ⟨B,hsmall,?_,?_⟩
  · filter_upwards [eventually_uniform_area_exp_tail_bound T hT u] with a ha
    exact (ha B hsmall).trans (ENNReal.ofReal_le_ofReal hB.le)
  · exact (entrance_area_exp_tail_bound T hT u B hsmall).trans (ENNReal.ofReal_le_ofReal hB.le)

end PerronWright.BrownianPositiveBridgeAreaExponentialTails
