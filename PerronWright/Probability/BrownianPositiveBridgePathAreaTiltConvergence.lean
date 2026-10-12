import PerronWright.Probability.BrownianPositiveBridgeAreaTiltedTransfer

/-! # Actual whole-path area tilts converge weakly

Probability-valued source families use an irrelevant fallback only outside
the proved integrable endpoint neighborhood. On that neighborhood their
measures are the literal positive bridge area tilts. Actual weighted tests
give weak path convergence, hence weak area-law convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveBridgePathAreaTiltConvergence

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaExponentialSquare BrownianPositiveBridgeAreaFactorialGrowth
open BrownianPositiveBridgeAreaExponentialTails BrownianPositiveBridgePathConvergence
open BrownianPositiveBridgeWeakClusterSupport BrownianPositiveBridgeAreaLawIdentification
open BrownianPositiveBridgeAreaTiltedTransfer WeakContinuousSquareIntegralTransfer
open ContinuousPathAreaContinuity

def entranceTiltedPathProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) : ProbabilityMeasure Path :=
  ⟨(BrownianEntranceContinuousRealization.pathLaw T hT).tilted (fun f ↦ u*pathArea T f),
    entrance_area_tilt_isProbability T hT u⟩

def sourceTiltedPathProbability (T : ℝ≥0) (hT : 0 < T) (u a : ℝ) : ProbabilityMeasure Path :=
  if ha : 0 < a then
    if hi : Integrable (fun f : Path ↦ Real.exp (u*pathArea T f)) (positiveBridgeLaw a T) then
      letI := positiveBridgeLaw_isProbability a ha T hT
      ⟨(positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f),isProbabilityMeasure_tilted hi⟩
    else entranceTiltedPathProbability T hT u
  else entranceTiltedPathProbability T hT u

theorem sourceTiltedPathProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (u a : ℝ)
    (ha : 0 < a)
    (hi : Integrable (fun f : Path ↦ Real.exp (u*pathArea T f)) (positiveBridgeLaw a T)) :
    (sourceTiltedPathProbability T hT u a : Measure Path) =
      (positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f) := by
  simp only [sourceTiltedPathProbability,dif_pos ha,dif_pos hi]
  rfl

theorem eventually_sourceTiltedPathProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (sourceTiltedPathProbability T hT u a : Measure Path) =
        (positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f) := by
  filter_upwards [self_mem_nhdsWithin,eventually_area_exp_integrable T hT u] with a ha hi
  exact sourceTiltedPathProbability_toMeasure T hT u a ha hi

private theorem weighted_path_test_square_pointwise (T : ℝ≥0) (u : ℝ)
    (Φ : Path →ᵇ ℝ) (f : Path) :
    (Real.exp (u*pathArea T f)*Φ f)^2 ≤
      (‖Φ‖^2*Real.exp (u^2/areaSquareParameter T))*
        Real.exp (areaSquareParameter T*pathArea T f^2) := by
  have hs : (Φ f)^2 ≤ ‖Φ‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (Φ f)) (Φ.norm_coe_le_norm f) 2
  have he : (Real.exp (u*pathArea T f))^2 = Real.exp (2*u*pathArea T f) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [mul_pow,he]
  calc
    _ ≤ Real.exp (2*u*pathArea T f)*‖Φ‖^2 :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ ≤ (Real.exp (u^2/areaSquareParameter T)*
        Real.exp (areaSquareParameter T*pathArea T f^2))*‖Φ‖^2 :=
      mul_le_mul_of_nonneg_right
        (exponential_linear_square_bound _ u _ (areaSquareParameter_pos T)) (sq_nonneg _)
    _ = _ := by ring

theorem actual_weighted_path_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (Φ : Path →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, Real.exp (u*pathArea T f)*Φ f ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫ f : Path, Real.exp (u*pathArea T f)*Φ f
        ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  let K := ‖Φ‖^2*Real.exp (u^2/areaSquareParameter T)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f : Path, ENNReal.ofReal ((Real.exp (u*pathArea T f)*Φ f)^2)
        ∂(bridgeProbability T hT a : Measure Path)) ≤
      ENNReal.ofReal (K*(4*areaGrowthConstant T)) := by
    filter_upwards [self_mem_nhdsWithin,eventually_uniform_area_exp_square_bound T hT] with a ha hb
    rw [bridgeProbability_toMeasure T hT a ha]
    calc
      _ ≤ ∫⁻ f : Path, ENNReal.ofReal K*ENNReal.ofReal
          (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂positiveBridgeLaw a T := by
        apply lintegral_mono
        intro f
        dsimp only
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (weighted_path_test_square_pointwise T u Φ f)
      _ = ENNReal.ofReal K*(∫⁻ f : Path, ENNReal.ofReal
          (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂positiveBridgeLaw a T) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K*ENNReal.ofReal (4*areaGrowthConstant T) := mul_le_mul' le_rfl hb
      _ = _ := (ENNReal.ofReal_mul hK).symm
  have ht := tendsto_integral_of_uniform_square_bound
    (bridgeProbability T hT) (entranceProbability T hT) (tendsto_positiveBridgeProbability T hT)
    (fun f ↦ Real.exp (u*pathArea T f)*Φ f)
    ((Real.continuous_exp.comp ((continuous_pathArea T).const_mul u)).mul Φ.continuous)
    (K*(4*areaGrowthConstant T)) (by have := areaGrowthConstant_ge_one T; positivity) hs
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [bridgeProbability_toMeasure T hT a ha]

private theorem integral_tilted_path_test (T : ℝ≥0) (u : ℝ) (Φ : Path →ᵇ ℝ) (μ : Measure Path) :
    (∫ f, Φ f ∂μ.tilted (fun f ↦ u*pathArea T f)) =
      (∫ f, Real.exp (u*pathArea T f)*Φ f ∂μ)/
        (∫ f, Real.exp (u*pathArea T f) ∂μ) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div]
  exact integral_div _ _

theorem actual_tilted_path_test_integral_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (Φ : Path →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, Φ f
      ∂(positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f)) (𝓝[>] 0)
      (𝓝 (∫ f : Path, Φ f
        ∂(BrownianEntranceContinuousRealization.pathLaw T hT).tilted
          (fun f ↦ u*pathArea T f))) := by
  simp_rw [integral_tilted_path_test]
  exact (actual_weighted_path_test_tendsto T hT u Φ).div
    (actual_area_exp_normalizer_tendsto T hT u) (entrance_area_exp_normalizer_pos T hT u).ne'

theorem tendsto_sourceTiltedPathProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Tendsto (sourceTiltedPathProbability T hT u) (𝓝[>] 0)
      (𝓝 (entranceTiltedPathProbability T hT u)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro Φ
  apply (actual_tilted_path_test_integral_tendsto T hT u Φ).congr'
  filter_upwards [eventually_sourceTiltedPathProbability_toMeasure T hT u] with a ha
  rw [ha]

def sourceTiltedAreaProbability (T : ℝ≥0) (hT : 0 < T) (u a : ℝ) : ProbabilityMeasure ℝ :=
  (sourceTiltedPathProbability T hT u a).map (measurable_pathArea T).aemeasurable

def entranceTiltedAreaProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) : ProbabilityMeasure ℝ :=
  (entranceTiltedPathProbability T hT u).map (measurable_pathArea T).aemeasurable

theorem entranceTiltedAreaProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (entranceTiltedAreaProbability T hT u : Measure ℝ) =
      ((BrownianEntranceContinuousRealization.pathLaw T hT).tilted
        (fun f ↦ u*pathArea T f)).map (pathArea T) := rfl

theorem eventually_sourceTiltedAreaProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (sourceTiltedAreaProbability T hT u a : Measure ℝ) =
        ((positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f)).map (pathArea T) := by
  filter_upwards [eventually_sourceTiltedPathProbability_toMeasure T hT u] with a ha
  change (sourceTiltedPathProbability T hT u a : Measure Path).map (pathArea T) = _
  rw [ha]

theorem tendsto_sourceTiltedAreaProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Tendsto (sourceTiltedAreaProbability T hT u) (𝓝[>] 0)
      (𝓝 (entranceTiltedAreaProbability T hT u)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (sourceTiltedPathProbability T hT u) (entranceTiltedPathProbability T hT u)
    (tendsto_sourceTiltedPathProbability T hT u) (continuous_pathArea T)

end PerronWright.BrownianPositiveBridgePathAreaTiltConvergence
