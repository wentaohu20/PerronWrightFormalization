import PerronWright.Probability.BrownianPositiveBridgeAreaFactorialGrowth
import PerronWright.Probability.BrownianPositiveBridgeAreaLawIdentification

/-! # Genuine uniform exponential-square control of positive bridge area

The actual exponential series is integrated by Tonelli on the common
endpoint neighborhood. Weak convergence transfers the proved finite bound
to the constructed entrance-path law, without a Vervaat identification.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveBridgeAreaExponentialSquare

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaFactorialGrowth BrownianPositiveBridgeAreaLawIdentification
open BrownianPositiveBridgeWeakClusterSupport BrownianPositiveBridgePathConvergence
open WeakContinuousMomentIdentification ContinuousPathAreaContinuity

def areaSquareParameter (T : ℝ≥0) : ℝ := 1/(2*areaGrowthBase T)

theorem areaSquareParameter_pos (T : ℝ≥0) : 0 < areaSquareParameter T := by
  have := areaGrowthBase_pos T
  unfold areaSquareParameter
  positivity

private theorem exponential_square_series (c x : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal (Real.exp (c*x^2)) =
      ∑' n : ℕ, ENNReal.ofReal (c^n/(n.factorial:ℝ))*ENNReal.ofReal (|x|^(2*n)) := by
  have heq (n : ℕ) : (c*x^2)^n/(n.factorial:ℝ) =
      (c^n/(n.factorial:ℝ))*|x|^(2*n) := by
    rw [mul_pow,pow_mul,sq_abs]
    ring
  have hmul (n : ℕ) : ENNReal.ofReal (c^n/(n.factorial:ℝ))*ENNReal.ofReal (|x|^(2*n)) =
      ENNReal.ofReal ((c^n/(n.factorial:ℝ))*|x|^(2*n)) :=
    (ENNReal.ofReal_mul (by positivity)).symm
  simp_rw [hmul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) (by
    convert! Real.summable_pow_div_factorial (c*x^2) using 1
    funext n
    exact (heq n).symm)]
  congr 1
  rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
  exact tsum_congr heq

theorem lintegral_actual_area_exp_square_series (T : ℝ≥0) (a c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ f : Path, ENNReal.ofReal (Real.exp (c*pathArea T f^2)) ∂positiveBridgeLaw a T) =
      ∑' n : ℕ, ENNReal.ofReal (c^n/(n.factorial:ℝ))*
        (∫⁻ f : Path, ENNReal.ofReal (|pathArea T f|^(2*n)) ∂positiveBridgeLaw a T) := by
  simp_rw [exponential_square_series c _ hc]
  have hm (n : ℕ) : Measurable (fun f : Path ↦ ENNReal.ofReal (c^n/(n.factorial:ℝ))*
      ENNReal.ofReal (|pathArea T f|^(2*n))) :=
    measurable_const.mul ((measurable_pathArea T).abs.pow_const (2*n)).ennreal_ofReal
  rw [lintegral_tsum (fun n ↦ (hm n).aemeasurable)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem hasSum_half_majorant (C : ℝ) :
    HasSum (fun n : ℕ ↦ C*((n+1:ℕ):ℝ)*(1/2:ℝ)^n) (4*C) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left C
  convert! h using 1
  · funext n
    simp
    ring
  · norm_num
    ring

private theorem square_parameter_factorial_balance (T : ℝ≥0) (n : ℕ) :
    ((areaSquareParameter T)^n/(n.factorial:ℝ))*
      (areaGrowthConstant T*(areaGrowthBase T)^n*((n+1).factorial:ℝ)) =
        areaGrowthConstant T*((n+1:ℕ):ℝ)*(1/2:ℝ)^n := by
  have hD := (areaGrowthBase_pos T).ne'
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  have hprod : (areaSquareParameter T)^n*(areaGrowthBase T)^n = (1/2:ℝ)^n := by
    rw [← mul_pow]
    congr 1
    unfold areaSquareParameter
    field_simp
  rw [Nat.factorial_succ,Nat.cast_mul]
  calc
    _ = areaGrowthConstant T*((n+1:ℕ):ℝ)*((areaSquareParameter T)^n*(areaGrowthBase T)^n) := by
      field_simp
    _ = _ := by rw [hprod]

theorem eventually_uniform_area_exp_square_bound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f : Path, ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2))
        ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal (4*areaGrowthConstant T) := by
  filter_upwards [eventually_all_area_even_factorial_growth_including_zero T hT] with a ha
  have hc := areaSquareParameter_pos T
  rw [lintegral_actual_area_exp_square_series T a _ (areaSquareParameter_pos T).le]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((areaSquareParameter T)^n/(n.factorial:ℝ))*
        ENNReal.ofReal (areaGrowthConstant T*(areaGrowthBase T)^n*((n+1).factorial:ℝ)) := by
      exact ENNReal.tsum_le_tsum (fun n ↦ mul_le_mul' le_rfl (ha n))
    _ = ∑' n : ℕ, ENNReal.ofReal (areaGrowthConstant T*((n+1:ℕ):ℝ)*(1/2:ℝ)^n) := by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_mul (by positivity),square_parameter_factorial_balance]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by
        have := areaGrowthConstant_ge_one T
        positivity) (hasSum_half_majorant (areaGrowthConstant T)).summable,
        (hasSum_half_majorant (areaGrowthConstant T)).tsum_eq]

theorem eventually_area_exp_square_integrable (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      Integrable (fun f : Path ↦ Real.exp (areaSquareParameter T*pathArea T f^2))
        (positiveBridgeLaw a T) := by
  filter_upwards [eventually_uniform_area_exp_square_bound T hT] with a ha
  refine ⟨((measurable_pathArea T).pow_const 2 |>.const_mul _ |>.exp).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mpr
  exact lt_of_le_of_lt ha ENNReal.ofReal_lt_top

theorem entrance_area_exp_square_bound (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ f : Path, ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2))
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) ≤ ENNReal.ofReal (4*areaGrowthConstant T) := by
  apply target_lintegral_le_of_eventual_bound (bridgeProbability T hT) (entranceProbability T hT)
    (tendsto_positiveBridgeProbability T hT)
    (fun f ↦ Real.exp (areaSquareParameter T*pathArea T f^2))
    (Real.continuous_exp.comp (((continuous_pathArea T).pow 2).const_mul _))
    (fun _ ↦ (Real.exp_pos _).le)
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_area_exp_square_bound T hT] with a ha hb
  rw [bridgeProbability_toMeasure T hT a ha]
  exact hb

theorem entrance_area_exp_square_integrable (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun f : Path ↦ Real.exp (areaSquareParameter T*pathArea T f^2))
      (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  refine ⟨((measurable_pathArea T).pow_const 2 |>.const_mul _ |>.exp).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mpr
  exact lt_of_le_of_lt (entrance_area_exp_square_bound T hT) ENNReal.ofReal_lt_top

end PerronWright.BrownianPositiveBridgeAreaExponentialSquare
