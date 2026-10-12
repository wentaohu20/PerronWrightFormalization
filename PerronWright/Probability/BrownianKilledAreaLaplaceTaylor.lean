import PerronWright.Probability.BrownianKilledAreaLaplaceTaylorGeometry
import PerronWright.Probability.BrownianKilledAreaMomentRealKernel
import PerronWright.Probability.BrownianKilledAreaKernel

/-! # Actual all-order Taylor bounds for Brownian area Laplace kernels

All coefficients are integrals against the original surviving-path moment
measures. Their proved Gaussian finiteness justifies the finite polynomial
integral. The error is controlled by the next genuine moment, for every
bounded real Borel endpoint test and every nonnegative area parameter.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaLaplaceTaylor

open BrownianPathLaw BrownianKilledAreaGeometry BrownianKilledAreaKernel
open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentFiniteness
open BrownianKilledAreaMomentRealKernel BrownianKilledAreaLaplaceTaylorGeometry
open ContinuousPathFirstPassage

theorem integrable_weighted_test (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) :
    Integrable (fun f : Path ↦ (weight level u T x f).toReal*F (x+f T)) pathLaw := by
  have hCn : 0 ≤ C := (abs_nonneg (F 0)).trans (hC 0)
  apply (integrable_const C).mono'
  · exact ((measurable_weight level u T x).ennreal_toReal.mul
      (hF.comp (measurable_const.add (continuous_eval T).measurable))).aestronglyMeasurable
  · apply ae_of_all
    intro f
    have hw : (weight level u T x f).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        (weight_le_one level u T x f)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (mul_le_mul hw (hC (x+f T)) (abs_nonneg _) (by norm_num)).trans_eq (one_mul C)

theorem integrable_moment_path_test (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) :
    Integrable (fun f : Path ↦ (momentWeight level n T x f).toReal*F (x+f T)) pathLaw := by
  apply ((integrable_momentWeight_toReal level n T x).mul_const C).mono'
  · exact ((measurable_momentWeight level n T x).ennreal_toReal.mul
      (hF.comp (measurable_const.add (continuous_eval T).measurable))).aestronglyMeasurable
  · apply ae_of_all
    intro f
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hC (x+f T)) ENNReal.toReal_nonneg

theorem law_integral_eq_path_integral (level : ℝ) (u T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ y, F y ∂law level u T x) =
      ∫ f : Path, (weight level u T x f).toReal*F (x+f T) ∂pathLaw := by
  have hy : Measurable (fun f : Path ↦ x+f T) :=
    measurable_const.add (continuous_eval T).measurable
  rw [law,integral_map hy.aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_weight level u T x)
      (ae_of_all _ (fun f ↦ (ne_top_of_le_ne_top ENNReal.one_ne_top
        (weight_le_one level u T x f)).lt_top))]
  rfl

theorem weight_taylor_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ) (n : ℕ) (f : Path) :
    |(weight level u T x f).toReal-∑ j ∈ Finset.range (n+1),
        ((-(u : ℝ))^j/(j.factorial : ℝ))*(momentWeight level j T x f).toReal| ≤
      ((u : ℝ)^(n+1)/((n+1).factorial : ℝ))*(momentWeight level (n+1) T x f).toReal := by
  by_cases hf : f ∈ survival (level-x) T
  · have hA := shiftedArea_nonneg_of_survival level x T f hf
    have hm (j : ℕ) : (momentWeight level j T x f).toReal = shiftedArea level x T f^j := by
      rw [momentWeight,indicator_of_mem hf,ENNReal.toReal_pow,ENNReal.toReal_ofReal hA]
    rw [weight,indicator_of_mem hf,ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simp_rw [hm]
    exact area_exponential_taylor_bound n u (shiftedArea level x T f) u.coe_nonneg hA
  · simp only [weight,momentWeight,indicator_of_notMem hf,ENNReal.toReal_zero,
      mul_zero,Finset.sum_const_zero,sub_zero,abs_zero,le_refl]

theorem weight_test_taylor_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ) (n : ℕ)
    (F : ℝ → ℝ) (f : Path) :
    |(weight level u T x f).toReal*F (x+f T)-∑ j ∈ Finset.range (n+1),
        ((-(u : ℝ))^j/(j.factorial : ℝ))*
          ((momentWeight level j T x f).toReal*F (x+f T))| ≤
      ((u : ℝ)^(n+1)/((n+1).factorial : ℝ))*
        ((momentWeight level (n+1) T x f).toReal*|F (x+f T)|) := by
  have h := mul_le_mul_of_nonneg_right (weight_taylor_bound level u T x n f)
    (abs_nonneg (F (x+f T)))
  rw [← abs_mul,sub_mul,Finset.sum_mul] at h
  simpa only [mul_assoc] using h

/-- The literal next surviving area moment controls the all-order error
of the actual killed-area Laplace kernel. No differentiability or moment
recurrence is supplied as a premise. -/
theorem law_integral_taylor_bound (level : ℝ) (u T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) :
    |(∫ y, F y ∂law level u T x)-∑ j ∈ Finset.range (n+1),
        ((-(u : ℝ))^j/(j.factorial : ℝ))*(∫ y, F y ∂momentLaw level j T x)| ≤
      ((u : ℝ)^(n+1)/((n+1).factorial : ℝ))*
        (∫ y, |F y| ∂momentLaw level (n+1) T x) := by
  have hsum : Integrable (fun f : Path ↦ ∑ j ∈ Finset.range (n+1),
      ((-(u : ℝ))^j/(j.factorial : ℝ))*
        ((momentWeight level j T x f).toReal*F (x+f T))) pathLaw := by
    exact integrable_finsetSum _ (fun j _ ↦
      (integrable_moment_path_test level j T x hF hC).const_mul _)
  have he : (∑ j ∈ Finset.range (n+1),
      ((-(u : ℝ))^j/(j.factorial : ℝ))*(∫ y, F y ∂momentLaw level j T x)) =
      ∫ f : Path, (∑ j ∈ Finset.range (n+1),
        ((-(u : ℝ))^j/(j.factorial : ℝ))*
          ((momentWeight level j T x f).toReal*F (x+f T))) ∂pathLaw := by
    rw [integral_finsetSum _ (fun j _ ↦
      (integrable_moment_path_test level j T x hF hC).const_mul _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,momentLaw_integral_eq_path_integral level j T x hF]
  have hi := (integrable_moment_path_test level (n+1) T x hF.abs
    (fun y ↦ by simpa only [abs_abs] using hC y)).const_mul
      ((u : ℝ)^(n+1)/((n+1).factorial : ℝ))
  have hb := norm_integral_le_of_norm_le
    (f := fun f : Path ↦ (weight level u T x f).toReal*F (x+f T)-
      ∑ j ∈ Finset.range (n+1), ((-(u : ℝ))^j/(j.factorial : ℝ))*
        ((momentWeight level j T x f).toReal*F (x+f T)))
    hi (ae_of_all _ (fun f : Path ↦ by
    simpa only [Real.norm_eq_abs] using weight_test_taylor_bound level u T x n F f))
  rw [law_integral_eq_path_integral level u T x hF,he,
    ← integral_sub (integrable_weighted_test level u T x hF hC) hsum]
  rw [Real.norm_eq_abs,integral_const_mul,
    ← momentLaw_integral_eq_path_integral level (n+1) T x hF.abs] at hb
  exact hb

end PerronWright.BrownianKilledAreaLaplaceTaylor
