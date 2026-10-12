import PerronWright.Probability.BrownianPinnedBridge

/-! # Actual pinned Brownian finite joint laws

Finite characteristic tests and the product decomposition with the
Brownian endpoint are computed from the constructed Brownian path law.
The covariance kernel and every finite law are proved, not stored in
an assumed bridge model. These exact laws are prerequisites for later
area tilting; no excursion positivity conditioning is asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPinnedBridgeFiniteLaw

open BrownianPathLaw BrownianPinnedBridge

variable {ι : Type*} [Fintype ι]

def linearTest (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (f : Path) : ℝ :=
  ∑ i, c i * bridge T (t i) f

def quadraticVariance (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*(min (t i : ℝ) (t j : ℝ) - (t i : ℝ)*(t j : ℝ)/(T : ℝ))

theorem hasGaussianLaw_linearTest (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasGaussianLaw (linearTest T t c) pathLaw := by
  have h := ((bridge_isGaussianProcess T).comp_right t).smul c
  convert! h.hasGaussianLaw_fun_sum (I := Finset.univ) using 1

theorem integral_linearTest (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    (∫ f, linearTest T t c f ∂pathLaw) = 0 := by
  unfold linearTest
  rw [integral_finsetSum _ (fun i _ ↦ (bridge_hasGaussianLaw T (t i)).integrable.const_mul _)]
  simp only [integral_const_mul,integral_bridge,mul_zero,Finset.sum_const_zero]

theorem variance_linearTest (T : ℝ≥0) (hT : 0 < T) (t : ι → ℝ≥0)
    (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    Var[linearTest T t c;pathLaw] = quadraticVariance T t c := by
  have hmem (i : ι) : MemLp (fun f ↦ c i * bridge T (t i) f) 2 pathLaw :=
    (bridge_hasGaussianLaw T (t i)).memLp_two.const_mul _
  unfold linearTest
  rw [variance_fun_sum hmem]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    covariance_bridge T _ _ hT (ht _) (ht _),quadraticVariance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticVariance_nonneg (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    0 ≤ quadraticVariance T t c := by
  rw [← variance_linearTest T hT t ht c]
  exact variance_nonneg _ _

theorem hasLaw_linearTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    HasLaw (linearTest T t c) (gaussianReal 0 (Real.toNNReal (quadraticVariance T t c))) pathLaw := by
  refine ⟨(hasGaussianLaw_linearTest T t c).aemeasurable,?_⟩
  rw [(hasGaussianLaw_linearTest T t c).map_eq_gaussianReal,integral_linearTest,
    variance_linearTest T hT t ht c]

/-- Genuine characteristic integral of an arbitrary finite bridge test. -/
theorem integral_exp_linearTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    (∫ f, Complex.exp ((linearTest T t c f : ℂ)*Complex.I) ∂pathLaw) =
      Complex.exp (-((quadraticVariance T t c : ℝ) : ℂ)/2) := by
  have h := (hasGaussianLaw_linearTest T t c).charFunDual_map_eq_fun (ContinuousLinearMap.id ℝ ℝ)
  rw [charFunDual_apply,integral_map (hasGaussianLaw_linearTest T t c).aemeasurable (by fun_prop)] at h
  simpa only [ContinuousLinearMap.id_apply,integral_linearTest,
    variance_linearTest T hT t ht c,Complex.ofReal_zero,zero_mul,zero_sub,neg_div] using h

def finiteLaw (T : ℝ≥0) (t : ι → ℝ≥0) : Measure (ι → ℝ) :=
  pathLaw.map (fun f i ↦ bridge T (t i) f)

instance (T : ℝ≥0) (t : ι → ℝ≥0) : IsProbabilityMeasure (finiteLaw T t) :=
  Measure.isProbabilityMeasure_map
    (measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)).aemeasurable

omit [Fintype ι] in
theorem hasLaw_finite (T : ℝ≥0) (t : ι → ℝ≥0) :
    HasLaw (fun f i ↦ bridge T (t i) f) (finiteLaw T t) pathLaw :=
  ⟨(measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)).aemeasurable,rfl⟩

omit [Fintype ι] in
theorem finite_bridge_independent_endpoint (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) :
    IndepFun (fun f : Path ↦ fun i ↦ bridge T (t i) f) (fun f : Path ↦ f T) pathLaw := by
  let t' : ι → Iic T := fun i ↦ ⟨t i,ht i⟩
  have hm : Measurable (fun x : Iic T → ℝ ↦ fun i ↦ x (t' i)) :=
    measurable_pi_lambda _ (fun i ↦ measurable_pi_apply (t' i))
  simpa only [Function.comp_def,id_eq,t'] using
    (bridge_process_independent_endpoint T hT).comp hm measurable_id

omit [Fintype ι] in
/-- Exact independent-product decomposition of the actual finite bridge
and actual Brownian endpoint, not a disintegration interface. -/
theorem finite_endpoint_jointLaw_eq_prod (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) :
    pathLaw.map (fun f : Path ↦ ((fun i ↦ bridge T (t i) f),f T)) =
      (finiteLaw T t).prod (gaussianReal 0 T) := by
  rw [(finite_bridge_independent_endpoint T hT t ht).map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)).aemeasurable
    (continuous_eval T).measurable.aemeasurable]
  rw [isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T |>.map_eq]
  rfl

end PerronWright.BrownianPinnedBridgeFiniteLaw

