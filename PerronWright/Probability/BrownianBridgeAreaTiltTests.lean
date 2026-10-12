import PerronWright.Probability.BrownianBridgeAreaJointGaussian

/-! # Actual area tilt on all finite pinned-bridge tests

Gaussian regression is proved from the actual joint bridge--area law.
It gives the true finite-test law under the exponentially weighted
Brownian path probability, without a Cameron--Martin interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeAreaTiltTests

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianPinnedBridgeArea BrownianPinnedBridgeAreaTilt
open BrownianBridgeAreaCrossKernel BrownianBridgeAreaJointGaussian

variable {ι : Type*} [Fintype ι]

/-- Every finite test of the actual pinned bridge is shifted by its
proved cross covariance with area, while its variance is unchanged. -/
theorem hasLaw_linearTest_areaTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    HasLaw (linearTest T t c)
      (gaussianReal (u*testCrossMean T t c) (Real.toNNReal (quadraticVariance T t c)))
      (tiltedAreaLaw T u) := by
  let X := linearTest T t c
  let A := area T
  let Q := (T : ℝ)^3/12
  let C := testCrossMean T t c
  let d := C/Q
  let R : Path → ℝ := fun f ↦ X f-d*A f
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : d*Q = C := by dsimp [d]; exact div_mul_cancel₀ _ (ne_of_gt hQ)
  have hXA := joint_hasGaussianLaw T hT t ht c
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ-d • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hRA : HasGaussianLaw (fun f : Path ↦ (R f,A f)) pathLaw := by
    convert! hXA.map_fun L using 1
  have hR := hRA.fst
  have hA : HasGaussianLaw A pathLaw := (area_hasGaussianLaw T hT)
  have hX : HasGaussianLaw X pathLaw := hasGaussianLaw_linearTest T t c
  have hcov : cov[R,A;pathLaw] = 0 := by
    dsimp only [R]
    rw [covariance_fun_sub_left hX.memLp_two (hA.memLp_two.const_mul _) hA.memLp_two,
      covariance_const_mul_left,covariance_self hA.aemeasurable,
      covariance_linearTest_area T hT t ht c,variance_area T hT]
    change C-d*Q = 0
    linarith
  have hI : IndepFun R A pathLaw := hRA.indepFun_of_covariance_eq_zero hcov
  have hRmean : (∫ f, R f ∂pathLaw) = 0 := by
    dsimp only [R]
    rw [integral_sub hX.integrable (hA.integrable.const_mul _),integral_const_mul,
      integral_linearTest,integral_area T hT]
    ring
  have hVR : Var[R;pathLaw] = quadraticVariance T t c-2*d*C+d^2*Q := by
    dsimp only [R]
    rw [variance_fun_sub hX.memLp_two (hA.memLp_two.const_mul _),
      variance_const_mul,covariance_const_mul_right,variance_linearTest T hT t ht c,
      covariance_linearTest_area T hT t ht c,variance_area T hT]
    ring
  have hV : quadraticVariance T t c = Var[R;pathLaw]+d^2*Q := by
    rw [hVR,← hC]
    ring
  have hLawR : HasLaw R (gaussianReal 0 (Real.toNNReal Var[R;pathLaw])) pathLaw := by
    refine ⟨hR.aemeasurable,?_⟩
    rw [hR.map_eq_gaussianReal,hRmean]
  have hmX := (BrownianPinnedBridgeTilt.continuous_linearTest T t c).measurable
  let := tiltedAreaLaw_isProbability T hT u
  refine ⟨hmX.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map hmX.aemeasurable (by fun_prop),
    tiltedAreaLaw,integral_tilted,integral_exp_mul_area T hT u]
  have hZ : (T : ℝ)^3*u^2/24 = Q*u^2/2 := by dsimp [Q]; ring
  rw [hZ]
  let Z := Real.exp (Q*u^2/2)
  have he : (fun f : Path ↦
      (Real.exp (u*area T f)/Real.exp (Q*u^2/2)) •
        Complex.exp ((s : ℂ)*(linearTest T t c f : ℂ)*Complex.I)) =
      (fun f ↦ (Z : ℂ)⁻¹ *
        (Complex.exp ((s : ℂ)*(R f : ℂ)*Complex.I)*
          Complex.exp (((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)*(A f : ℂ)))) := by
    funext f
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Z]
    rw [div_eq_mul_inv,
      mul_comm (Complex.exp ((u*area T f : ℝ) : ℂ))
        ((Complex.exp (((Q*u^2 : ℝ) : ℂ)/((2 : ℝ) : ℂ)))⁻¹),mul_assoc]
    congr 1
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    dsimp only [R,X,A]
    push_cast
    ring_nf
  rw [he,integral_const_mul]
  have hp : (∫ f, Complex.exp ((s : ℂ)*(R f : ℂ)*Complex.I)*
      Complex.exp (((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)*(A f : ℂ)) ∂pathLaw) =
      (∫ f, Complex.exp ((s : ℂ)*(R f : ℂ)*Complex.I) ∂pathLaw)*
        (∫ f, Complex.exp (((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)*(A f : ℂ)) ∂pathLaw) := by
    exact hI.integral_fun_comp_mul_comp
      (f := fun x : ℝ ↦ Complex.exp ((s : ℂ)*(x : ℂ)*Complex.I))
      (g := fun x : ℝ ↦ Complex.exp (((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)*(x : ℂ)))
      hR.aemeasurable hA.aemeasurable
      (by fun_prop) (by fun_prop)
  rw [hp]
  have hcR := congrFun (congrArg charFun hLawR.map_eq) s
  rw [charFun_apply_real,integral_map hLawR.aemeasurable (by fun_prop),charFun_gaussianReal] at hcR
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
    Real.coe_toNNReal _ (variance_nonneg _ _)] at hcR
  rw [hcR]
  change (Z : ℂ)⁻¹ * (Complex.exp (-((Var[R;pathLaw] : ℂ)*(s : ℂ)^2/2))*
    complexMGF (area T) pathLaw ((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)) = _
  rw [complexMGF_gaussianReal (hasLaw_area T hT).map_eq,charFun_gaussianReal]
  have hcoe : (Real.toNNReal ((T : ℝ)^3/12) : ℝ) = Q :=
    Real.coe_toNNReal _ (le_of_lt hQ)
  rw [hcoe,Real.coe_toNNReal _ (quadraticVariance_nonneg T hT t ht c)]
  simp only [Complex.ofReal_zero,mul_zero,zero_add,Z,Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  change -((Q*u^2/2 : ℝ) : ℂ)+
    (-((Var[R;pathLaw] : ℂ)*(s : ℂ)^2/2)+(Q : ℂ)*((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)^2/2) =
      (s : ℂ)*((u*C : ℝ) : ℂ)*Complex.I-(quadraticVariance T t c : ℂ)*(s : ℂ)^2/2
  rw [hV,← hC]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

theorem integral_linearTest_areaTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    (∫ f, linearTest T t c f ∂tiltedAreaLaw T u) = u*testCrossMean T t c := by
  rw [(hasLaw_linearTest_areaTilt T hT t ht c u).integral_eq,integral_id_gaussianReal]

theorem variance_linearTest_areaTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (u : ℝ) :
    Var[linearTest T t c;tiltedAreaLaw T u] = quadraticVariance T t c := by
  rw [(hasLaw_linearTest_areaTilt T hT t ht c u).variance_eq,variance_id_gaussianReal,
    Real.coe_toNNReal _ (quadraticVariance_nonneg T hT t ht c)]

end PerronWright.BrownianBridgeAreaTiltTests
