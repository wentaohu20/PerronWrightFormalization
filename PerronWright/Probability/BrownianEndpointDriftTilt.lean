import PerronWright.Probability.BrownianPathLaw
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Genuine endpoint tilting of the constructed Brownian path law

The exponential endpoint density is normalized using the actual Gaussian
marginal. Gaussian regression proves its action on every finite path test.
Projective uniqueness and the proved rational-evaluation Borel embedding
then identify the entire continuous-path law, including times beyond the
horizon. Stopping yields the usual linear drift on the finite horizon.
No positive-excursion, Palm, or Cameron--Martin identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEndpointDriftTilt

open BrownianPathLaw BrownianGaussianSkeleton

theorem integral_exp_mul_endpoint (T : ℝ≥0) (u : ℝ) :
    (∫ f : Path, Real.exp (u*f T) ∂pathLaw) = Real.exp ((T : ℝ)*u^2/2) := by
  have h := mgf_gaussianReal
    (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq u
  simpa only [mgf,zero_mul,zero_add] using h

theorem integrable_exp_mul_endpoint (T : ℝ≥0) (u : ℝ) :
    Integrable (fun f : Path ↦ Real.exp (u*f T)) pathLaw := by
  apply mgf_pos_iff.mp
  change 0 < ∫ f : Path, Real.exp (u*f T) ∂pathLaw
  rw [integral_exp_mul_endpoint]
  exact Real.exp_pos _

def tiltedLaw (T : ℝ≥0) (u : ℝ) : Measure Path :=
  pathLaw.tilted (fun f ↦ u*f T)

instance tiltedLaw_isProbability (T : ℝ≥0) (u : ℝ) : IsProbabilityMeasure (tiltedLaw T u) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_endpoint T u)

def endpointDensity (T : ℝ≥0) (u : ℝ) (f : Path) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (u*f T-(T : ℝ)*u^2/2))

theorem measurable_endpointDensity (T : ℝ≥0) (u : ℝ) :
    Measurable (endpointDensity T u) := by
  unfold endpointDensity
  exact (Real.continuous_exp.comp
    (((continuous_eval T).const_mul u).sub continuous_const)).measurable.ennreal_ofReal

theorem tiltedLaw_eq_withDensity (T : ℝ≥0) (u : ℝ) :
    tiltedLaw T u = pathLaw.withDensity (endpointDensity T u) := by
  unfold tiltedLaw Measure.tilted endpointDensity
  rw [integral_exp_mul_endpoint]
  simp only [Real.exp_sub]

theorem lintegral_endpointDensity (T : ℝ≥0) (u : ℝ) :
    (∫⁻ f, endpointDensity T u f ∂pathLaw) = 1 := by
  have h := measure_univ (μ := tiltedLaw T u)
  rw [tiltedLaw_eq_withDensity,withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ] at h
  exact h

variable {ι : Type*} [Fintype ι]

def linearTest (t : ι → ℝ≥0) (c : ι → ℝ) (f : Path) : ℝ :=
  ∑ i, c i*f (t i)

def quadraticVariance (t : ι → ℝ≥0) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)

def crossMean (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) : ℝ :=
  ∑ i, c i*min (t i : ℝ) (T : ℝ)

theorem continuous_linearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    Continuous (linearTest t c) :=
  continuous_finsetSum _ (fun i _ ↦ (continuous_eval (t i)).const_mul (c i))

theorem hasGaussianLaw_linearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasGaussianLaw (linearTest t c) pathLaw := by
  have h := ((isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess).comp_right t).smul c
  convert! h.hasGaussianLaw_fun_sum (I := Finset.univ) using 1

theorem integral_linearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    (∫ f, linearTest t c f ∂pathLaw) = 0 := by
  unfold linearTest
  rw [integral_finsetSum _ (fun i _ ↦
    (isBrownian_pathLaw.toIsPreBrownianReal.integrable_eval (t i)).const_mul _)]
  simp only [integral_const_mul,isBrownian_pathLaw.toIsPreBrownianReal.integral_eval,
    mul_zero,Finset.sum_const_zero]

theorem variance_linearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    Var[linearTest t c;pathLaw] = quadraticVariance t c := by
  have hmem (i : ι) : MemLp (fun f : Path ↦ c i*f (t i)) 2 pathLaw :=
    (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two.const_mul _
  unfold linearTest
  rw [variance_fun_sum hmem]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    isBrownian_pathLaw.toIsPreBrownianReal.covariance_eval,NNReal.coe_min,quadraticVariance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticVariance_nonneg (t : ι → ℝ≥0) (c : ι → ℝ) :
    0 ≤ quadraticVariance t c := by
  rw [← variance_linearTest]
  exact variance_nonneg _ _

theorem hasLaw_linearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasLaw (linearTest t c) (gaussianReal 0 (Real.toNNReal (quadraticVariance t c))) pathLaw := by
  refine ⟨(hasGaussianLaw_linearTest t c).aemeasurable,?_⟩
  rw [(hasGaussianLaw_linearTest t c).map_eq_gaussianReal,integral_linearTest,
    variance_linearTest]

theorem covariance_linearTest_endpoint (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    cov[linearTest t c,fun f : Path ↦ f T;pathLaw] = crossMean T t c := by
  have hmem (i : ι) : MemLp (fun f : Path ↦ c i*f (t i)) 2 pathLaw :=
    (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two.const_mul _
  have hT := (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval T).memLp_two
  unfold linearTest
  rw [covariance_fun_sum_left hmem hT]
  simp only [covariance_const_mul_left,isBrownian_pathLaw.toIsPreBrownianReal.covariance_eval,
    NNReal.coe_min,crossMean]

theorem joint_hasGaussianLaw (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasGaussianLaw (fun f : Path ↦ (linearTest t c f,f T)) pathLaw := by
  let I : Finset ℝ≥0 := Finset.univ.image t ∪ {T}
  let L : (I → ℝ) →L[ℝ] (ℝ × ℝ) :=
    { toFun x := (∑ i, c i*x ⟨t i,by simp [I]⟩,x ⟨T,by simp [I]⟩)
      map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
      map_smul' a x := by
        ext
        · simp only [Pi.smul_apply,smul_eq_mul,Prod.smul_fst,Finset.mul_sum,RingHom.id_apply]
          apply Finset.sum_congr rfl
          intro i _
          ring
        · simp }
  convert! (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw I).map_fun L using 1

theorem variance_endpoint (T : ℝ≥0) :
    Var[fun f : Path ↦ f T;pathLaw] = (T : ℝ) := by
  rw [(isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).variance_eq,
    variance_id_gaussianReal]

/-- Every finite test of the actual Brownian path is shifted by its
proved cross covariance with the endpoint, while its variance is unchanged. -/
theorem hasLaw_linearTest_endpointTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (c : ι → ℝ) (u : ℝ) :
    HasLaw (linearTest t c)
      (gaussianReal (u*crossMean T t c) (Real.toNNReal (quadraticVariance t c)))
      (tiltedLaw T u) := by
  let X := linearTest t c
  let A : Path → ℝ := fun f ↦ f T
  let Q := (T : ℝ)
  let C := crossMean T t c
  let d := C/Q
  let R : Path → ℝ := fun f ↦ X f-d*A f
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : d*Q = C := by dsimp [d]; exact div_mul_cancel₀ _ (ne_of_gt hQ)
  have hXA := joint_hasGaussianLaw T t c
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ-d • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hRA : HasGaussianLaw (fun f : Path ↦ (R f,A f)) pathLaw := by
    convert! hXA.map_fun L using 1
  have hR := hRA.fst
  have hA : HasGaussianLaw A pathLaw := (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval T)
  have hX : HasGaussianLaw X pathLaw := hasGaussianLaw_linearTest t c
  have hcov : cov[R,A;pathLaw] = 0 := by
    dsimp only [R]
    rw [covariance_fun_sub_left hX.memLp_two (hA.memLp_two.const_mul _) hA.memLp_two,
      covariance_const_mul_left,covariance_self hA.aemeasurable,
      covariance_linearTest_endpoint T t c,variance_endpoint T]
    change C-d*Q = 0
    linarith
  have hI : IndepFun R A pathLaw := hRA.indepFun_of_covariance_eq_zero hcov
  have hRmean : (∫ f, R f ∂pathLaw) = 0 := by
    dsimp only [R]
    rw [integral_sub hX.integrable (hA.integrable.const_mul _),integral_const_mul,
      integral_linearTest,isBrownian_pathLaw.toIsPreBrownianReal.integral_eval T]
    ring
  have hVR : Var[R;pathLaw] = quadraticVariance t c-2*d*C+d^2*Q := by
    dsimp only [R]
    rw [variance_fun_sub hX.memLp_two (hA.memLp_two.const_mul _),
      variance_const_mul,covariance_const_mul_right,variance_linearTest t c,
      covariance_linearTest_endpoint T t c,variance_endpoint T]
    ring
  have hV : quadraticVariance t c = Var[R;pathLaw]+d^2*Q := by
    rw [hVR,← hC]
    ring
  have hLawR : HasLaw R (gaussianReal 0 (Real.toNNReal Var[R;pathLaw])) pathLaw := by
    refine ⟨hR.aemeasurable,?_⟩
    rw [hR.map_eq_gaussianReal,hRmean]
  have hmX := (continuous_linearTest t c).measurable
  refine ⟨hmX.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map hmX.aemeasurable (by fun_prop),
    tiltedLaw,integral_tilted,integral_exp_mul_endpoint T u]
  let Z := Real.exp (Q*u^2/2)
  have he : (fun f : Path ↦
      (Real.exp (u*f T)/Real.exp (Q*u^2/2)) •
        Complex.exp ((s : ℂ)*(linearTest t c f : ℂ)*Complex.I)) =
      (fun f ↦ (Z : ℂ)⁻¹ *
        (Complex.exp ((s : ℂ)*(R f : ℂ)*Complex.I)*
          Complex.exp (((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)*(A f : ℂ)))) := by
    funext f
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Z]
    rw [div_eq_mul_inv,
      mul_comm (Complex.exp ((u*f T : ℝ) : ℂ))
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
    complexMGF (fun f : Path ↦ f T) pathLaw ((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)) = _
  rw [complexMGF_gaussianReal (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq,charFun_gaussianReal]
  rw [Real.coe_toNNReal _ (quadraticVariance_nonneg t c)]
  simp only [Complex.ofReal_zero,mul_zero,zero_add,Z,Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  change -((Q*u^2/2 : ℝ) : ℂ)+
    (-((Var[R;pathLaw] : ℂ)*(s : ℂ)^2/2)+(Q : ℂ)*((u : ℂ)+(s : ℂ)*(d : ℂ)*Complex.I)^2/2) =
      (s : ℂ)*((u*C : ℝ) : ℂ)*Complex.I-(quadraticVariance t c : ℂ)*(s : ℂ)^2/2
  rw [hV,← hC]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

theorem integral_linearTest_endpointTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (c : ι → ℝ) (u : ℝ) :
    (∫ f, linearTest t c f ∂tiltedLaw T u) = u*crossMean T t c := by
  rw [(hasLaw_linearTest_endpointTilt T hT t c u).integral_eq,integral_id_gaussianReal]

theorem variance_linearTest_endpointTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (c : ι → ℝ) (u : ℝ) :
    Var[linearTest t c;tiltedLaw T u] = quadraticVariance t c := by
  rw [(hasLaw_linearTest_endpointTilt T hT t c u).variance_eq,variance_id_gaussianReal,
    Real.coe_toNNReal _ (quadraticVariance_nonneg t c)]


theorem finite_law_endpointTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (u : ℝ) :
    (tiltedLaw T u).map (fun f : Path ↦ fun i ↦ f (t i)) =
      pathLaw.map (fun f : Path ↦ fun i ↦ f (t i)+u*min (t i : ℝ) (T : ℝ)) := by
  have hm : Measurable (fun f : Path ↦ fun i ↦ f (t i)) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (t i)).measurable)
  have hm' : Measurable (fun f : Path ↦ fun i ↦ f (t i)+u*min (t i : ℝ) (T : ℝ)) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (t i)).measurable.add_const _)
  apply Measure.ext_of_charFunDual
  funext L
  let c : ι → ℝ := fun i ↦ L (fun j ↦ if i = j then 1 else 0)
  have hsplit (x : ι → ℝ) : L x = ∑ i, c i*x i := by
    change L.toLinearMap x = _
    rw [LinearMap.pi_apply_eq_sum_univ L.toLinearMap x]
    apply Finset.sum_congr rfl
    intro i _
    change x i*L (fun j ↦ if i = j then 1 else 0) = L (fun j ↦ if i = j then 1 else 0)*x i
    exact mul_comm _ _
  have hleft : HasLaw (fun f : Path ↦ L (fun i ↦ f (t i)))
      (gaussianReal (u*crossMean T t c) (Real.toNNReal (quadraticVariance t c)))
      (tiltedLaw T u) := by
    have he : (fun f : Path ↦ L (fun i ↦ f (t i))) = linearTest t c := by
      funext f
      exact hsplit _
    rw [he]
    exact hasLaw_linearTest_endpointTilt T hT t c u
  have hright : HasLaw (fun f : Path ↦ L (fun i ↦ f (t i)+u*min (t i : ℝ) (T : ℝ)))
      (gaussianReal (u*crossMean T t c) (Real.toNNReal (quadraticVariance t c)))
      pathLaw := by
    have he : (fun f : Path ↦ L (fun i ↦ f (t i)+u*min (t i : ℝ) (T : ℝ))) =
        (fun f ↦ linearTest t c f+u*crossMean T t c) := by
      funext f
      rw [hsplit]
      simp only [linearTest,crossMean,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    simpa only [zero_add] using gaussianReal_add_const (hasLaw_linearTest t c) (u*crossMean T t c)
  rw [charFunDual_apply,charFunDual_apply,integral_map hm.aemeasurable (by fun_prop),
    integral_map hm'.aemeasurable (by fun_prop)]
  simpa only [Function.comp_def] using
    (hleft.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).trans
      (hright.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).symm

omit [Fintype ι] in
/-- Every indexed law, including times after the weighted endpoint, is
identified from its actual finite laws by projective uniqueness. -/
theorem indexed_law_endpointTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (u : ℝ) :
    (tiltedLaw T u).map (fun f : Path ↦ fun i ↦ f (t i)) =
      pathLaw.map (fun f : Path ↦ fun i ↦ f (t i)+u*min (t i : ℝ) (T : ℝ)) := by
  let X : ι → Path → ℝ := fun i f ↦ f (t i)
  let Y : ι → Path → ℝ := fun i f ↦ f (t i)+u*min (t i : ℝ) (T : ℝ)
  have hm : Measurable (fun f : Path ↦ fun i ↦ X i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (t i)).measurable)
  have hm' : Measurable (fun f : Path ↦ fun i ↦ Y i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_eval (t i)).measurable.add_const _)
  have hx := isProjectiveLimit_map (X := X) (P := tiltedLaw T u) hm.aemeasurable
  have hy := isProjectiveLimit_map (X := Y) (P := pathLaw) hm'.aemeasurable
  have he (I : Finset ι) :
      (tiltedLaw T u).map (fun f ↦ I.restrict (X · f)) =
        pathLaw.map (fun f ↦ I.restrict (Y · f)) :=
    finite_law_endpointTilt T hT (fun i : I ↦ t i) u
  simp only [he] at hx
  exact hx.unique hy

def driftPath (T : ℝ≥0) (u : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ f t+u*(min t T : ℝ≥0),
    (continuous_path f).add
      ((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul u)⟩

def stoppedPath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ f (min t T),(continuous_path f).comp (continuous_id.min continuous_const)⟩

def stoppedDriftPath (T : ℝ≥0) (u : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ f (min t T)+u*(min t T : ℝ≥0),
    (continuous_path (stoppedPath T f)).add
      ((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul u)⟩

theorem continuous_driftPath (T : ℝ≥0) (u : ℝ) : Continuous (driftPath T u) := by
  let g : C(ℝ≥0,ℝ) := ⟨fun t ↦ u*(min t T : ℝ≥0),
    ((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul u)⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ f+g)
  exact continuous_id.add continuous_const

theorem continuous_stoppedPath (T : ℝ≥0) : Continuous (stoppedPath T) := by
  let p : C(ℝ≥0,ℝ≥0) := ⟨fun t ↦ min t T,continuous_id.min continuous_const⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ f.comp p)
  exact ContinuousMap.continuous_precomp p

theorem continuous_stoppedDriftPath (T : ℝ≥0) (u : ℝ) :
    Continuous (stoppedDriftPath T u) := by
  let p : C(ℝ≥0,ℝ≥0) := ⟨fun t ↦ min t T,continuous_id.min continuous_const⟩
  let g : C(ℝ≥0,ℝ) := ⟨fun t ↦ u*(min t T : ℝ≥0),
    ((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul u)⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ f.comp p+g)
  exact (ContinuousMap.continuous_precomp p).add continuous_const

@[simp] theorem driftPath_eval (T t : ℝ≥0) (u : ℝ) (f : Path) :
    driftPath T u f t = f t+u*min (t : ℝ) (T : ℝ) := by
  change f t+u*(min t T : ℝ≥0) = _
  rw [NNReal.coe_min]

@[simp] theorem stoppedPath_eval (T t : ℝ≥0) (f : Path) :
    stoppedPath T f t = f (min t T) := rfl

@[simp] theorem stoppedDriftPath_eval (T t : ℝ≥0) (u : ℝ) (f : Path) :
    stoppedDriftPath T u f t = f (min t T)+u*min (t : ℝ) (T : ℝ) := by
  change f (min t T)+u*(min t T : ℝ≥0) = _
  rw [NNReal.coe_min]

theorem measurable_driftPath (T : ℝ≥0) (u : ℝ) : Measurable (driftPath T u) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦
    f (rationalTimeReal q)+u*(min (rationalTimeReal q) T : ℝ≥0))
  exact measurable_pi_lambda _ (fun q ↦ (continuous_eval (rationalTimeReal q)).measurable.add_const _)

theorem measurable_stoppedPath (T : ℝ≥0) : Measurable (stoppedPath T) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ f (min (rationalTimeReal q) T))
  exact measurable_pi_lambda _ (fun q ↦ (continuous_eval (min (rationalTimeReal q) T)).measurable)

theorem measurable_stoppedDriftPath (T : ℝ≥0) (u : ℝ) :
    Measurable (stoppedDriftPath T u) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦
    f (min (rationalTimeReal q) T)+u*(min (rationalTimeReal q) T : ℝ≥0))
  exact measurable_pi_lambda _ (fun q ↦
    (continuous_eval (min (rationalTimeReal q) T)).measurable.add_const _)

theorem stopped_driftPath (T : ℝ≥0) (u : ℝ) (f : Path) :
    stoppedPath T (driftPath T u f) = stoppedDriftPath T u f := by
  apply ContinuousMap.ext
  intro t
  change f (min t T)+u*(min (min t T) T : ℝ≥0) =
    f (min t T)+u*(min t T : ℝ≥0)
  rw [min_assoc,min_self]

/-- The actual endpoint-weighted compact-open path probability law is
exactly the law of Brownian motion plus the literal truncated linear drift. -/
theorem pathLaw_endpointTilt_eq_drift (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    tiltedLaw T u = pathLaw.map (driftPath T u) := by
  apply rationalEval_measurableEmbedding.map_injective
  rw [Measure.map_map continuous_rationalEval.measurable (measurable_driftPath T u)]
  exact indexed_law_endpointTilt T hT rationalTimeReal u

theorem weighted_pathLaw_eq_drift (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    pathLaw.withDensity (endpointDensity T u) = pathLaw.map (driftPath T u) := by
  rw [← tiltedLaw_eq_withDensity]
  exact pathLaw_endpointTilt_eq_drift T hT u

theorem stopped_pathLaw_endpointTilt_eq_drift (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (tiltedLaw T u).map (stoppedPath T) = pathLaw.map (stoppedDriftPath T u) := by
  rw [pathLaw_endpointTilt_eq_drift T hT u,
    Measure.map_map (measurable_stoppedPath T) (measurable_driftPath T u)]
  congr 1
  exact funext (stopped_driftPath T u)

theorem weighted_stopped_pathLaw_eq_drift (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (pathLaw.withDensity (endpointDensity T u)).map (stoppedPath T) =
      pathLaw.map (stoppedDriftPath T u) := by
  rw [← tiltedLaw_eq_withDensity]
  exact stopped_pathLaw_endpointTilt_eq_drift T hT u

theorem driftPath_eval_of_le (T t : ℝ≥0) (ht : t ≤ T) (u : ℝ) (f : Path) :
    driftPath T u f t = f t+u*(t : ℝ) := by
  rw [driftPath_eval,min_eq_left (show (t : ℝ) ≤ T from ht)]

theorem stoppedDriftPath_eval_of_le (T t : ℝ≥0) (ht : t ≤ T) (u : ℝ) (f : Path) :
    stoppedDriftPath T u f t = f t+u*(t : ℝ) := by
  rw [stoppedDriftPath_eval,min_eq_left ht,min_eq_left (show (t : ℝ) ≤ T from ht)]

/-- The nonnegative measurable-test identity requires no finite-moment
or integrability assumption. It is the literal endpoint Radon--Nikodym formula. -/
theorem lintegral_driftPath_eq_endpointWeight (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    {Φ : Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (driftPath T u f) ∂pathLaw) =
      ∫⁻ f, endpointDensity T u f*Φ f ∂pathLaw := by
  calc
    _ = ∫⁻ f, Φ f ∂pathLaw.map (driftPath T u) :=
      (lintegral_map hΦ (measurable_driftPath T u)).symm
    _ = ∫⁻ f, Φ f ∂pathLaw.withDensity (endpointDensity T u) := by
      rw [weighted_pathLaw_eq_drift T hT u]
    _ = _ := lintegral_withDensity_eq_lintegral_mul pathLaw
      (measurable_endpointDensity T u) hΦ

theorem lintegral_stoppedDriftPath_eq_endpointWeight (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    {Φ : Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (stoppedDriftPath T u f) ∂pathLaw) =
      ∫⁻ f, endpointDensity T u f*Φ (stoppedPath T f) ∂pathLaw := by
  have h := lintegral_driftPath_eq_endpointWeight T hT u
    (hΦ.comp (measurable_stoppedPath T))
  simpa only [Function.comp_def,stopped_driftPath] using h

theorem integral_driftPath_eq_endpointWeight (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    {Φ : Path → ℝ} (hΦ : Measurable Φ) :
    (∫ f, Φ (driftPath T u f) ∂pathLaw) =
      ∫ f, Real.exp (u*f T-(T : ℝ)*u^2/2)*Φ f ∂pathLaw := by
  calc
    _ = ∫ f, Φ f ∂pathLaw.map (driftPath T u) :=
      (integral_map (measurable_driftPath T u).aemeasurable hΦ.aestronglyMeasurable).symm
    _ = ∫ f, Φ f ∂tiltedLaw T u := by rw [pathLaw_endpointTilt_eq_drift T hT u]
    _ = _ := by
      rw [tiltedLaw,integral_tilted,integral_exp_mul_endpoint]
      simp only [smul_eq_mul,Real.exp_sub]

end PerronWright.BrownianEndpointDriftTilt
