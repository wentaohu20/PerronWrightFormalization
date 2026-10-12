import PerronWright.Probability.BrownianBridgeAreaCrossKernel

/-! # Actual joint Gaussian bridge tests and continuous signed area

Every finite bridge test plus an arbitrary multiple of the literal
continuous area is obtained as a true sample limit of finite Gaussian
tests. The actual cross covariance is then recovered from the proved
variance law. No Cameron--Martin or excursion interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeAreaJointGaussian

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianPinnedBridgeArea BrownianBridgeAreaCrossKernel

variable {ι : Type*} [Fintype ι]

def combinedTest (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (v : ℝ) (f : Path) : ℝ :=
  linearTest T t c f+v*area T f

def combinedVariance (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (v : ℝ) : ℝ :=
  quadraticVariance T t c+2*v*testCrossMean T t c+v^2*((T : ℝ)^3/12)

private def combinedQuadrature (T : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (v : ℝ)
    (m : ℕ) (f : Path) : ℝ := linearTest T t c f+v*quadrature T m f

private theorem combinedQuadrature_hasGaussianLaw (T : ℝ≥0) (t : ι → ℝ≥0)
    (c : ι → ℝ) (v : ℝ) (m : ℕ) : HasGaussianLaw (combinedQuadrature T t c v m) pathLaw := by
  let t' : Sum ι (Fin m) → ℝ≥0 := Sum.elim t (timeGrid T m)
  let c' : Sum ι (Fin m) → ℝ := Sum.elim c (fun _ ↦ v*((T : ℝ)/(m : ℝ)))
  have h := (((bridge_isGaussianProcess T).comp_right t').smul c').hasGaussianLaw_fun_sum
    (I := Finset.univ)
  convert! h using 1
  funext f
  simp only [combinedQuadrature,quadrature,linearTest,Fintype.sum_sum_type,t',c',
    Sum.elim_inl,Sum.elim_inr,Function.comp_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

private theorem integral_combinedQuadrature (T : ℝ≥0) (t : ι → ℝ≥0)
    (c : ι → ℝ) (v : ℝ) (m : ℕ) : (∫ f, combinedQuadrature T t c v m f ∂pathLaw) = 0 := by
  unfold combinedQuadrature
  have hq : Integrable (quadrature T m) pathLaw :=
    (hasGaussianLaw_linearTest T (timeGrid T m) _).integrable
  rw [integral_add (hasGaussianLaw_linearTest T t c).integrable
    (hq.const_mul v),
    integral_const_mul,integral_linearTest]
  simp only [quadrature,integral_linearTest,mul_zero,add_zero]

private theorem variance_combinedQuadrature (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (v : ℝ) (m : ℕ) :
    Var[combinedQuadrature T t c v m;pathLaw] = quadraticVariance T t c+
      2*v*cov[linearTest T t c,quadrature T m;pathLaw]+
      v^2*quadraticVariance T (timeGrid T m) (fun _ ↦ (T : ℝ)/(m : ℝ)) := by
  unfold combinedQuadrature
  have hq : MemLp (quadrature T m) 2 pathLaw :=
    (hasGaussianLaw_linearTest T (timeGrid T m) _).memLp_two
  rw [variance_fun_add (hasGaussianLaw_linearTest T t c).memLp_two
    (hq.const_mul v),
    variance_const_mul,covariance_const_mul_right,variance_linearTest T hT t ht,
    show Var[quadrature T m;pathLaw] = quadraticVariance T (timeGrid T m) _ from
      variance_linearTest T hT (timeGrid T m) (timeGrid_le T m) _]
  ring

private theorem variance_combinedQuadrature_tendsto (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (v : ℝ) :
    Tendsto (fun n : ℕ ↦ Var[combinedQuadrature T t c v (n+1);pathLaw])
      atTop (𝓝 (combinedVariance T t c v)) := by
  simp only [variance_combinedQuadrature T hT t ht]
  exact ((tendsto_const_nhds.add
    ((covariance_linearTest_quadrature_tendsto T hT t ht c).const_mul (2*v))).add
    ((quadrature_variance_tendsto T hT).const_mul (v^2)))

theorem combinedVariance_nonneg (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (v : ℝ) :
    0 ≤ combinedVariance T t c v :=
  ge_of_tendsto (variance_combinedQuadrature_tendsto T hT t ht c v)
    (Eventually.of_forall (fun _ ↦ variance_nonneg _ _))

private theorem integral_exp_combinedQuadrature (T : ℝ≥0) (t : ι → ℝ≥0)
    (c : ι → ℝ) (v : ℝ) (m : ℕ) (s : ℝ) :
    (∫ f, Complex.exp ((s : ℂ)*(combinedQuadrature T t c v m f : ℂ)*Complex.I) ∂pathLaw) =
      Complex.exp (-(Var[combinedQuadrature T t c v m;pathLaw] : ℂ)*(s : ℂ)^2/2) := by
  have hg := combinedQuadrature_hasGaussianLaw T t c v m
  have h : HasLaw (combinedQuadrature T t c v m)
      (gaussianReal 0 (Real.toNNReal Var[combinedQuadrature T t c v m;pathLaw])) pathLaw := by
    refine ⟨hg.aemeasurable,?_⟩
    rw [hg.map_eq_gaussianReal,integral_combinedQuadrature]
  have hc := congrFun (congrArg charFun h.map_eq) s
  rw [charFun_apply_real,integral_map h.aemeasurable (by fun_prop),charFun_gaussianReal] at hc
  simpa only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
    Real.coe_toNNReal _ (variance_nonneg _ _),neg_div,neg_mul] using hc

theorem integral_exp_combinedTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (v s : ℝ) :
    (∫ f, Complex.exp ((s : ℂ)*(combinedTest T t c v f : ℂ)*Complex.I) ∂pathLaw) =
      Complex.exp (-((combinedVariance T t c v : ℝ) : ℂ)*(s : ℂ)^2/2) := by
  have hchar : Continuous (fun x : ℝ ↦ Complex.exp ((s : ℂ)*(x : ℂ)*Complex.I)) := by fun_prop
  have hs (f : Path) : Tendsto (fun n : ℕ ↦ combinedQuadrature T t c v (n+1) f)
      atTop (𝓝 (combinedTest T t c v f)) :=
    tendsto_const_nhds.add ((quadrature_tendsto_area T f).const_mul v)
  have hlim : Tendsto
      (fun n : ℕ ↦ ∫ f, Complex.exp ((s : ℂ)*(combinedQuadrature T t c v (n+1) f : ℂ)*Complex.I) ∂pathLaw)
      atTop (𝓝 (∫ f, Complex.exp ((s : ℂ)*(combinedTest T t c v f : ℂ)*Complex.I) ∂pathLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · intro n
      exact (hchar.measurable.comp_aemeasurable
        (combinedQuadrature_hasGaussianLaw T t c v (n+1)).aemeasurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun f ↦ by simp [Complex.norm_exp])
    · exact Eventually.of_forall (fun f ↦ (hchar.tendsto _).comp (hs f))
  have hformula : Tendsto
      (fun n : ℕ ↦ ∫ f, Complex.exp ((s : ℂ)*(combinedQuadrature T t c v (n+1) f : ℂ)*Complex.I) ∂pathLaw)
      atTop (𝓝 (Complex.exp (-((combinedVariance T t c v : ℝ) : ℂ)*(s : ℂ)^2/2))) := by
    simp only [integral_exp_combinedQuadrature]
    have hc : Continuous (fun x : ℝ ↦ Complex.exp (-(x : ℂ)*(s : ℂ)^2/2)) := by fun_prop
    exact (hc.tendsto _).comp (variance_combinedQuadrature_tendsto T hT t ht c v)
  exact tendsto_nhds_unique hlim hformula

theorem hasLaw_combinedTest (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) (v : ℝ) :
    HasLaw (combinedTest T t c v)
      (gaussianReal 0 (Real.toNNReal (combinedVariance T t c v))) pathLaw := by
  have hm : Measurable (combinedTest T t c v) :=
    (BrownianPinnedBridgeTilt.continuous_linearTest T t c).measurable.add
      ((measurable_area T).const_mul v)
  refine ⟨hm.aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map hm.aemeasurable (by fun_prop),
    integral_exp_combinedTest T hT t ht c v,charFun_gaussianReal]
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,neg_div,neg_mul,
    Real.coe_toNNReal _ (combinedVariance_nonneg T hT t ht c v)]

theorem covariance_linearTest_area (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    cov[linearTest T t c,area T;pathLaw] = testCrossMean T t c := by
  have hv := (hasLaw_combinedTest T hT t ht c 1).variance_eq
  change Var[fun f ↦ linearTest T t c f+1*area T f;pathLaw] = _ at hv
  rw [variance_id_gaussianReal,Real.coe_toNNReal _
    (combinedVariance_nonneg T hT t ht c 1)] at hv
  have he : Var[fun f ↦ linearTest T t c f+area T f;pathLaw] =
      quadraticVariance T t c+2*testCrossMean T t c+(T : ℝ)^3/12 := by
    simpa only [combinedVariance,mul_one,one_mul,one_pow] using hv
  have h := variance_fun_add (hasGaussianLaw_linearTest T t c).memLp_two
    (area_hasGaussianLaw T hT).memLp_two
  rw [variance_linearTest T hT t ht c,variance_area T hT] at h
  linarith

theorem covariance_bridge_area (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    cov[bridge T t,area T;pathLaw] = crossMean T t := by
  have he : linearTest T (fun _ : Unit ↦ t) (fun _ ↦ (1 : ℝ)) = bridge T t := by
    funext f
    simp only [linearTest,Fintype.sum_unique,one_mul]
  have h := covariance_linearTest_area T hT (fun _ : Unit ↦ t) (fun _ ↦ ht) (fun _ ↦ 1)
  rw [he] at h
  simpa only [testCrossMean,Fintype.sum_unique,one_mul] using h

/-- Genuine jointly Gaussian pair for every finite bridge test and the
actual continuous signed area. -/
theorem joint_hasGaussianLaw (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    HasGaussianLaw (fun f : Path ↦ (linearTest T t c f,area T f)) pathLaw := by
  refine ⟨?_⟩
  apply isGaussian_of_isGaussian_map
  intro L
  have hsplit (x y : ℝ) : L (x,y) = L (1,0)*x+L (0,1)*y := by
    have he : (x,y) = x • (1,0)+y • (0,1) := by ext <;> simp
    rw [he,L.map_add,L.map_smul,L.map_smul]
    simp only [smul_eq_mul]
    ring
  have he : (fun f : Path ↦ L (linearTest T t c f,area T f)) =
      combinedTest T t (fun i ↦ L (1,0)*c i) (L (0,1)) := by
    funext f
    rw [hsplit]
    simp only [combinedTest,linearTest,Finset.mul_sum,mul_assoc]
  rw [Measure.map_map L.continuous.measurable
    ((BrownianPinnedBridgeTilt.continuous_linearTest T t c).measurable.prodMk (measurable_area T))]
  change IsGaussian (pathLaw.map (fun f : Path ↦ L (linearTest T t c f,area T f)))
  rw [he]
  exact (hasLaw_combinedTest T hT t ht (fun i ↦ L (1,0)*c i) (L (0,1))).hasGaussianLaw.isGaussian_map

end PerronWright.BrownianBridgeAreaJointGaussian
