import PerronWright.Analysis.TreeFoldSquareRoot

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.TreeFoldUniformField

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def scalarIntegralCLM (M : CompactBJRModel S) : C(S, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' (α := S) (E := ℂ) (μ := M.mu) ℂ).comp
    (ContinuousMap.toLp 1 M.mu ℂ)

private theorem scalarIntegralCLM_apply (M : CompactBJRModel S) (f : C(S, ℂ)) :
    scalarIntegralCLM M f = ∫ x, f x ∂M.mu := by
  unfold scalarIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp (p := 1) (μ := M.mu) (𝕜 := ℂ) f

/-- The centered analytic fold curve solves the actual field-dependent tree
equation and uses the critical profile as the zero coordinate in the Perron
direction. This is the two-parameter starting point for the joint `X` chart. -/
theorem centeredFoldCurve_equations (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      TreeCritical.residual M
        (((TreeFold.centeredFoldCurve M hM q).1, q.1),
          (TreeFold.centeredFoldCurve M hM q).2) = 0 ∧
      M.normalizedPerronFunctional hM
        ((TreeFold.centeredFoldCurve M hM q).2 - RadiusResponse.profile M hM q.1) =
        q.2 := by
  let j : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ :=
    fun q ↦ (q.1, TreeFold.criticalCoordinate M hM q.1 + q.2)
  have hj0 : j (0, 0) = (0, 0) := by
    simp only [j, TreeFold.criticalCoordinate_base, zero_add]
  have hja : AnalyticAt ℂ j (0, 0) := by
    have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.1) (0, 0) := analyticAt_fst
    have hsnd : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.2) (0, 0) := analyticAt_snd
    have hcrit : AnalyticAt ℂ
        (fun q : C(S, ℂ) × ℂ ↦ TreeFold.criticalCoordinate M hM q.1) (0, 0) :=
      (TreeFold.criticalCoordinate_analytic M hM).comp_of_eq hfst rfl
    exact hfst.prod (hcrit.add hsnd)
  have hjt : Filter.Tendsto j (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [hj0] using hja.continuousAt.tendsto
  filter_upwards [hjt.eventually (TreeFold.foldCurve_equations M hM)] with q hq
  have hfirst := hq.1
  have hsecond := hq.2
  change TreeCritical.residual M
      (((TreeFold.centeredFoldCurve M hM q).1, q.1),
        (TreeFold.centeredFoldCurve M hM q).2) = 0 at hfirst
  change M.normalizedPerronFunctional hM
      ((TreeFold.centeredFoldCurve M hM q).2 - 1) =
      TreeFold.criticalCoordinate M hM q.1 + q.2 at hsecond
  refine ⟨hfirst, ?_⟩
  calc
    M.normalizedPerronFunctional hM
        ((TreeFold.centeredFoldCurve M hM q).2 - RadiusResponse.profile M hM q.1) =
      M.normalizedPerronFunctional hM
        ((TreeFold.centeredFoldCurve M hM q).2 - 1) -
          M.normalizedPerronFunctional hM (RadiusResponse.profile M hM q.1 - 1) := by
            rw [← map_sub]
            congr 1
            abel
    _ = TreeFold.criticalCoordinate M hM q.1 + q.2 -
          TreeFold.criticalCoordinate M hM q.1 := by
            rw [hsecond]
            rfl
    _ = q.2 := by ring

/-- Complex-bilinear symmetry of the genuine kernel action. This is the
field-dependent left-eigenfunctional identity needed at a critical pair. -/
theorem complexAction_pairing_symm (M : CompactBJRModel S)
    (f h : C(S, ℂ)) :
    (∫ x, f x * M.kernel.complexAction M.mu h x ∂M.mu) =
      ∫ x, h x * M.kernel.complexAction M.mu f x ∂M.mu := by
  calc
    (∫ x, f x * M.kernel.complexAction M.mu h x ∂M.mu) =
        ∫ x, ∫ y, f x * ((M.kernel x y : ℂ) * h y) ∂M.mu ∂M.mu := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [M.kernel.complexAction_apply, integral_const_mul]
    _ = ∫ y, ∫ x, f x * ((M.kernel x y : ℂ) * h y) ∂M.mu ∂M.mu := by
          exact integral_integral_swap_of_hasCompactSupport
            (μ := M.mu) (ν := M.mu)
            (f := fun x y ↦ f x * ((M.kernel x y : ℂ) * h y))
            (by fun_prop) isClosed_closure.isCompact
    _ = ∫ y, h y * M.kernel.complexAction M.mu f y ∂M.mu := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [M.kernel.complexAction_apply, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          change f x * ((M.kernel x y : ℂ) * h y) =
            h y * ((M.kernel y x : ℂ) * f x)
          rw [M.kernel.symmetric x y]
          ring

/-- A right eigenvector of `K M_τ` at eigenvalue one gives a genuine left
annihilator for `I - M_τ K`, with no adjoint postulated. -/
theorem eigen_left_annihilation (M : CompactBJRModel S)
    (τ v h : C(S, ℂ))
    (hv : M.kernel.complexAction M.mu (τ * v) = v) :
    (∫ x, v x * (h x - τ x * M.kernel.complexAction M.mu h x) ∂M.mu) = 0 := by
  have hi₁ : Integrable (fun x ↦ v x * h x) M.mu :=
    (v.continuous.mul h.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hi₂ : Integrable (fun x ↦ v x * (τ x * M.kernel.complexAction M.mu h x))
      M.mu :=
    (v.continuous.mul (τ.continuous.mul
      (M.kernel.complexAction M.mu h).continuous)).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
  calc
    (∫ x, v x * (h x - τ x * M.kernel.complexAction M.mu h x) ∂M.mu) =
        (∫ x, v x * h x ∂M.mu) -
          (∫ x, (τ * v) x * M.kernel.complexAction M.mu h x ∂M.mu) := by
            rw [show (fun x ↦ v x * (h x - τ x * M.kernel.complexAction M.mu h x)) =
                (fun x ↦ v x * h x - v x * (τ x * M.kernel.complexAction M.mu h x))
                from by funext x; ring, integral_sub hi₁ hi₂]
            congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            simp only [ContinuousMap.mul_apply]
            ring
    _ = (∫ x, v x * h x ∂M.mu) -
          (∫ x, h x * M.kernel.complexAction M.mu (τ * v) x ∂M.mu) := by
            rw [complexAction_pairing_symm M (τ * v) h]
    _ = 0 := by
      rw [hv]
      have heq : (∫ x, v x * h x ∂M.mu) = ∫ x, h x * v x ∂M.mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      rw [heq, sub_self]

/-- The analytic critical pair supplies the left null functional of the
linearized tree equation throughout a small field neighborhood. -/
theorem critical_left_annihilation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, ∀ h : C(S, ℂ),
      (∫ x, (CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g)) x *
        (h x - (RadiusResponse.profile M hM g) x *
          M.kernel.complexAction M.mu h x) ∂M.mu) = 0 := by
  have hτt : Filter.Tendsto (RadiusResponse.profile M hM) (𝓝 0) (𝓝 1) := by
    simpa only [RadiusResponse.profile_base] using
      (RadiusResponse.profile_analytic M hM).continuousAt.tendsto
  have heig := hτt.eventually (CriticalPair.eigenpair_equations M hM)
  have hcrit := (Classical.choose_spec (CriticalPair.criticalPair_germ M hM)).2.2.1
  filter_upwards [heig, hcrit] with g he hc h
  have hlam : CriticalPair.eigenvalue M hM (RadiusResponse.profile M hM g) = 1 :=
    hc.2
  have hv : M.kernel.complexAction M.mu
      (RadiusResponse.profile M hM g *
        CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g)) =
      CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g) := by
    rw [he.1, hlam, one_smul]
  exact eigen_left_annihilation M _ _ h hv

/-- The left functional does not annihilate the critical profile. At zero
field this pairing is exactly the normalization `∫u=1`. -/
theorem critical_pairing_ne_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      (∫ x, (CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g)) x *
        (RadiusResponse.profile M hM g) x ∂M.mu) ≠ 0 := by
  let τ : C(S, ℂ) → C(S, ℂ) := RadiusResponse.profile M hM
  let v : C(S, ℂ) → C(S, ℂ) :=
    fun g ↦ CriticalPair.eigenvector M hM (τ g)
  have hτa : AnalyticAt ℂ τ 0 := RadiusResponse.profile_analytic M hM
  have hτ0 : τ 0 = 1 := RadiusResponse.profile_base M hM
  have hva : AnalyticAt ℂ v 0 := by
    exact (CriticalPair.eigenvector_analytic M hM).comp_of_eq hτa hτ0
  have hv0 : v 0 = M.complexPerronFunction hM := by
    rw [show v 0 = CriticalPair.eigenvector M hM (τ 0) from rfl, hτ0,
      CriticalPair.eigenvector_base]
  let A : C(S, ℂ) → ℂ := fun g ↦ scalarIntegralCLM M (v g * τ g)
  have hAa : AnalyticAt ℂ A 0 := by
    exact ((scalarIntegralCLM M).analyticAt _).comp (hva.mul hτa)
  have hA0 : A 0 = 1 := by
    rw [show A 0 = scalarIntegralCLM M (v 0 * τ 0) from rfl,
      hv0, hτ0, mul_one, scalarIntegralCLM_apply]
    have h := FoldCoefficients.weightedIntegralComplex_one M hM
    change (∫ x, (M.perronFunction hM x : ℂ) * (1 : C(S, ℂ)) x ∂M.mu) = 1 at h
    simpa only [ContinuousMap.one_apply, mul_one,
      CompactBJRModel.complexPerronFunction_apply] using h
  have hAnz : ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), A g ≠ 0 := by
    exact hAa.continuousAt.eventually_ne (by rw [hA0]; exact one_ne_zero)
  filter_upwards [hAnz] with g hg
  have hAeq : A g = ∫ x, v g x * τ g x ∂M.mu := by
    rw [show A g = scalarIntegralCLM M (v g * τ g) from rfl,
      scalarIntegralCLM_apply]
    rfl
  exact hAeq ▸ hg

private def treeExponential (M : CompactBJRModel S) (g : C(S, ℂ))
    (U : ℂ → C(S, ℂ)) (s : ℂ) : C(S, ℂ) :=
  NormedSpace.exp (g - TreeCritical.degree M + M.kernel.complexActionCLM M.mu (U s))

private theorem treeExponential_hasDerivAt (M : CompactBJRModel S)
    (g : C(S, ℂ)) (U : ℂ → C(S, ℂ)) (s : ℂ)
    (hU : AnalyticAt ℂ U s) :
    HasDerivAt (treeExponential M g U)
      (treeExponential M g U s * M.kernel.complexActionCLM M.mu (deriv U s)) s := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  have hinner : HasDerivAt (fun t : ℂ ↦ g - d + K (U t))
      (K (deriv U s)) s :=
    ((K.hasFDerivAt.comp_hasDerivAt s hU.hasStrictDerivAt.hasDerivAt).const_add
      (g - d))
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := g - d + K (U s))).comp_hasDerivAt
    s hinner
  change HasDerivAt (NormedSpace.exp ∘ fun t : ℂ ↦ g - d + K (U t))
    (NormedSpace.exp (g - d + K (U s)) * K (deriv U s)) s
  have hcoeff : ((NormedSpace.exp (g - d + K (U s)) •
      (1 : C(S, ℂ) →L[ℂ] C(S, ℂ))) (K (deriv U s))) =
      NormedSpace.exp (g - d + K (U s)) * K (deriv U s) := by
    ext x
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul, ContinuousMap.mul_apply]
  exact hexp.congr_deriv hcoeff

/-- First derivative of an actual local tree-solution curve at a fixed field.
This is derived by differentiating the tree equation, not assumed. -/
theorem tree_curve_first_derivative (M : CompactBJRModel S)
    (g : C(S, ℂ)) (z : ℂ → ℂ) (U : ℂ → C(S, ℂ))
    (hz : AnalyticAt ℂ z 0) (hU : AnalyticAt ℂ U 0)
    (heq : ∀ᶠ s in 𝓝 (0 : ℂ),
      U s = z s • treeExponential M g U s) :
    deriv U 0 = deriv z 0 • treeExponential M g U 0 +
      z 0 • (treeExponential M g U 0 *
        M.kernel.complexActionCLM M.mu (deriv U 0)) := by
  have hprod := hz.hasStrictDerivAt.hasDerivAt.smul
    (treeExponential_hasDerivAt M g U 0 hU)
  have heq' : U =ᶠ[𝓝 (0 : ℂ)] (fun s ↦ z s • treeExponential M g U s) := heq
  have hd := heq'.deriv_eq (𝕜 := ℂ)
  change deriv U 0 = deriv (z • treeExponential M g U) 0 at hd
  rw [hprod.deriv] at hd
  simpa only [add_comm] using hd

/-- Algebraic Fredholm alternative for the derivative of an actual tree
solution curve: the left null functional forces a stationary radius. -/
theorem tree_curve_radius_deriv_zero (M : CompactBJRModel S)
    (g : C(S, ℂ)) (z : ℂ → ℂ) (U : ℂ → C(S, ℂ)) (v : C(S, ℂ))
    (hz : AnalyticAt ℂ z 0) (hU : AnalyticAt ℂ U 0)
    (heq : ∀ᶠ s in 𝓝 (0 : ℂ),
      U s = z s • treeExponential M g U s)
    (hleft : (∫ x, v x *
      ((deriv U 0) x - (U 0) x *
        M.kernel.complexAction M.mu (deriv U 0) x) ∂M.mu) = 0)
    (hpair : (∫ x, v x * (U 0) x ∂M.mu) ≠ 0) :
    deriv z 0 = 0 := by
  let K := M.kernel.complexActionCLM M.mu
  let E := treeExponential M g U
  have hbase : U 0 = z 0 • E 0 := heq.self_of_nhds
  have hd := tree_curve_first_derivative M g z U hz hU heq
  have hpoint (x : S) :
      z 0 * ((deriv U 0) x - (U 0) x * (K (deriv U 0)) x) =
        deriv z 0 * (U 0) x := by
    have hdx := congrArg (fun f : C(S, ℂ) ↦ f x) hd
    have hbx := congrArg (fun f : C(S, ℂ) ↦ f x) hbase
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul] at hdx hbx
    rw [hbx]
    rw [hdx]
    ring
  have hint : z 0 * (∫ x, v x *
      ((deriv U 0) x - (U 0) x * (K (deriv U 0)) x) ∂M.mu) =
      deriv z 0 * (∫ x, v x * (U 0) x ∂M.mu) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    calc
      z 0 * (v x * ((deriv U 0) x - (U 0) x * (K (deriv U 0)) x)) =
          v x * (z 0 * ((deriv U 0) x - (U 0) x * (K (deriv U 0)) x)) := by
            ring
      _ = v x * (deriv z 0 * (U 0) x) := by rw [hpoint]
      _ = deriv z 0 * (v x * (U 0) x) := by ring
  have hleft' : (∫ x, v x *
      ((deriv U 0) x - (U 0) x * (K (deriv U 0)) x) ∂M.mu) = 0 := by
    simpa only [K, ContinuousKernel.complexActionCLM_apply] using hleft
  rw [hleft', mul_zero] at hint
  exact (mul_eq_zero.mp hint.symm).resolve_right hpair

/-- The radius coordinate of the actual centered field-dependent fold curve
is stationary in the Perron direction at every sufficiently small field. -/
theorem centered_radius_deriv_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      deriv (fun t : ℂ ↦ (TreeFold.centeredFoldCurve M hM (g, t)).1) 0 = 0 := by
  let ψ := TreeFold.centeredFoldCurve M hM
  have hemb : Filter.Tendsto (fun g : C(S, ℂ) ↦ (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
      (fun g : C(S, ℂ) ↦ (g, (0 : ℂ))) 0).continuousAt.tendsto
  have hψa := hemb.eventually (TreeFold.centeredFoldCurve_analytic M hM).eventually_analyticAt
  have hψeq := hemb.eventually (centeredFoldCurve_equations M hM).eventually_nhds
  have hcrit := TreeFold.centeredFoldCurve_critical M hM
  have hleft := critical_left_annihilation M hM
  have hpair := critical_pairing_ne_zero M hM
  filter_upwards [hψa, hψeq, hcrit, hleft, hpair] with g hψag hψeqg hcritg hleftg hpairg
  let z : ℂ → ℂ := fun t ↦ (ψ (g, t)).1
  let U : ℂ → C(S, ℂ) := fun t ↦ (ψ (g, t)).2
  have hsection : AnalyticAt ℂ (fun t : ℂ ↦ (g, t)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hψslice : AnalyticAt ℂ (fun t : ℂ ↦ ψ (g, t)) 0 := by
    exact hψag.comp_of_eq hsection rfl
  have hza : AnalyticAt ℂ z 0 := analyticAt_fst.comp hψslice
  have hUa : AnalyticAt ℂ U 0 := analyticAt_snd.comp hψslice
  have hsectiont : Filter.Tendsto (fun t : ℂ ↦ (g, t)) (𝓝 0) (𝓝 (g, 0)) :=
    hsection.continuousAt.tendsto
  have htree : ∀ᶠ t in 𝓝 (0 : ℂ),
      U t = z t • treeExponential M g U t := by
    filter_upwards [hsectiont.eventually hψeqg] with t ht
    exact sub_eq_zero.mp ht.1
  have hU0 : U 0 = RadiusResponse.profile M hM g := by
    exact congrArg Prod.snd hcritg
  have hleft' : (∫ x,
      (CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g)) x *
        ((deriv U 0) x - (U 0) x *
          M.kernel.complexAction M.mu (deriv U 0) x) ∂M.mu) = 0 := by
    rw [hU0]
    exact hleftg (deriv U 0)
  have hpair' : (∫ x,
      (CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g)) x *
        (U 0) x ∂M.mu) ≠ 0 := by
    rw [hU0]
    exact hpairg
  exact tree_curve_radius_deriv_zero M g z U
    (CriticalPair.eigenvector M hM (RadiusResponse.profile M hM g))
    hza hUa htree hleft' hpair'

/-- One-variable analytic division by a quadratic zero, including the exact
leading Taylor coefficient. This lemma is elementary and assumes no fold
interface. -/
theorem scalar_quadratic_factorization (f : ℂ → ℂ)
    (hfa : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      H 0 = deriv (deriv f) 0 / 2 ∧
      ∀ s : ℂ, f s = s ^ 2 * H s := by
  obtain ⟨R, hRa, hR⟩ := hfa.exists_eq_sum_add_pow_mul 3
  let H : ℂ → ℂ := fun s ↦ deriv (deriv f) 0 / 2 + s * R s
  have hHa : AnalyticAt ℂ H 0 :=
    analyticAt_const.add (analyticAt_id.mul hRa)
  have hH0 : H 0 = deriv (deriv f) 0 / 2 := by simp [H]
  refine ⟨H, hHa, hH0, ?_⟩
  intro s
  have hpoly :
      (∑ i ∈ Finset.range 3, (s ^ i / i.factorial) • iteratedDeriv i f 0) =
        deriv (deriv f) 0 / 2 * s ^ 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedDeriv_succ, iteratedDeriv_zero]
    simp only [hf0, hf1]
    norm_num
    ring
  have hs := hR s
  rw [hpoly] at hs
  change f s = _ at hs
  rw [hs]
  simp only [H, smul_eq_mul]
  ring

/-- At each sufficiently small field, the *actual* centered radius has a
quadratic analytic factor in the local scalar coordinate. Joint analyticity
of these chosen factors is a separate, stronger division statement. -/
theorem centered_radius_pointwise_quadratic_factor (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
        H 0 = -(deriv (deriv
          (fun t : ℂ ↦ (TreeFold.centeredFoldCurve M hM (g, t)).1)) 0) / 2 ∧
        ∀ t : ℂ,
          RadiusResponse.radius M hM g -
            (TreeFold.centeredFoldCurve M hM (g, t)).1 = t ^ 2 * H t := by
  have hemb : Filter.Tendsto (fun g : C(S, ℂ) ↦ (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
      (fun g : C(S, ℂ) ↦ (g, (0 : ℂ))) 0).continuousAt.tendsto
  have hψa := hemb.eventually (TreeFold.centeredFoldCurve_analytic M hM).eventually_analyticAt
  have hcrit := TreeFold.centeredFoldCurve_critical M hM
  have hzd := centered_radius_deriv_zero M hM
  filter_upwards [hψa, hcrit, hzd] with g hψag hcritg hzdg
  let z : ℂ → ℂ := fun t ↦ (TreeFold.centeredFoldCurve M hM (g, t)).1
  let f : ℂ → ℂ := fun t ↦ RadiusResponse.radius M hM g - z t
  have hsection : AnalyticAt ℂ (fun t : ℂ ↦ (g, t)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hza : AnalyticAt ℂ z 0 :=
    analyticAt_fst.comp (hψag.comp_of_eq hsection rfl)
  have hfa : AnalyticAt ℂ f 0 := analyticAt_const.sub hza
  have hz0 : z 0 = RadiusResponse.radius M hM g :=
    congrArg Prod.fst hcritg
  have hf0 : f 0 = 0 := by simp [f, hz0]
  have hf1 : deriv f 0 = 0 := by
    rw [show f = (fun t : ℂ ↦ RadiusResponse.radius M hM g - z t) from rfl,
      deriv_const_sub]
    simp only [z, hzdg, neg_zero]
  obtain ⟨H, hHa, hH0, hFactor⟩ := scalar_quadratic_factorization f hfa hf0 hf1
  refine ⟨H, hHa, ?_, ?_⟩
  · rw [hH0]
    change deriv (deriv (fun t : ℂ ↦ RadiusResponse.radius M hM g - z t)) 0 / 2 = _
    rw [deriv_const_sub' (RadiusResponse.radius M hM g)]
    change deriv (-(deriv z)) 0 / 2 = _
    rw [deriv.neg]
  · exact hFactor

end PerronWright.TreeFoldUniformField
