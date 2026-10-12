import PerronWright.Enumeration.ZeroFieldTreeDeltaContinuation

/-!
# Full Cartesian-Delta continuation of the zero-field tree EGF

The local activity-coordinate singularity is already proved in
`ZeroFieldTreeDeltaContinuation`.  The remaining global chart is obtained
from the unconditional normalized rooted-tree profile.  Its scalar
unrooted-tree functional is the usual dissymmetry combination

`integral T - (1/2) integral (T * K T)`.

The first lemmas below isolate the analytic and differential facts about this
functional.  The intended terminal construction is:

1. apply the functional to the zero-field slice of the global normalized
   Cartesian-Delta rooted profile;
2. differentiate the rooted fixed-point equation and use symmetry of the
   kernel pairing to prove `G'(w) = integral T(w) / w` for `w != 0`;
3. compare this with the already proved genuine rooted/unrooted derivative
   identity on the unit disk, fixing the additive constant at `w = 0`;
4. on the fold chart apply the same differential identity after
   `w = 1-X^2`, and compare with the normalized primitive.  This promotes the
   local cubic expansion from the lens to the whole local fold chart without
   requiring a connectedness lemma for the slit activity domain.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldTreeGlobalContinuation

namespace Match

export PerronWright.ZeroFieldTreeEGFMatching
  (complexTreeEGF complexTreeEGF_coeff zeroFieldTreeFMS zeroFieldTreeSeries
    one_le_zeroFieldTreeFMS_radius zeroFieldTreeSeries_analyticOnNhd_unit
    scalarRootedTreeSeries rooted_equals_X_mul_tree_deriv_on_unit)

end Match

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal tree EGF has zero constant term. -/
@[simp] theorem zeroFieldTreeSeries_zero (M : CompactBJRModel S) :
    Match.zeroFieldTreeSeries M 0 = 0 := by
  have hpos : 0 < (Match.zeroFieldTreeFMS M).radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le
      (Match.one_le_zeroFieldTreeFMS_radius M)
  have hp : HasFPowerSeriesAt
      (Match.zeroFieldTreeSeries M) (Match.zeroFieldTreeFMS M) 0 :=
    (Match.zeroFieldTreeFMS M).hasFPowerSeriesOnBall hpos
      |>.hasFPowerSeriesAt
  have hzero := hp.coeff_zero (fun _ : Fin 0 ↦ (0 : ℂ))
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff] at hzero
  rw [Match.zeroFieldTreeFMS,
    oneDimensionalFormalMultilinearSeries_coeff] at hzero
  simpa [Match.complexTreeEGF_coeff,
    CompactBJRModel.treeEGF] using hzero.symm

/-- The analytic dissymmetry functional evaluated at a type-resolved rooted
tree profile. -/
def treeDissymmetryFunctional (M : CompactBJRModel S)
    (T : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M T -
    (1 / 2 : ℂ) * MPR.scalarIntegralCLM M
      (T * M.kernel.complexActionCLM M.mu T)

/-- Analytic rooted profiles give analytic scalar tree continuations through
the dissymmetry functional. -/
theorem treeDissymmetryFunctional_analyticAt
    (M : CompactBJRModel S) {T : ℂ → C(S, ℂ)} {w : ℂ}
    (hT : AnalyticAt ℂ T w) :
    AnalyticAt ℂ (fun z ↦ treeDissymmetryFunctional M (T z)) w := by
  have hK : AnalyticAt ℂ
      (fun z ↦ M.kernel.complexActionCLM M.mu (T z)) w :=
    ((M.kernel.complexActionCLM M.mu).analyticAt _).comp hT
  have hvertex : AnalyticAt ℂ
      (fun z ↦ MPR.scalarIntegralCLM M (T z)) w :=
    ((MPR.scalarIntegralCLM M).analyticAt _).comp hT
  have hedge : AnalyticAt ℂ
      (fun z ↦ MPR.scalarIntegralCLM M
        (T z * M.kernel.complexActionCLM M.mu (T z))) w :=
    ((MPR.scalarIntegralCLM M).analyticAt _).comp (hT.mul hK)
  have hhalf : AnalyticAt ℂ (fun _ : ℂ ↦ (1 / 2 : ℂ)) w :=
    analyticAt_const
  exact hvertex.sub (hhalf.mul hedge)

theorem treeDissymmetryFunctional_analyticOnNhd
    (M : CompactBJRModel S) {T : ℂ → C(S, ℂ)} {U : Set ℂ}
    (hT : AnalyticOnNhd ℂ T U) :
    AnalyticOnNhd ℂ (fun z ↦ treeDissymmetryFunctional M (T z)) U := by
  intro w hw
  exact treeDissymmetryFunctional_analyticAt M (hT w hw)

/-- After differentiating the dissymmetry functional, symmetry of the kernel
pairing collapses the two edge-rooted terms to one. -/
theorem treeDissymmetryFunctional_hasDerivAt
    (M : CompactBJRModel S) {T : ℂ → C(S, ℂ)} {w : ℂ}
    {V : C(S, ℂ)} (hT : HasDerivAt T V w) :
    HasDerivAt (fun z ↦ treeDissymmetryFunctional M (T z))
      (MPR.scalarIntegralCLM M V -
        MPR.scalarIntegralCLM M
          (T w * M.kernel.complexActionCLM M.mu V)) w := by
  have hK : HasDerivAt
      (fun z ↦ M.kernel.complexActionCLM M.mu (T z))
      (M.kernel.complexActionCLM M.mu V) w :=
    (M.kernel.complexActionCLM M.mu).hasFDerivAt.comp_hasDerivAt w hT
  have hvertex : HasDerivAt
      (fun z ↦ MPR.scalarIntegralCLM M (T z))
      (MPR.scalarIntegralCLM M V) w :=
    (MPR.scalarIntegralCLM M).hasFDerivAt.comp_hasDerivAt w hT
  have hedge : HasDerivAt
      (fun z ↦ MPR.scalarIntegralCLM M
        (T z * M.kernel.complexActionCLM M.mu (T z)))
      (MPR.scalarIntegralCLM M
        (V * M.kernel.complexActionCLM M.mu (T w) +
          T w * M.kernel.complexActionCLM M.mu V)) w :=
    (MPR.scalarIntegralCLM M).hasFDerivAt.comp_hasDerivAt w (hT.mul hK)
  have hraw := hvertex.sub (hedge.const_mul (1 / 2 : ℂ))
  have hsymm :
      MPR.scalarIntegralCLM M
          (V * M.kernel.complexActionCLM M.mu (T w)) =
        MPR.scalarIntegralCLM M
          (T w * M.kernel.complexActionCLM M.mu V) := by
    simp only [MPR.scalarIntegralCLM_apply,
      ContinuousKernel.complexActionCLM_apply, ContinuousMap.mul_apply]
    exact TreeFoldUniformField.complexAction_pairing_symm M V (T w)
  apply hraw.congr_deriv
  rw [map_add, hsymm]
  ring

/-- Along any analytic zero-field rooted fixed-point curve
`T(a) = z(a) exp(-d + K T(a))`, the dissymmetry functional has the scalar
derivative forced by rooting.  This is the common differential identity for
both the global activity chart (`z(a)=a`) and the fold chart
(`z(a)=1-a^2`). -/
theorem treeDissymmetryFunctional_hasDerivAt_of_fixedPoint
    (M : CompactBJRModel S) {z : ℂ → ℂ} {T : ℂ → C(S, ℂ)}
    {a z' : ℂ} {V : C(S, ℂ)}
    (hz : HasDerivAt z z' a) (hT : HasDerivAt T V a)
    (hfix : ∀ᶠ t in nhds a,
      T t = z t • NormedSpace.exp
        (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T t)))
    (hzne : z a ≠ 0) :
    HasDerivAt (fun t ↦ treeDissymmetryFunctional M (T t))
      (z' * MPR.scalarIntegralCLM M (T a) / z a) a := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let E : ℂ → C(S, ℂ) := fun t ↦ NormedSpace.exp (-d + K (T t))
  have hinner : HasDerivAt (fun t : ℂ ↦ -d + K (T t)) (K V) a :=
    (K.hasFDerivAt.comp_hasDerivAt a hT).const_add (-d)
  have hEraw :=
    (hasFDerivAt_exp (𝕂 := ℂ) (x := -d + K (T a))).comp_hasDerivAt
      a hinner
  have hE : HasDerivAt E (E a * K V) a := by
    change HasDerivAt
      (NormedSpace.exp ∘ fun t : ℂ ↦ -d + K (T t))
      (NormedSpace.exp (-d + K (T a)) * K V) a
    have hcoeff :
        ((NormedSpace.exp (-d + K (T a)) •
          (1 : C(S, ℂ) →L[ℂ] C(S, ℂ))) (K V)) =
          NormedSpace.exp (-d + K (T a)) * K V := by
      ext x
      simp only [smul_apply, one_apply_eq_self, smul_eq_mul,
        ContinuousMap.mul_apply]
    exact hEraw.congr_deriv hcoeff
  have hprod := hz.smul hE
  have hfix' : T =ᶠ[nhds a] (fun t ↦ z t • E t) := by
    change ∀ᶠ t in nhds a,
      T t = z t • NormedSpace.exp (-d + K (T t))
    exact hfix
  have hd := hfix'.deriv_eq (𝕜 := ℂ)
  change deriv T a = deriv (z • E) a at hd
  rw [hT.deriv, hprod.deriv] at hd
  have hbase : T a = z a • E a := by
    exact hfix'.self_of_nhds
  have hIV := congrArg (MPR.scalarIntegralCLM M) hd
  simp only [map_add, map_smul, smul_eq_mul] at hIV
  have hIT : MPR.scalarIntegralCLM M (T a) =
      z a * MPR.scalarIntegralCLM M (E a) := by
    rw [hbase, map_smul]
    rfl
  have hITK : MPR.scalarIntegralCLM M
      (T a * M.kernel.complexActionCLM M.mu V) =
        z a * MPR.scalarIntegralCLM M (E a * K V) := by
    have hpoint : T a * M.kernel.complexActionCLM M.mu V =
        z a • (E a * K V) := by
      rw [hbase]
      ext x
      simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        smul_eq_mul, K]
      ring
    rw [hpoint, map_smul]
    rfl
  have hfunctional := treeDissymmetryFunctional_hasDerivAt M hT
  apply hfunctional.congr_deriv
  rw [hIV, hITK, hIT]
  field_simp [hzne]
  ring

theorem treeDissymmetryFunctional_deriv_eq_of_fixedPoint
    (M : CompactBJRModel S) {z : ℂ → ℂ} {T : ℂ → C(S, ℂ)}
    {a : ℂ} (hz : AnalyticAt ℂ z a) (hT : AnalyticAt ℂ T a)
    (hfix : ∀ᶠ t in nhds a,
      T t = z t • NormedSpace.exp
        (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T t)))
    (hzne : z a ≠ 0) :
    deriv (fun t ↦ treeDissymmetryFunctional M (T t)) a =
      deriv z a * MPR.scalarIntegralCLM M (T a) / z a := by
  exact (treeDissymmetryFunctional_hasDerivAt_of_fixedPoint M
    hz.differentiableAt.hasDerivAt hT.differentiableAt.hasDerivAt
    hfix hzne).deriv

/-- The dissymmetry functional evaluated on the canonical zero-field fold
profile.  Unlike the global activity chart, this function is analytic across
the fold point `X = 0`. -/
def zeroFieldFoldDissymmetry (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (X : ℂ) : ℂ :=
  treeDissymmetryFunctional M
    (TreeNormalizedFoldActivity.foldProfile M hM (0, X))

/-- On a genuine disk around the fold point, the fold dissymmetry functional
is an analytic primitive of the previously constructed tree fold
derivative. -/
theorem exists_zeroFieldFoldDissymmetry_derivative
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (zeroFieldFoldDissymmetry M hM)
        (Metric.ball (0 : ℂ) r) ∧
      ∀ X ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (zeroFieldFoldDissymmetry M hM)
          (ZeroFieldTreeLocalSingularity.treeFoldDerivative M hM X) X := by
  let T : ℂ → C(S, ℂ) := fun X ↦
    TreeNormalizedFoldActivity.foldProfile M hM (0, X)
  have hT0 : AnalyticAt ℂ T 0 := by
    exact (TreeNormalizedFoldActivity.foldProfile_analytic M hM).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hline : Tendsto (fun X : ℂ ↦ ((0 : C(S, ℂ)), X))
      (nhds 0) (nhds ((0 : C(S, ℂ)), (0 : ℂ))) :=
    continuousAt_const.prodMk continuousAt_id
  have hres : ∀ᶠ X : ℂ in nhds 0,
      TreeCritical.residual M (((1 - X ^ 2 : ℂ), 0), T X) = 0 := by
    simpa only [T, RadiusResponse.radius_base, one_mul] using
      hline.eventually
        (TreeNormalizedFoldActivity.foldProfile_residual M hM)
  have hgood : ∀ᶠ X : ℂ in nhds 0,
      AnalyticAt ℂ T X ∧
        TreeCritical.residual M (((1 - X ^ 2 : ℂ), 0), T X) = 0 :=
    hT0.eventually_analyticAt.and hres
  obtain ⟨r0, hr0, hball0⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := min r0 1
  have hr : 0 < r := lt_min hr0 zero_lt_one
  have hr0' : r ≤ r0 := min_le_left r0 1
  have hr1 : r ≤ 1 := min_le_right r0 1
  have hTan : AnalyticOnNhd ℂ T (Metric.ball (0 : ℂ) r) := by
    intro X hX
    exact (hball0 (Metric.ball_subset_ball hr0' hX)).1
  have hHan : AnalyticOnNhd ℂ (zeroFieldFoldDissymmetry M hM)
      (Metric.ball (0 : ℂ) r) := by
    change AnalyticOnNhd ℂ
      (fun X : ℂ ↦ treeDissymmetryFunctional M
        (TreeNormalizedFoldActivity.foldProfile M hM (0, X)))
      (Metric.ball (0 : ℂ) r)
    exact treeDissymmetryFunctional_analyticOnNhd M hTan
  refine ⟨r, hr, hHan, ?_⟩
  intro X hX
  have hX0 : X ∈ Metric.ball (0 : ℂ) r0 :=
    Metric.ball_subset_ball hr0' hX
  have hTX : HasDerivAt T (deriv T X) X :=
    (hball0 hX0).1.differentiableAt.hasDerivAt
  have hzne : (1 - X ^ 2 : ℂ) ≠ 0 := by
    intro hzero
    have hpow : X ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
    have hnorm : ‖X‖ ^ 2 = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hnormlt : ‖X‖ < 1 := by
      have : ‖X‖ < r := by
        simpa only [Metric.mem_ball, dist_zero_right] using hX
      exact this.trans_le hr1
    nlinarith [norm_nonneg X]
  have hz : HasDerivAt (fun Y : ℂ ↦ 1 - Y ^ 2) (-2 * X) X := by
    have hraw :=
      (hasDerivAt_const X (1 : ℂ)).sub ((hasDerivAt_id X).pow 2)
    have heq : (fun Y : ℂ ↦ 1 - Y ^ 2) =ᶠ[nhds X]
        ((fun _Y : ℂ ↦ 1) - id ^ 2) :=
      Filter.Eventually.of_forall (fun Y ↦ by simp [pow_two])
    apply (hraw.congr_of_eventuallyEq heq).congr_deriv
    simp [id]
  have hfix : ∀ᶠ Y : ℂ in nhds X,
      T Y = (1 - Y ^ 2) • NormedSpace.exp
        (-TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (T Y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hX] with Y hY
    have hresY := (hball0
      (Metric.ball_subset_ball hr0' hY)).2
    change T Y - (1 - Y ^ 2) • NormedSpace.exp
      ((0 : C(S, ℂ)) - TreeCritical.degree M +
        M.kernel.complexActionCLM M.mu (T Y)) = 0 at hresY
    simpa only [zero_sub] using sub_eq_zero.mp hresY
  have hprimitive :=
    treeDissymmetryFunctional_hasDerivAt_of_fixedPoint
      (M := M) (z := fun Y : ℂ ↦ 1 - Y ^ 2) (T := T)
      hz hTX hfix hzne
  apply hprimitive.congr_deriv
  simp only [ZeroFieldTreeLocalSingularity.treeFoldDerivative,
    ZeroFieldTreeLocalSingularity.foldVertexRootedScalar, T]

/-- The unconditional normalized rooted profile produces a genuine analytic
unrooted dissymmetry chart on a full Cartesian Delta-domain.  Away from the
origin its derivative is exactly the scalar rooted profile divided by the
activity. -/
theorem exists_zeroFieldTree_global_dissymmetry_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (eta r : ℝ) (theta : ℂ → C(S, ℂ)) (G : ℂ → ℂ),
      0 < eta ∧ 0 < r ∧
      AnalyticOnNhd ℂ theta (Transfer.cartesianDelta eta 0) ∧
      AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta 0) ∧
      Set.EqOn theta M.rootedTreeSeries (Metric.ball (0 : ℂ) 1) ∧
      Set.EqOn theta
        (fun w : ℂ ↦
          TreeNormalizedFoldActivity.normalizedFoldProfile M hM (w, 0))
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      (∀ w : ℂ, G w = treeDissymmetryFunctional M (theta w)) ∧
      ∀ w ∈ Transfer.cartesianDelta eta 0, w ≠ 0 →
        deriv G w = MPR.scalarIntegralCLM M (theta w) / w := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, _hActivity,
      hTheta, hData, hThetaFold, hThetaInside⟩ :=
    NormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  let theta : ℂ → C(S, ℂ) := fun w ↦ Theta (w, 0)
  let G : ℂ → ℂ := fun w ↦ treeDissymmetryFunctional M (theta w)
  have htheta : AnalyticOnNhd ℂ theta
      (Transfer.cartesianDelta eta 0) := by
    intro w hw
    have hpair : (w, (0 : C(S, ℂ))) ∈
        Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s :=
      ⟨hw, Metric.mem_ball_self hs⟩
    exact (hTheta (w, (0 : C(S, ℂ))) hpair).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0) := by
    exact treeDissymmetryFunctional_analyticOnNhd M htheta
  have hinside : Set.EqOn theta M.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1) := by
    simpa only [theta] using hThetaInside
  have hfold : Set.EqOn theta
      (fun w : ℂ ↦
        TreeNormalizedFoldActivity.normalizedFoldProfile M hM (w, 0))
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) := by
    intro w hw
    exact hThetaFold ⟨hw, Metric.mem_ball_self hs⟩
  refine ⟨eta, r, theta, G, heta, hr, htheta, hG, hinside, hfold,
    fun _ ↦ rfl, ?_⟩
  intro w hw hwne
  have hDnhds : Transfer.cartesianDelta eta 0 ∈ nhds w :=
    (Transfer.isOpen_cartesianDelta eta 0).mem_nhds hw
  have hfix : ∀ᶠ t : ℂ in nhds w,
      theta t = t • NormedSpace.exp
        (-TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (theta t)) := by
    filter_upwards [hDnhds] with t ht
    have hpair : (t, (0 : C(S, ℂ))) ∈
        Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s :=
      ⟨ht, Metric.mem_ball_self hs⟩
    have hres := (hData (t, (0 : C(S, ℂ))) hpair).2
    rw [TreeNormalizedFoldActivity.activityMap_zeroField] at hres
    change theta t -
      t • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (theta t)) = 0 at hres
    simpa only [zero_sub] using sub_eq_zero.mp hres
  have hformula := treeDissymmetryFunctional_hasDerivAt_of_fixedPoint
    (M := M) (z := id) (T := theta)
    (hasDerivAt_id w) (htheta w hw).differentiableAt.hasDerivAt
    (by simpa only [id_eq] using hfix) hwne
  simpa only [G, id_eq, one_mul] using hformula.deriv

/-- The global dissymmetry chart is the literal unrooted-tree EGF throughout
the open unit disk. -/
theorem global_dissymmetry_eq_zeroFieldTreeSeries_on_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {eta : ℝ} {theta : ℂ → C(S, ℂ)} {G : ℂ → ℂ}
    (heta : 0 < eta)
    (_htheta : AnalyticOnNhd ℂ theta (Transfer.cartesianDelta eta 0))
    (hG : AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta 0))
    (hthetaInside : Set.EqOn theta M.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1))
    (hGdef : ∀ w : ℂ, G w = treeDissymmetryFunctional M (theta w))
    (hGderiv : ∀ w ∈ Transfer.cartesianDelta eta 0, w ≠ 0 →
      deriv G w = MPR.scalarIntegralCLM M (theta w) / w) :
    Set.EqOn G (Match.zeroFieldTreeSeries M)
      (Metric.ball (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball (0 : ℂ) 1
  have hUsub : U ⊆ Transfer.cartesianDelta eta 0 :=
    Transfer.unit_ball_subset_cartesianDelta heta
  have hGunit : AnalyticOnNhd ℂ G U := hG.mono hUsub
  have hTree : AnalyticOnNhd ℂ (Match.zeroFieldTreeSeries M) U :=
    Match.zeroFieldTreeSeries_analyticOnNhd_unit M
  have hderivEq_of_ne {w : ℂ} (hw : w ∈ U) (hwne : w ≠ 0) :
      deriv G w = deriv (Match.zeroFieldTreeSeries M) w := by
    have hroot := Match.rooted_equals_X_mul_tree_deriv_on_unit M hw
    have hscalar : MPR.scalarIntegralCLM M (theta w) =
        Match.scalarRootedTreeSeries M w := by
      rw [hthetaInside hw]
      rfl
    have htreeDeriv : deriv (Match.zeroFieldTreeSeries M) w =
        MPR.scalarIntegralCLM M (theta w) / w := by
      apply (eq_div_iff hwne).2
      rw [hscalar]
      simpa only [mul_comm] using hroot
    rw [hGderiv w (hUsub hw) hwne, htreeDeriv]
  let w₀ : ℂ := (1 / 2 : ℂ)
  have hw₀U : w₀ ∈ U := by
    simp only [U, w₀, Metric.mem_ball, dist_zero_right]
    norm_num
  have hw₀ne : w₀ ≠ 0 := by norm_num [w₀]
  have hevent : ∀ᶠ w : ℂ in nhds w₀,
      deriv G w = deriv (Match.zeroFieldTreeSeries M) w := by
    have hUnhds : U ∈ nhds w₀ := Metric.isOpen_ball.mem_nhds hw₀U
    have hnenhds : ({0}ᶜ : Set ℂ) ∈ nhds w₀ :=
      isOpen_compl_singleton.mem_nhds (by simpa using hw₀ne)
    filter_upwards [hUnhds, hnenhds] with w hwU hwne
    exact hderivEq_of_ne hwU (by simpa using hwne)
  have hderivEq : Set.EqOn (deriv G)
      (deriv (Match.zeroFieldTreeSeries M)) U :=
    hGunit.deriv.eqOn_of_preconnected_of_eventuallyEq hTree.deriv
      (convex_ball (0 : ℂ) 1).isPreconnected hw₀U hevent
  have hzeroU : (0 : ℂ) ∈ U := Metric.mem_ball_self zero_lt_one
  have hrootZero : M.rootedTreeSeries 0 = 0 := by
    have hres := M.rootedTreeSeries_residual_zero_openDisk hM
      (z := (0 : ℂ)) (by norm_num)
    change M.rootedTreeSeries 0 -
      (0 : ℂ) • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (M.rootedTreeSeries 0)) = 0 at hres
    simpa only [zero_smul, sub_zero] using hres
  have hthetaZero : theta 0 = 0 := by
    rw [hthetaInside hzeroU, hrootZero]
  have hGzero : G 0 = Match.zeroFieldTreeSeries M 0 := by
    rw [hGdef, hthetaZero, zeroFieldTreeSeries_zero]
    simp [treeDissymmetryFunctional]
  exact Metric.isOpen_ball.eqOn_of_deriv_eq
    (convex_ball (0 : ℂ) 1).isPreconnected
    hGunit.differentiableOn hTree.differentiableOn hderivEq
    hzeroU hGzero

/-- The genuine zero-field tree EGF has one analytic continuation on a
full Cartesian Delta-domain.  On the entire local fold part of that domain,
the same continuation has the integrated cubic Perron--Wright expansion.

The continuation is not installed as an interface: it is the explicit
dissymmetry functional of the unconditional normalized rooted profile. -/
theorem exists_zeroFieldTree_cartesianDelta_continuation
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (C : ℂ) (R G : ℂ → ℂ) (eta r : ℝ),
      0 < eta ∧ 0 < r ∧
      AnalyticAt ℂ R 0 ∧
      AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta 0) ∧
      Set.EqOn G (Match.zeroFieldTreeSeries M)
        (Metric.ball (0 : ℂ) 1) ∧
      ∀ w ∈ TreeNormalizedFoldActivity.localCartesianDelta 1 0 r,
        G w = C - (1 - w) +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            Transfer.cartesianDeltaSqrt w ^ 3 +
          (1 - w) ^ 2 * R (Transfer.cartesianDeltaSqrt w) := by
  obtain ⟨eta, rDelta, theta, G, heta, hrDelta, htheta, hG,
      hthetaInside, hthetaFold, hGdef, hGderiv⟩ :=
    exists_zeroFieldTree_global_dissymmetry_profile M hM
  have hGinside : Set.EqOn G (Match.zeroFieldTreeSeries M)
      (Metric.ball (0 : ℂ) 1) :=
    global_dissymmetry_eq_zeroFieldTreeSeries_on_unit M hM heta htheta hG
      hthetaInside hGdef hGderiv
  obtain ⟨U, R, rU, hrU, _hU0, hUa, hRa, hUderiv, hUexp⟩ :=
    ZeroFieldTreeIntegratedSingularity.exists_normalized_zeroFieldTree_fold_expansion
      M hM
  obtain ⟨C, epsilon, hepsilon, hphysical⟩ :=
    ZeroFieldTreeEGFMatching.exists_positive_ray_treeSeries_eq_const_add_of_primitive
      M hM U hrU hUderiv
  obtain ⟨rH, hrH, hHa, hHderiv⟩ :=
    exists_zeroFieldFoldDissymmetry_derivative M hM
  let rEq : ℝ := min rH rU
  have hrEq : 0 < rEq := lt_min hrH hrU
  have hrEqH : rEq ≤ rH := min_le_left rH rU
  have hrEqU : rEq ≤ rU := min_le_right rH rU
  have hHaEq : AnalyticOnNhd ℂ (zeroFieldFoldDissymmetry M hM)
      (Metric.ball (0 : ℂ) rEq) :=
    hHa.mono (Metric.ball_subset_ball hrEqH)
  have hCUaEq : AnalyticOnNhd ℂ (fun X : ℂ ↦ C + U X)
      (Metric.ball (0 : ℂ) rEq) := by
    exact analyticOnNhd_const.add
      (hUa.mono (Metric.ball_subset_ball hrEqU))
  have hderivEq : Set.EqOn
      (deriv (zeroFieldFoldDissymmetry M hM))
      (deriv (fun X : ℂ ↦ C + U X))
      (Metric.ball (0 : ℂ) rEq) := by
    intro X hX
    have hH := hHderiv X (Metric.ball_subset_ball hrEqH hX)
    have hCU := (hUderiv X
      (Metric.ball_subset_ball hrEqU hX)).const_add C
    exact hH.deriv.trans hCU.deriv.symm
  let a : ℝ := min rEq (min epsilon (min rDelta 1)) / 2
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have harEq : a < rEq := by
    dsimp only [a]
    have := min_le_left rEq (min epsilon (min rDelta 1))
    nlinarith
  have haepsilon : a < epsilon := by
    dsimp only [a]
    have := (min_le_right rEq (min epsilon (min rDelta 1))).trans
      (min_le_left epsilon (min rDelta 1))
    nlinarith
  have harDelta : a < rDelta := by
    dsimp only [a]
    have := (min_le_right rEq (min epsilon (min rDelta 1))).trans
      ((min_le_right epsilon (min rDelta 1)).trans
        (min_le_left rDelta 1))
    nlinarith
  have haone : a < 1 := by
    dsimp only [a]
    have := (min_le_right rEq (min epsilon (min rDelta 1))).trans
      ((min_le_right epsilon (min rDelta 1)).trans
        (min_le_right rDelta 1))
    nlinarith
  let w0 : ℝ := 1 - a ^ 2
  have hw0pos : 0 < w0 := by
    dsimp only [w0]
    nlinarith [sq_pos_of_pos ha]
  have hw0one : w0 < 1 := by
    dsimp only [w0]
    nlinarith [sq_pos_of_pos ha]
  have hw0ball : (w0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hw0pos]
    exact hw0one
  have hsqrt0 : Transfer.cartesianDeltaSqrt (w0 : ℂ) = (a : ℂ) := by
    rw [Transfer.cartesianDeltaSqrt]
    have hone : (1 : ℂ) - (w0 : ℂ) = ((a ^ 2 : ℝ) : ℂ) := by
      norm_cast
      dsimp only [w0]
      ring
    rw [hone, Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg a)]
    simp only [Complex.ofReal_re, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hw0local : (w0 : ℂ) ∈
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 rDelta := by
    refine ⟨Transfer.unit_ball_subset_cartesianDelta (by norm_num) hw0ball, ?_⟩
    change Transfer.cartesianDeltaSqrt (w0 : ℂ) ∈
      Metric.ball (0 : ℂ) rDelta
    rw [hsqrt0, Metric.mem_ball, dist_zero_right,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact harDelta
  have hseed : zeroFieldFoldDissymmetry M hM (a : ℂ) =
      C + U (a : ℂ) := by
    have htheta0 := hthetaFold hw0local
    change theta (w0 : ℂ) =
      TreeNormalizedFoldActivity.foldProfile M hM
        (0, Transfer.cartesianDeltaSqrt (w0 : ℂ)) at htheta0
    rw [hsqrt0] at htheta0
    calc
      zeroFieldFoldDissymmetry M hM (a : ℂ) =
          treeDissymmetryFunctional M (theta (w0 : ℂ)) := by
        rw [zeroFieldFoldDissymmetry, htheta0]
      _ = G (w0 : ℂ) := (hGdef (w0 : ℂ)).symm
      _ = Match.zeroFieldTreeSeries M (w0 : ℂ) := hGinside hw0ball
      _ = C + U (a : ℂ) := hphysical a ha haepsilon
  have haBall : (a : ℂ) ∈ Metric.ball (0 : ℂ) rEq := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha]
    exact harEq
  have hfoldEq : Set.EqOn (zeroFieldFoldDissymmetry M hM)
      (fun X : ℂ ↦ C + U X) (Metric.ball (0 : ℂ) rEq) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq
      (convex_ball (0 : ℂ) rEq).isPreconnected
      hHaEq.differentiableOn hCUaEq.differentiableOn hderivEq
      haBall hseed
  obtain ⟨rho, hrho, hUexpBall⟩ := Metric.mem_nhds_iff.mp hUexp
  let r : ℝ := min rEq (min rDelta rho)
  have hr : 0 < r := lt_min hrEq
    (lt_min hrDelta hrho)
  have hr_rEq : r ≤ rEq := min_le_left rEq _
  have hr_rDelta : r ≤ rDelta :=
    (min_le_right rEq _).trans (min_le_left rDelta _)
  have hr_rho : r ≤ rho :=
    (min_le_right rEq _).trans
      (min_le_right rDelta rho)
  refine ⟨C, R, G, eta, r, heta, hr, hRa, hG, hGinside, ?_⟩
  intro w hw
  let X : ℂ := Transfer.cartesianDeltaSqrt w
  have hXEq : X ∈ Metric.ball (0 : ℂ) rEq :=
    Metric.ball_subset_ball hr_rEq hw.2
  have hXDelta : X ∈ Metric.ball (0 : ℂ) rDelta :=
    Metric.ball_subset_ball hr_rDelta hw.2
  have hwDelta : w ∈
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 rDelta :=
    ⟨hw.1, hXDelta⟩
  have hGX : G w = zeroFieldFoldDissymmetry M hM X := by
    have hthetaX := hthetaFold hwDelta
    change theta w =
      TreeNormalizedFoldActivity.foldProfile M hM (0, X) at hthetaX
    rw [hGdef, zeroFieldFoldDissymmetry, hthetaX]
  have hUX : U X = -X ^ 2 +
      (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
      X ^ 4 * R X :=
    hUexpBall (Metric.ball_subset_ball hr_rho hw.2)
  have hXsq : X ^ 2 = 1 - w :=
    Transfer.cartesianDeltaSqrt_sq w
  have hXfour : X ^ 4 = (1 - w) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring, hXsq]
  change G w = C - (1 - w) +
    (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
      (1 - w) ^ 2 * R X
  rw [hGX, hfoldEq hXEq]
  change C + U X = C - (1 - w) +
    (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
      (1 - w) ^ 2 * R X
  rw [hUX, hXsq, hXfour]
  ring

end PerronWright.ZeroFieldTreeGlobalContinuation
