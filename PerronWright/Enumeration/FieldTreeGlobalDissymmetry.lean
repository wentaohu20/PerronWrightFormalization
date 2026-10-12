import PerronWright.Enumeration.ScalarFieldRootedTreeRadius
import PerronWright.Enumeration.ZeroFieldTreeGlobalContinuation

/-!
# Joint-field tree dissymmetry on a normalized Cartesian Delta-domain

The rooted-tree construction already gives one jointly analytic profile
`Theta(w,g)` on a full normalized Cartesian Delta product.  This file applies
the actual tree dissymmetry functional to that profile.  The resulting scalar
map is jointly analytic, agrees at zero field with the literal unrooted-tree
EGF, and satisfies the field-dependent rooting identity

`d/dw G(w,g) = integral Theta(w,g) / w`.

The derivative identity is derived from the genuine residual equation.  In
particular, no global continuation, coefficient bound, or remainder estimate
is installed as an interface.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FieldTreeGlobalDissymmetry

namespace GC

export PerronWright.ZeroFieldTreeGlobalContinuation
  (treeDissymmetryFunctional treeDissymmetryFunctional_hasDerivAt
    global_dissymmetry_eq_zeroFieldTreeSeries_on_unit)

end GC

namespace Match

export PerronWright.ZeroFieldTreeEGFMatching
  (zeroFieldTreeSeries)

end Match

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Analyticity of the dissymmetry functional after an analytic map from an
arbitrary complex Banach space. -/
theorem treeDissymmetryFunctional_analyticAt_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (M : CompactBJRModel S) {T : E → C(S, ℂ)} {q : E}
    (hT : AnalyticAt ℂ T q) :
    AnalyticAt ℂ (fun x ↦ GC.treeDissymmetryFunctional M (T x)) q := by
  have hK : AnalyticAt ℂ
      (fun x ↦ M.kernel.complexActionCLM M.mu (T x)) q :=
    ((M.kernel.complexActionCLM M.mu).analyticAt _).comp hT
  have hvertex : AnalyticAt ℂ
      (fun x ↦ MPR.scalarIntegralCLM M (T x)) q :=
    ((MPR.scalarIntegralCLM M).analyticAt _).comp hT
  have hedge : AnalyticAt ℂ
      (fun x ↦ MPR.scalarIntegralCLM M
        (T x * M.kernel.complexActionCLM M.mu (T x))) q :=
    ((MPR.scalarIntegralCLM M).analyticAt _).comp (hT.mul hK)
  exact hvertex.sub (analyticAt_const.mul hedge)

/-- The usual rooting derivative remains valid with an arbitrary fixed
complex field.  The field is constant along the activity slice, so it
contributes no derivative term. -/
theorem treeDissymmetryFunctional_hasDerivAt_of_fieldFixedPoint
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {z : ℂ → ℂ} {T : ℂ → C(S, ℂ)} {a z' : ℂ}
    {V : C(S, ℂ)}
    (hz : HasDerivAt z z' a) (hT : HasDerivAt T V a)
    (hfix : ∀ᶠ t in nhds a,
      T t = z t • NormedSpace.exp
        (g - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (T t)))
    (hzne : z a ≠ 0) :
    HasDerivAt (fun t ↦ GC.treeDissymmetryFunctional M (T t))
      (z' * MPR.scalarIntegralCLM M (T a) / z a) a := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let E : ℂ → C(S, ℂ) := fun t ↦
    NormedSpace.exp (g - d + K (T t))
  have hinner : HasDerivAt (fun t : ℂ ↦ g - d + K (T t)) (K V) a :=
    (K.hasFDerivAt.comp_hasDerivAt a hT).const_add (g - d)
  have hEraw :=
    (hasFDerivAt_exp (𝕂 := ℂ) (x := g - d + K (T a))).comp_hasDerivAt
      a hinner
  have hE : HasDerivAt E (E a * K V) a := by
    change HasDerivAt
      (NormedSpace.exp ∘ fun t : ℂ ↦ g - d + K (T t))
      (NormedSpace.exp (g - d + K (T a)) * K V) a
    have hcoeff :
        ((NormedSpace.exp (g - d + K (T a)) •
          (1 : C(S, ℂ) →L[ℂ] C(S, ℂ))) (K V)) =
          NormedSpace.exp (g - d + K (T a)) * K V := by
      ext x
      simp only [smul_apply, one_apply_eq_self, smul_eq_mul,
        ContinuousMap.mul_apply]
    exact hEraw.congr_deriv hcoeff
  have hprod := hz.smul hE
  have hfix' : T =ᶠ[nhds a] (fun t ↦ z t • E t) := by
    change ∀ᶠ t in nhds a,
      T t = z t • NormedSpace.exp (g - d + K (T t))
    exact hfix
  have hd := hfix'.deriv_eq (𝕜 := ℂ)
  change deriv T a = deriv (z • E) a at hd
  rw [hT.deriv, hprod.deriv] at hd
  have hbase : T a = z a • E a := hfix'.self_of_nhds
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
  have hfunctional := GC.treeDissymmetryFunctional_hasDerivAt M hT
  apply hfunctional.congr_deriv
  rw [hIV, hITK, hIT]
  field_simp [hzne]
  ring

/-- The jointly analytic normalized tree profile induces a jointly analytic
unrooted-tree continuation on the same Cartesian Delta product.  Its
zero-field slice is the literal tree EGF, and on the local fold product it is
the dissymmetry functional of the actual joint fold chart. -/
theorem exists_normalizedFieldTree_global_dissymmetry_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (eta r s : ℝ)
      (Theta : ℂ × C(S, ℂ) → C(S, ℂ))
      (G : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ Theta
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        RadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M
            (TreeNormalizedFoldActivity.activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta
        (TreeNormalizedFoldActivity.normalizedFoldProfile M hM)
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = GC.treeDissymmetryFunctional M (Theta q)) ∧
      Set.EqOn G
        (fun q ↦ GC.treeDissymmetryFunctional M
          (TreeNormalizedFoldActivity.normalizedFoldProfile M hM q))
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      Set.EqOn (fun w : ℂ ↦ G (w, 0))
        (Match.zeroFieldTreeSeries M) (Metric.ball (0 : ℂ) 1) ∧
      ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        q.1 ≠ 0 →
          deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
            MPR.scalarIntegralCLM M (Theta q) / q.1 := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, _hActivity,
      hTheta, hData, hThetaFold, hThetaInside⟩ :=
    PerronWright.NormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  let G : ℂ × C(S, ℂ) → ℂ := fun q ↦
    GC.treeDissymmetryFunctional M (Theta q)
  have hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) := by
    intro q hq
    exact treeDissymmetryFunctional_analyticAt_comp M (hTheta q hq)
  have hderiv : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      q.1 ≠ 0 →
        deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
          MPR.scalarIntegralCLM M (Theta q) / q.1 := by
    intro q hq hqne
    let rho : ℂ := RadiusResponse.radius M hM q.2
    let z : ℂ → ℂ := fun w ↦ rho * w
    let T : ℂ → C(S, ℂ) := fun w ↦ Theta (w, q.2)
    have hrho : rho ≠ 0 := (hData q hq).1
    have hslice : AnalyticAt ℂ T q.1 :=
      (hTheta q hq).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    have hz : HasDerivAt z rho q.1 := by
      simpa only [z, id_eq, mul_one] using
        (hasDerivAt_id q.1).const_mul rho
    have hopen : IsOpen
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) :=
      (Transfer.isOpen_cartesianDelta eta 0).prod Metric.isOpen_ball
    have hfix : ∀ᶠ w : ℂ in nhds q.1,
        T w = z w • NormedSpace.exp
          (q.2 - TreeCritical.degree M +
            M.kernel.complexActionCLM M.mu (T w)) := by
      have hline : Tendsto (fun w : ℂ ↦ (w, q.2))
          (nhds q.1) (nhds q) := by
        simpa only [id_eq, Prod.eta] using
          (continuousAt_id.prodMk continuousAt_const).tendsto
      filter_upwards [hline.eventually (hopen.mem_nhds hq)] with w hw
      have hres := (hData (w, q.2) hw).2
      change T w - z w • NormedSpace.exp
        (q.2 - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (T w)) = 0 at hres
      exact sub_eq_zero.mp hres
    have hzne : z q.1 ≠ 0 := mul_ne_zero hrho hqne
    have hformula :=
      treeDissymmetryFunctional_hasDerivAt_of_fieldFixedPoint
        M q.2 hz hslice.differentiableAt.hasDerivAt hfix hzne
    change deriv (fun w : ℂ ↦
      GC.treeDissymmetryFunctional M (T w)) q.1 = _
    rw [hformula.deriv]
    simpa only [z, T, Prod.eta] using
      (mul_div_mul_left
        (MPR.scalarIntegralCLM M (Theta q)) q.1 hrho)
  have hGfold : Set.EqOn G
      (fun q ↦ GC.treeDissymmetryFunctional M
        (TreeNormalizedFoldActivity.normalizedFoldProfile M hM q))
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) := by
    intro q hq
    dsimp only [G]
    rw [hThetaFold hq]
  have hGinside : Set.EqOn (fun w : ℂ ↦ G (w, 0))
      (Match.zeroFieldTreeSeries M) (Metric.ball (0 : ℂ) 1) := by
    let theta : ℂ → C(S, ℂ) := fun w ↦ Theta (w, 0)
    let G₀ : ℂ → ℂ := fun w ↦ G (w, 0)
    have htheta : AnalyticOnNhd ℂ theta
        (Transfer.cartesianDelta eta 0) := by
      intro w hw
      exact (hTheta (w, 0) ⟨hw, Metric.mem_ball_self hs⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    have hG₀ : AnalyticOnNhd ℂ G₀
        (Transfer.cartesianDelta eta 0) := by
      intro w hw
      exact (hG (w, 0) ⟨hw, Metric.mem_ball_self hs⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    have hthetaInside : Set.EqOn theta M.rootedTreeSeries
        (Metric.ball (0 : ℂ) 1) := by
      simpa only [theta] using hThetaInside
    have hG₀def : ∀ w : ℂ,
        G₀ w = GC.treeDissymmetryFunctional M (theta w) := by
      intro w
      rfl
    have hG₀deriv : ∀ w ∈ Transfer.cartesianDelta eta 0, w ≠ 0 →
        deriv G₀ w = MPR.scalarIntegralCLM M (theta w) / w := by
      intro w hw hwne
      exact hderiv (w, 0) ⟨hw, Metric.mem_ball_self hs⟩ hwne
    simpa only [G₀] using
      GC.global_dissymmetry_eq_zeroFieldTreeSeries_on_unit
        M hM heta htheta hG₀ hthetaInside hG₀def hG₀deriv
  exact ⟨eta, r, s, Theta, G, heta, hr, hs, hTheta, hG, hData,
    hThetaFold, fun _ ↦ rfl, hGfold, hGinside, hderiv⟩

end PerronWright.FieldTreeGlobalDissymmetry
