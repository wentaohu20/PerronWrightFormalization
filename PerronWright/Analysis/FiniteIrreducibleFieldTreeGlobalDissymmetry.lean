import PerronWright.Analysis.FiniteIrreducibleTreeDissymmetry
import PerronWright.Enumeration.FieldTreeGlobalDissymmetry

/-!
# Genuine finite irreducible field-tree global dissymmetry

The actual normalized finite rooted profile is inserted into the literal
tree dissymmetry functional. Its field-dependent rooting derivative follows
from the residual equation. The pure symmetry calculation uses discrete BJR
data only; no regular-critical or primitive adapter is supplied.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldTreeGlobalDissymmetry

export PerronWright.FieldTreeGlobalDissymmetry
  (treeDissymmetryFunctional_analyticAt_comp
   treeDissymmetryFunctional_hasDerivAt_of_fieldFixedPoint)

namespace GC
export PerronWright.ZeroFieldTreeGlobalContinuation
  (treeDissymmetryFunctional)
export PerronWright.FiniteIrreducibleTreeDissymmetry
  (global_dissymmetry_eq_zeroFieldTreeSeries_on_unit)
end GC

namespace Match
export PerronWright.ZeroFieldTreeEGFMatching (zeroFieldTreeSeries)
end Match

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)
end MPR

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The jointly analytic normalized tree profile induces a jointly analytic
unrooted-tree continuation on the same Cartesian Delta product.  Its
zero-field slice is the literal tree EGF, and on the local fold product it is
the dissymmetry functional of the actual joint fold chart. -/
theorem exists_normalizedFieldTree_global_dissymmetry_profile
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
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
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel
            (FiniteIrreducibleNormalizedFoldActivity.activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta
        (FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile M hM)
        (FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = GC.treeDissymmetryFunctional M.bjrModel (Theta q)) ∧
      Set.EqOn G
        (fun q ↦ GC.treeDissymmetryFunctional M.bjrModel
          (FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile M hM q))
        (FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      Set.EqOn (fun w : ℂ ↦ G (w, 0))
        (Match.zeroFieldTreeSeries M.bjrModel) (Metric.ball (0 : ℂ) 1) ∧
      ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        q.1 ≠ 0 →
          deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
            MPR.scalarIntegralCLM M (Theta q) / q.1 := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, _hActivity,
      hTheta, hData, hThetaFold, hThetaInside⟩ :=
    PerronWright.FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  let G : ℂ × C(S, ℂ) → ℂ := fun q ↦
    GC.treeDissymmetryFunctional M.bjrModel (Theta q)
  have hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) := by
    intro q hq
    exact treeDissymmetryFunctional_analyticAt_comp M.bjrModel (hTheta q hq)
  have hderiv : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      q.1 ≠ 0 →
        deriv (fun w : ℂ ↦ G (w, q.2)) q.1 =
          MPR.scalarIntegralCLM M (Theta q) / q.1 := by
    intro q hq hqne
    let rho : ℂ := FiniteIrreducibleRadiusResponse.radius M hM q.2
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
          (q.2 - TreeCritical.degree M.bjrModel +
            M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T w)) := by
      have hline : Tendsto (fun w : ℂ ↦ (w, q.2))
          (nhds q.1) (nhds q) := by
        simpa only [id_eq, Prod.eta] using
          (continuousAt_id.prodMk continuousAt_const).tendsto
      filter_upwards [hline.eventually (hopen.mem_nhds hq)] with w hw
      have hres := (hData (w, q.2) hw).2
      change T w - z w • NormedSpace.exp
        (q.2 - TreeCritical.degree M.bjrModel +
          M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T w)) = 0 at hres
      exact sub_eq_zero.mp hres
    have hzne : z q.1 ≠ 0 := mul_ne_zero hrho hqne
    have hformula :=
      treeDissymmetryFunctional_hasDerivAt_of_fieldFixedPoint
        M.bjrModel q.2 hz hslice.differentiableAt.hasDerivAt hfix hzne
    change deriv (fun w : ℂ ↦
      GC.treeDissymmetryFunctional M.bjrModel (T w)) q.1 = _
    rw [hformula.deriv]
    simpa only [z, T, Prod.eta, FiniteIrreducibleTreeDissymmetry.scalarIntegralCLM_eq_bjr] using
      (mul_div_mul_left
        (MPR.scalarIntegralCLM M (Theta q)) q.1 hrho)
  have hGfold : Set.EqOn G
      (fun q ↦ GC.treeDissymmetryFunctional M.bjrModel
        (FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile M hM q))
      (FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) := by
    intro q hq
    dsimp only [G]
    rw [hThetaFold hq]
  have hGinside : Set.EqOn (fun w : ℂ ↦ G (w, 0))
      (Match.zeroFieldTreeSeries M.bjrModel) (Metric.ball (0 : ℂ) 1) := by
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
    have hthetaInside : Set.EqOn theta M.bjrModel.rootedTreeSeries
        (Metric.ball (0 : ℂ) 1) := by
      simpa only [theta] using hThetaInside
    have hG₀def : ∀ w : ℂ,
        G₀ w = GC.treeDissymmetryFunctional M.bjrModel (theta w) := by
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


end PerronWright.FiniteIrreducibleFieldTreeGlobalDissymmetry
