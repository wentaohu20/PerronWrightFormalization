import PerronWright.Enumeration.SimpleCycleRayPrimitive

/-!
# Local complex logarithmic continuation of the simple-cycle series

The direct profile series is known only on the strict-subcritical physical
ray.  This file packages the logarithmic expression obtained there as a
genuine complex analytic continuation on a small principal-log slit disk.
It deliberately makes no convergence claim for the direct series away from
the positive real ray.
-/

open Filter Topology PerronWright Set
open scoped Topology RightActions

noncomputable section

namespace PerronWright.SimpleCycleLogContinuation

/- Keep the calculus and complex-algebra additive structures aligned. -/
@[reducible] local instance complexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

namespace MPR

export PerronWright.MarkedPathResolvent (profile)

end MPR

namespace JS

export PerronWright.JointSimpleCycleEGF (profileSimpleCycleSeries)

end JS

namespace SC

export PerronWright.SimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation)

end SC

namespace Prim

export PerronWright.SimpleCycleRayPrimitive
  (exists_profileSimpleCycleSeries_logarithmic_primitive)

end Prim

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The physical-ray formula determines a genuine local complex continuation
on the intersection of the principal logarithm's slit plane and a small disk.
The direct series is identified with this continuation only on the positive
real physical ray. -/
theorem exists_simpleCycle_logarithmic_continuation
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (B H : C(S, ℂ) × ℂ → ℂ) (C : ℂ) (r : ℝ) (G : ℂ → ℂ),
      AnalyticAt ℂ B (0, 0) ∧
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      0 < r ∧
      (∀ X : ℂ, G X = -(1 / 2 : ℂ) * Complex.log X +
        H ((0 : C(S, ℂ)), X) + C) ∧
      IsOpen (Complex.slitPlane ∩ Metric.ball (0 : ℂ) r) ∧
      AnalyticOnNhd ℂ G
        (Complex.slitPlane ∩ Metric.ball (0 : ℂ) r) ∧
      (∀ X : ℂ, X ∈ Complex.slitPlane ∩ Metric.ball (0 : ℂ) r →
        HasDerivAt G
          (SC.simpleCycleDerivativeContinuation M hM
            ((0 : C(S, ℂ)), X)) X) ∧
      ∀ X : ℝ, 0 < X → X < r →
        JS.profileSimpleCycleSeries M
            (MPR.profile M hM ((0 : C(S, ℂ)), (X : ℂ))) = G (X : ℂ) := by
  obtain ⟨B, H, hBa, hHa, hHaxis, hsplit, hHderiv,
      ε, C, hε, hphysical⟩ :=
    Prim.exists_profileSimpleCycleSeries_logarithmic_primitive M hM
  have hgoodQ : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ H q ∧
      (q.2 ≠ 0 → SC.simpleCycleDerivativeContinuation M hM q =
        -(1 / 2 : ℂ) * q.2⁻¹ + B q) ∧
      (fderiv ℂ H q) (0, 1) = B q := by
    filter_upwards [hHa.eventually_analyticAt, hsplit, hHderiv]
      with q hHq hsplitq hHderivq
    exact ⟨hHq, hsplitq, hHderivq⟩
  have hlineAt : AnalyticAt ℂ
      (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hgoodX : ∀ᶠ X : ℂ in 𝓝 0,
      AnalyticAt ℂ H ((0 : C(S, ℂ)), X) ∧
      (X ≠ 0 → SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), X) =
        -(1 / 2 : ℂ) * X⁻¹ + B ((0 : C(S, ℂ)), X)) ∧
      (fderiv ℂ H ((0 : C(S, ℂ)), X)) (0, 1) =
        B ((0 : C(S, ℂ)), X) :=
    hlineAt.continuousAt.eventually hgoodQ
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hgoodX
  let r : ℝ := min ε δ
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hε hδ
  let G : ℂ → ℂ := fun X =>
    -(1 / 2 : ℂ) * Complex.log X + H ((0 : C(S, ℂ)), X) + C
  let U : Set ℂ := Complex.slitPlane ∩ Metric.ball (0 : ℂ) r
  have hUopen : IsOpen U :=
    Complex.isOpen_slitPlane.inter Metric.isOpen_ball
  have hdata : ∀ X : ℂ, X ∈ U →
      AnalyticAt ℂ H ((0 : C(S, ℂ)), X) ∧
      (X ≠ 0 → SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), X) =
        -(1 / 2 : ℂ) * X⁻¹ + B ((0 : C(S, ℂ)), X)) ∧
      (fderiv ℂ H ((0 : C(S, ℂ)), X)) (0, 1) =
        B ((0 : C(S, ℂ)), X) := by
    intro X hX
    apply hball
    have hnorm : ‖X‖ < r := by
      simpa only [U, Metric.mem_ball, dist_zero_right] using hX.2
    simpa only [dist_zero_right] using
      hnorm.trans_le (min_le_right ε δ)
  have hGanalytic : AnalyticOnNhd ℂ G U := by
    intro X hX
    obtain ⟨hHfull, -, -⟩ := hdata X hX
    have hHslice : AnalyticAt ℂ
        (fun Y : ℂ => H ((0 : C(S, ℂ)), Y)) X :=
      hHfull.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    have hlog : AnalyticAt ℂ Complex.log X :=
      analyticAt_clog hX.1
    have hformula : AnalyticAt ℂ
        (fun Y : ℂ => -(1 / 2 : ℂ) * Complex.log Y +
          H ((0 : C(S, ℂ)), Y) + C) X :=
      ((analyticAt_const.mul hlog).add hHslice).add analyticAt_const
    simpa only [G] using hformula
  have hGderiv : ∀ X : ℂ, X ∈ U →
      HasDerivAt G
        (SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), X)) X := by
    intro X hX
    obtain ⟨hHfull, hsplitX, hHvertical⟩ := hdata X hX
    have hXne : X ≠ 0 :=
      (Complex.mem_slitPlane_iff_arg.mp hX.1).2
    have hlineDeriv : HasDerivAt
        (fun Y : ℂ => ((0 : C(S, ℂ)), Y))
        ((0 : C(S, ℂ)), (1 : ℂ)) X :=
      (hasDerivAt_const X (0 : C(S, ℂ))).prodMk (hasDerivAt_id X)
    have hHraw :=
      hHfull.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt X hlineDeriv
    have hHslice : HasDerivAt
        (fun Y : ℂ => H ((0 : C(S, ℂ)), Y))
        (B ((0 : C(S, ℂ)), X)) X := by
      have h := hHraw.congr_deriv hHvertical
      simpa only [Function.comp_def] using h
    have hlog : HasDerivAt Complex.log X⁻¹ X :=
      Complex.hasDerivAt_log hX.1
    have hformula :=
      ((hlog.const_mul (-(1 / 2 : ℂ))).add hHslice).add_const C
    have hderivEq :
        -(1 / 2 : ℂ) * X⁻¹ + B ((0 : C(S, ℂ)), X) =
          SC.simpleCycleDerivativeContinuation M hM
            ((0 : C(S, ℂ)), X) :=
      (hsplitX hXne).symm
    rw [HasDerivAt, HasDerivAtFilter]
    refine ⟨?_⟩
    have hd := hformula.congr_deriv hderivEq
    rw [HasDerivAt, HasDerivAtFilter] at hd
    simpa only [G, Pi.add_apply] using hd.isLittleOTVS
  have hphysicalG : ∀ X : ℝ, 0 < X → X < r →
      JS.profileSimpleCycleSeries M
          (MPR.profile M hM ((0 : C(S, ℂ)), (X : ℂ))) = G (X : ℂ) := by
    intro X hX hXr
    have hXε : X < ε := hXr.trans_le (min_le_left ε δ)
    have heq := hphysical X hX hXε
    simpa only [G] using heq
  refine ⟨B, H, C, r, G, hBa, hHa, hHaxis, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    rfl
  · simpa only [U] using hUopen
  · exact hGanalytic
  · exact hGderiv
  · exact hphysicalG

end PerronWright.SimpleCycleLogContinuation
