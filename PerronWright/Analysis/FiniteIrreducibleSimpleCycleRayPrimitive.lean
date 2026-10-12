import PerronWright.Analysis.FiniteIrreducibleSimpleCyclePhysicalRayBridge
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Integrating the physical-ray simple-cycle derivative

The direct simple-cycle series and the independently constructed resolvent
continuation have already been identified at the derivative level on a short
positive real fold ray.  Here the regular-part primitive is used to integrate
that identity.  The remaining additive constant is constructed by constancy
of a zero-derivative real restriction; no value for it is assumed.
-/

open Filter Topology PerronWright Set
open scoped Topology RightActions

noncomputable section

namespace PerronWright.FiniteIrreducibleSimpleCycleRayPrimitive

/- Keep the additive structure used by the calculus API aligned with the
structure inherited from the normed additive group.  The complex imports
expose a definitionally different legacy additive instance as well. -/
@[reducible] local instance complexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

namespace MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent (profile)

end MPR

namespace JS

export PerronWright.JointSimpleCycleEGF (profileSimpleCycleSeries)

end JS

namespace SC

export PerronWright.FiniteIrreducibleSimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation
   exists_simpleCycleDerivativeContinuation_regularPrimitive)

end SC

namespace Ray

export PerronWright.FiniteIrreducibleSimpleCyclePhysicalRayBridge
  (exists_profileSimpleCycleSeries_physical_ray)

end Ray

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- On a sufficiently short positive real physical ray, the direct
simple-cycle series is a logarithmic primitive of the marked-resolvent
continuation.  The additive constant is produced by the derivative-zero
theorem on the connected real interval; it is not postulated or numerically
identified. -/
theorem exists_profileSimpleCycleSeries_logarithmic_primitive
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ B H : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ B (0, 0) ∧
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0), q.2 ≠ 0 →
        SC.simpleCycleDerivativeContinuation M hM q =
          -(1 / 2 : ℂ) * q.2⁻¹ + B q) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0),
        (fderiv ℂ H q) (0, 1) = B q) ∧
      ∃ ε : ℝ, ∃ C : ℂ, 0 < ε ∧ ∀ X : ℝ, 0 < X → X < ε →
        JS.profileSimpleCycleSeries M.bjrModel
            (MPR.profile M hM ((0 : C(S, ℂ)), (X : ℂ))) =
          -(1 / 2 : ℂ) * Complex.log (X : ℂ) +
            H ((0 : C(S, ℂ)), (X : ℂ)) + C := by
  obtain ⟨B, H, hBa, hHa, hHaxis, hsplit, hHderiv⟩ :=
    SC.exists_simpleCycleDerivativeContinuation_regularPrimitive M hM
  obtain ⟨εr, hεr, hray⟩ :=
    Ray.exists_profileSimpleCycleSeries_physical_ray M hM
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
          ((0 : C(S, ℂ)), X) = -(1 / 2 : ℂ) * X⁻¹ +
            B ((0 : C(S, ℂ)), X)) ∧
      (fderiv ℂ H ((0 : C(S, ℂ)), X)) (0, 1) =
        B ((0 : C(S, ℂ)), X) :=
    hlineAt.continuousAt.eventually hgoodQ
  obtain ⟨εa, hεa, hball⟩ := Metric.eventually_nhds_iff.mp hgoodX
  let ε : ℝ := min εr εa
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεr hεa
  let F : ℂ → ℂ := fun X =>
    JS.profileSimpleCycleSeries M.bjrModel
        (MPR.profile M hM ((0 : C(S, ℂ)), X)) +
      (1 / 2 : ℂ) * Complex.log X -
      H ((0 : C(S, ℂ)), X)
  let f : ℝ → ℂ := fun X => F (X : ℂ)
  have hzero : ∀ X : ℝ, X ∈ Ioo 0 ε → HasDerivAt f 0 X := by
    intro X hXmem
    have hX : 0 < X := hXmem.1
    have hXε : X < ε := hXmem.2
    have hXεr : X < εr := hXε.trans_le (min_le_left _ _)
    have hXεa : X < εa := hXε.trans_le (min_le_right _ _)
    have hdist : dist (X : ℂ) 0 < εa := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hX]
      exact hXεa
    obtain ⟨hHfull, hsplitX, hHvertical⟩ := hball hdist
    have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
    have hdirectRaw := (hray X hX hXεr).2.2.2
    have hdirect : HasDerivAt
        (fun Y : ℂ => JS.profileSimpleCycleSeries M.bjrModel
          (MPR.profile M hM ((0 : C(S, ℂ)), Y)))
        (SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) := by
      change HasDerivAt
        (fun Y : ℂ => JS.profileSimpleCycleSeries M.bjrModel
          (MPR.profile M hM ((0 : C(S, ℂ)), Y)))
        (SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) at hdirectRaw
      exact hdirectRaw
    have hlineDeriv : HasDerivAt
        (fun Y : ℂ => ((0 : C(S, ℂ)), Y))
        ((0 : C(S, ℂ)), (1 : ℂ)) (X : ℂ) :=
      (hasDerivAt_const (X : ℂ) (0 : C(S, ℂ))).prodMk
        (hasDerivAt_id (X : ℂ))
    have hHraw :=
      hHfull.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt
        (X : ℂ) hlineDeriv
    have hHslice : HasDerivAt
        (fun Y : ℂ => H ((0 : C(S, ℂ)), Y))
        (B ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) := by
      have h := hHraw.congr_deriv hHvertical
      simpa only [Function.comp_def] using h
    have hlog : HasDerivAt Complex.log ((X : ℂ)⁻¹) (X : ℂ) :=
      Complex.hasDerivAt_log (Complex.ofReal_mem_slitPlane.mpr hX)
    have hreal :=
      (hdirect.comp_ofReal.add
        ((hlog.const_mul (1 / 2 : ℂ)).comp_ofReal)).sub
        hHslice.comp_ofReal
    have hcancel :
        SC.simpleCycleDerivativeContinuation M hM
            ((0 : C(S, ℂ)), (X : ℂ)) +
            (1 / 2 : ℂ) * (X : ℂ)⁻¹ -
            B ((0 : C(S, ℂ)), (X : ℂ)) = 0 := by
      rw [hsplitX hXne]
      ring
    rw [HasDerivAt, HasDerivAtFilter]
    refine ⟨?_⟩
    have hr := hreal.congr_deriv hcancel
    rw [HasDerivAt, HasDerivAtFilter] at hr
    simpa only [f, F, Pi.add_apply, Pi.sub_apply] using hr.isLittleOTVS
  have hdiff : DifferentiableOn ℝ f (Ioo 0 ε) := by
    intro X hX
    exact (hzero X hX).differentiableAt.differentiableWithinAt
  have hderivZero : (Ioo 0 ε).EqOn (deriv f) 0 := by
    intro X hX
    exact (hzero X hX).deriv
  obtain ⟨C, hC⟩ :=
    isOpen_Ioo.exists_is_const_of_deriv_eq_zero
      (convex_Ioo (0 : ℝ) ε).isPreconnected hdiff hderivZero
  refine ⟨B, H, hBa, hHa, hHaxis, hsplit, hHderiv, ε, C, hε, ?_⟩
  intro X hX hXε
  have hconst := hC X ⟨hX, hXε⟩
  calc
    JS.profileSimpleCycleSeries M.bjrModel
        (MPR.profile M hM ((0 : C(S, ℂ)), (X : ℂ))) =
        -(1 / 2 : ℂ) * Complex.log (X : ℂ) +
          H ((0 : C(S, ℂ)), (X : ℂ)) + f X := by
            dsimp only [f, F]
            ring
    _ = -(1 / 2 : ℂ) * Complex.log (X : ℂ) +
          H ((0 : C(S, ℂ)), (X : ℂ)) + C := by rw [hconst]

end PerronWright.FiniteIrreducibleSimpleCycleRayPrimitive
