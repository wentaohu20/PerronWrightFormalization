import PerronWright.Analysis.FiniteIrreducibleUniformFieldFold
import PerronWright.Analysis.TreeFoldJointDivision

/-! Genuine joint quadratic division for the finite critical-field fold. -/

open scoped NNReal ENNReal
open Topology
noncomputable section

namespace PerronWright.FiniteIrreducibleFieldDivision

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

theorem centered_radius_joint_quadratic_factor (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ H : C(S, ℂ) × ℂ → ℂ, AnalyticAt ℂ H (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        FiniteIrreducibleRadiusResponse.radius M hM q.1 -
          (FiniteIrreducibleFieldFold.centeredFoldCurve M hM q).1 = q.2 ^ 2 * H q := by
  let f : C(S, ℂ) × ℂ → ℂ := fun q =>
    FiniteIrreducibleRadiusResponse.radius M hM q.1 -
      (FiniteIrreducibleFieldFold.centeredFoldCurve M hM q).1
  have hfa : AnalyticAt ℂ f (0, 0) := by
    have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ => q.1) (0, 0) :=
      analyticAt_fst
    exact ((FiniteIrreducibleRadiusResponse.radius_analytic M hM).comp_of_eq hfst rfl).sub
      (analyticAt_fst.comp (FiniteIrreducibleFieldFold.centeredFoldCurve_analytic M hM))
  have hf0 : ∀ᶠ g : C(S, ℂ) in 𝓝 0, f (g, 0) = 0 := by
    filter_upwards [FiniteIrreducibleFieldFold.centeredFoldCurve_critical M hM] with g hg
    change FiniteIrreducibleRadiusResponse.radius M hM g -
      (FiniteIrreducibleFieldFold.centeredFoldCurve M hM (g, 0)).1 = 0
    rw [hg]
    simp [FiniteIrreducibleRadiusResponse.radius]
  have hfd : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      deriv (fun t : ℂ => f (g, t)) 0 = 0 := by
    filter_upwards [FiniteIrreducibleUniformFieldFold.centered_radius_deriv_zero M hM] with g hg
    change deriv (fun t : ℂ => FiniteIrreducibleRadiusResponse.radius M hM g -
      (FiniteIrreducibleFieldFold.centeredFoldCurve M hM (g, t)).1) 0 = 0
    rw [deriv_const_sub]
    simp [hg]
  exact PerronWright.TreeFoldJointDivision.analytic_vertical_second_division hfa hf0 hfd

theorem centered_radius_joint_quadratic_factor_base (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ H : C(S, ℂ) × ℂ → ℂ, AnalyticAt ℂ H (0, 0) ∧
      H (0, 0) = (M.beta hM : ℂ) / 2 ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        FiniteIrreducibleRadiusResponse.radius M hM q.1 -
          (FiniteIrreducibleFieldFold.centeredFoldCurve M hM q).1 = q.2 ^ 2 * H q := by
  obtain ⟨H, hHa, hfactor⟩ := centered_radius_joint_quadratic_factor M hM
  obtain ⟨K, hKa, hKbase, hKfactor⟩ :=
    (FiniteIrreducibleUniformFieldFold.centered_radius_pointwise_quadratic_factor M hM).self_of_nhds
  have hsection : Filter.Tendsto (fun t : ℂ => ((0 : C(S, ℂ)), t))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_const.prod analyticAt_id : AnalyticAt ℂ
      (fun t : ℂ => ((0 : C(S, ℂ)), t)) 0).continuousAt.tendsto
  have hslice : ∀ᶠ t : ℂ in 𝓝 0,
      FiniteIrreducibleRadiusResponse.radius M hM 0 -
        (FiniteIrreducibleFieldFold.centeredFoldCurve M hM (0, t)).1 = t ^ 2 * H (0, t) := by
    simpa using hsection.eventually hfactor
  have hHK : ∀ᶠ t : ℂ in 𝓝[≠] 0, H (0, t) = K t := by
    filter_upwards [hslice.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht0
    have hmul : t ^ 2 * H (0, t) = t ^ 2 * K t := ht.symm.trans (hKfactor t)
    exact (mul_left_cancel₀ (pow_ne_zero 2 ht0) hmul)
  have hHslice : AnalyticAt ℂ (fun t : ℂ => H (0, t)) 0 :=
    hHa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hHatK : H (0, 0) = K 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      (hHslice.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hKa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hHK
  have hcurv : deriv (deriv (fun t : ℂ =>
      (FiniteIrreducibleFieldFold.centeredFoldCurve M hM (0, t)).1)) 0 =
      -(M.beta hM : ℂ) := by
    have hsame : (fun t : ℂ => (FiniteIrreducibleFieldFold.centeredFoldCurve M hM (0, t)).1) =
        FiniteIrreducibleFieldCurvature.radiusSlice M hM := by
      funext t
      simp [FiniteIrreducibleFieldFold.centeredFoldCurve, FiniteIrreducibleFieldFold.criticalCoordinate_base,
        FiniteIrreducibleFieldCurvature.radiusSlice]
    rw [hsame]
    exact FiniteIrreducibleFieldCurvature.radiusSlice_second_deriv M hM
  refine ⟨H, hHa, ?_, hfactor⟩
  rw [hHatK, hKbase, hcurv]
  ring

end PerronWright.FiniteIrreducibleFieldDivision
