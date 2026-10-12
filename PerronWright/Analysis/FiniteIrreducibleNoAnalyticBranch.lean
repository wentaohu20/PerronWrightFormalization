import PerronWright.Analysis.FiniteIrreducibleUniformFieldFold

/-!
# No analytic zero-field tree branch through the critical point

The critical tree equation cannot be solved by a one-valued holomorphic
profile as a function of the ordinary activity coordinate through `z = 1`.
The proof differentiates the actual tree equation and applies the already
constructed Perron functional; no singularity hypothesis is assumed.
-/

open scoped Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- There is no analytic zero-field tree-solution curve through the critical
point when it is parametrized by the ordinary activity `z`. -/
theorem FiniteIrreducibleModel.not_exists_analytic_tree_curve_through_critical
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ¬ ∃ T : ℂ → C(S, ℂ),
      AnalyticAt ℂ T 1 ∧ T 1 = 1 ∧
      ∀ᶠ z : ℂ in 𝓝 1,
        M.treeResidual ((z, 0), T z) = 0 := by
  rintro ⟨T, hTa, hT1, hres⟩
  let z : ℂ → ℂ := fun s => 1 + s
  let U : ℂ → C(S, ℂ) := fun s => T (1 + s)
  have hza : AnalyticAt ℂ z 0 := analyticAt_const.add analyticAt_id
  have hUa : AnalyticAt ℂ U 0 := by
    have hinner : AnalyticAt ℂ (fun s : ℂ => 1 + s) 0 :=
      analyticAt_const.add analyticAt_id
    exact hTa.comp_of_eq hinner (by simp)
  have hshift : Filter.Tendsto (fun s : ℂ => 1 + s) (𝓝 0) (𝓝 1) := by
    simpa [z] using hza.continuousAt.tendsto
  have hres0 : ∀ᶠ s : ℂ in 𝓝 0,
      M.treeResidual ((z s, 0), U s) = 0 := by
    simpa only [z, U] using hshift.eventually hres
  have hcurve := FiniteIrreducibleUniformFieldFold.tree_curve_first_derivative M
    (0 : C(S, ℂ)) z U hza hUa (by
      filter_upwards [hres0] with s hs
      change U s - z s • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
          M.complexOperator (U s)) = 0 at hs
      simp only [zero_sub] at hs
      change U s = z s • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
          M.complexOperator (U s))
      simpa only [zero_sub] using sub_eq_zero.mp hs)
  change deriv U 0 =
      deriv z 0 • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
          M.complexOperator (U 0)) +
      z 0 • (NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
          M.complexOperator (U 0)) *
        M.complexOperator (deriv U 0)) at hcurve
  have hfirst : deriv U 0 =
      (1 : C(S, ℂ)) +
        M.complexOperator (deriv U 0) := by
    simpa [z, U, hT1, TreeCritical.degree, FiniteIrreducibleModel.complexOperator,
      FiniteIrreducibleModel.bjrModel] using hcurve
  have hell := congrArg (M.normalizedPerronFunctional hM) hfirst
  simp only [map_add, M.normalizedPerronFunctional_action hM,
    FiniteIrreducibleModel.normalizedPerronFunctional_one] at hell
  have hzero : (1 / (M.alpha hM : ℂ)) = 0 := by
    have hcancel :
        (1 / (M.alpha hM : ℂ)) +
            M.normalizedPerronFunctional hM (deriv U 0) =
          0 + M.normalizedPerronFunctional hM (deriv U 0) := by
      simpa only [zero_add] using hell.symm
    exact add_right_cancel hcancel
  exact (one_div_ne_zero
    (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne')) hzero

end PerronWright
