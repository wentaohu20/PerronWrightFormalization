import PerronWright.Analysis.ScalarFieldBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open MeasureTheory
open scoped Topology
noncomputable section

namespace PerronWright.ScalarFieldResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem scalarFieldComplex_analyticAt_one (M : CompactBJRModel S) :
    AnalyticAt ℂ (scalarFieldComplex M) 1 := by
  have hlog : AnalyticAt ℂ Complex.log 1 :=
    analyticAt_clog Complex.one_mem_slitPlane
  have hlin : AnalyticAt ℂ (fun t : ℂ => t - 1) 1 :=
    analyticAt_id.sub analyticAt_const
  have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : C(S, ℂ))) 1 := analyticAt_const
  have hdeg : AnalyticAt ℂ (fun _ : ℂ => TreeCritical.degree M) 1 := analyticAt_const
  have h : AnalyticAt ℂ
      (fun t : ℂ => Complex.log t • (1 : C(S, ℂ)) -
        (t - 1) • TreeCritical.degree M) 1 :=
    (hlog.smul hone).sub (hlin.smul hdeg)
  exact h

theorem scalarCriticalRadius_analyticAt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ
      (fun t : ℂ => RadiusResponse.radius M hM (scalarFieldComplex M t)) 1 := by
  exact (RadiusResponse.radius_analytic M hM).comp_of_eq
    (scalarFieldComplex_analyticAt_one M) (scalarFieldComplex_one M)

theorem scalarCriticalRadius_quadratic_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun y : ℂ =>
      RadiusResponse.radius M hM (scalarFieldComplex M (1 + y)) - 1)
      =O[𝓝 (0 : ℂ)] (fun y : ℂ => ‖y‖ ^ 2) := by
  let f : ℂ → ℂ := fun t => RadiusResponse.radius M hM (scalarFieldComplex M t)
  obtain ⟨p, hp⟩ := scalarCriticalRadius_analyticAt_one M hM
  have hf0 : f 1 = 1 := by
    simp [f, scalarFieldComplex_one, RadiusResponse.radius_base]
  have hder : deriv f 1 = 0 := criticalRadius_scalar_deriv_zero M hM
  have hp1 (y : ℂ) : p 1 (fun _ => y) = 0 := by
    have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L y) hp.fderiv_eq
    change deriv (fun t : ℂ => RadiusResponse.radius M hM (scalarFieldComplex M t)) 1 = 0 at hder
    simpa only [continuousMultilinearCurryFin1_apply,
      Fin.snoc_zero, fderiv_eq_smul_deriv, hder, smul_zero] using h.symm
  have hsum (y : ℂ) : p.partialSum 2 y = 1 := by
    change (∑ k ∈ Finset.range 2, p k (fun _ => y)) = 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, hp1, add_zero]
    exact (hp.coeff_zero (fun _ : Fin 0 => y)).trans hf0
  have hb := hp.isBigO_sub_partialSum_pow 2
  simpa only [f, hsum] using hb

end PerronWright.ScalarFieldResponse
