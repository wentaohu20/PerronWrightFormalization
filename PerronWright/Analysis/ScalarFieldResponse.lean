import PerronWright.Analysis.RadiusResponse
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open MeasureTheory
open scoped Topology
noncomputable section

namespace PerronWright.ScalarFieldResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Complexification of the paper's scalar change of field. -/
def scalarFieldComplex (M : CompactBJRModel S) (t : ℂ) : C(S, ℂ) :=
  Complex.log t • (1 : C(S, ℂ)) - (t - 1) • TreeCritical.degree M

@[simp] theorem scalarFieldComplex_one (M : CompactBJRModel S) :
    scalarFieldComplex M 1 = 0 := by
  simp [scalarFieldComplex]

theorem scalarFieldComplex_hasDerivAt_one (M : CompactBJRModel S) :
    HasDerivAt (scalarFieldComplex M) (1 - TreeCritical.degree M) 1 := by
  have hlog : HasDerivAt Complex.log 1 (1 : ℂ) := by
    simpa using Complex.hasDerivAt_log Complex.one_mem_slitPlane
  have h := (hlog.smul_const (1 : C(S, ℂ))).sub
    (((hasDerivAt_id (1 : ℂ)).sub_const 1).smul_const (TreeCritical.degree M))
  convert h using 1
  all_goals first | rfl | simp only [one_smul]

theorem weightedIntegralComplex_one_sub_degree_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.weightedIntegralComplex hM (1 - TreeCritical.degree M) = 0 := by
  change M.weightedIntegralComplexCLM hM (1 - TreeCritical.degree M) = 0
  rw [map_sub]
  change M.weightedIntegralComplex hM 1 -
    M.weightedIntegralComplex hM (M.kernel.complexAction M.mu 1) = 0
  rw [M.weightedIntegralComplex_action hM 1]
  ring

theorem criticalRadius_scalar_deriv_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    deriv (fun t : ℂ => RadiusResponse.radius M hM (scalarFieldComplex M t)) 1 = 0 := by
  have hf := (RadiusResponse.radius_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  rw [← scalarFieldComplex_one M] at hf
  have h := hf.comp_hasDerivAt 1 (scalarFieldComplex_hasDerivAt_one M)
  have hd := h.deriv
  simp only [scalarFieldComplex_one] at hd
  rw [RadiusResponse.radius_fderiv_integral,
    weightedIntegralComplex_one_sub_degree_zero] at hd
  simpa only [Function.comp_def, neg_zero] using hd

end PerronWright.ScalarFieldResponse
