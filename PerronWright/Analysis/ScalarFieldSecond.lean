import PerronWright.Analysis.ScalarFieldReal

open MeasureTheory
open scoped Topology
noncomputable section

namespace PerronWright.ScalarFieldResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem scalarFieldComplex_hasDerivAt (M : CompactBJRModel S)
    {t : ℂ} (ht : t ∈ Complex.slitPlane) :
    HasDerivAt (scalarFieldComplex M)
      (t⁻¹ • (1 : C(S, ℂ)) - TreeCritical.degree M) t := by
  have hlog : HasDerivAt Complex.log t⁻¹ t := Complex.hasDerivAt_log ht
  have h := (hlog.smul_const (1 : C(S, ℂ))).sub
    (((hasDerivAt_id t).sub_const 1).smul_const (TreeCritical.degree M))
  convert h using 1
  all_goals first | rfl | simp only [one_smul]

theorem scalarFieldComplex_deriv_of_slitPlane (M : CompactBJRModel S)
    {t : ℂ} (ht : t ∈ Complex.slitPlane) :
    deriv (scalarFieldComplex M) t =
      t⁻¹ • (1 : C(S, ℂ)) - TreeCritical.degree M :=
  (scalarFieldComplex_hasDerivAt M ht).deriv

theorem scalarFieldComplex_second_deriv_one (M : CompactBJRModel S) :
    deriv (deriv (scalarFieldComplex M)) 1 = -(1 : C(S, ℂ)) := by
  have hloc :
      (fun t : ℂ => deriv (scalarFieldComplex M) t) =ᶠ[𝓝 1]
        (fun t : ℂ => t⁻¹ • (1 : C(S, ℂ)) - TreeCritical.degree M) := by
    filter_upwards [Complex.isOpen_slitPlane.eventually_mem Complex.one_mem_slitPlane]
      with t ht
    exact scalarFieldComplex_deriv_of_slitPlane M ht
  have hinv : HasDerivAt (fun t : ℂ => t⁻¹) (-(1 : ℂ)) 1 := by
    simpa using (hasDerivAt_inv (show (1 : ℂ) ≠ 0 by norm_num))
  have h := ((hinv.smul_const (1 : C(S, ℂ))).sub_const (TreeCritical.degree M)).deriv
  rw [hloc.deriv_eq] 
  simpa only [one_smul, neg_smul] using h

end PerronWright.ScalarFieldResponse
