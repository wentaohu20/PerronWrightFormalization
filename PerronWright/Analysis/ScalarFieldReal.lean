import PerronWright.Analysis.ScalarFieldTaylor

open MeasureTheory
open scoped Topology
noncomputable section

namespace PerronWright.ScalarFieldResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem scalarCriticalRadius_real_positive_near_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ t : ℝ in 𝓝 1,
      (RadiusResponse.radius M hM (scalarFieldComplex M (t : ℂ))).im = 0 ∧
      0 < (RadiusResponse.radius M hM (scalarFieldComplex M (t : ℂ))).re := by
  obtain ⟨ε, hε, hpos⟩ := CriticalPair.criticalPair_real_positive_radius M hM
  have hcont : ContinuousAt (fun t : ℝ => scalarFieldComplex M (t : ℂ)) 1 := by
    have hc : ContinuousAt (scalarFieldComplex M) ((1 : ℝ) : ℂ) := by
      simpa using (scalarFieldComplex_analyticAt_one M).continuousAt
    exact hc.comp Complex.continuous_ofReal.continuousAt
  have hlim : Filter.Tendsto (fun t : ℝ => scalarFieldComplex M (t : ℂ))
      (𝓝 1) (𝓝 (0 : C(S, ℂ))) := by
    simpa [scalarFieldComplex_one] using hcont.tendsto
  have hev : ∀ᶠ t : ℝ in 𝓝 1, ‖scalarFieldComplex M (t : ℂ)‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hlim ε hε)
  have htpos : ∀ᶠ t : ℝ in 𝓝 1, 0 < t :=
    (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
  filter_upwards [hev, htpos] with t hg ht
  have hstar : star (scalarFieldComplex M (t : ℂ)) =
      scalarFieldComplex M (t : ℂ) := by
    rw [scalarFieldComplex_ofReal M t ht]
    ext x
    simp [CompactBJRModel.complexifyField_apply]
  rcases hpos _ hg hstar with ⟨him, hre, _⟩
  exact ⟨him, hre⟩

end PerronWright.ScalarFieldResponse
