import PerronWright.Analysis.FiniteIrreducibleRadiusResponse
import PerronWright.Analysis.FieldLogRadiusTaylor

/-!
# Second-order Taylor interfaces for the literal finite critical pair

All functions below are components of the constructed analytic critical pair.
The generic analytic increment estimate is reused without any model hypotheses.
The diagonal quadratic term is the actual second Fréchet derivative and the
remainder is cubic. No convergence-radius or least-tree-branch identification
is asserted here.
-/

open Filter Topology Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleRadiusTaylor

section BanachTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The true quadratic Taylor polynomial of an analytic scalar germ has a
cubic remainder, in the norm of the entire Banach field. -/
theorem analytic_quadratic_remainder {F : E → ℂ} (hF : AnalyticAt ℂ F 0) :
    (fun h : E ↦ F h - F 0 - (fderiv ℂ F 0) h -
      (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 F 0) (fun _ ↦ h)) =O[𝓝 0]
        (fun h ↦ ‖h‖ ^ 3) := by
  obtain ⟨p, hp⟩ := hF
  have hb := hp.isBigO_sub_partialSum_pow 3
  have h1 (h : E) : p 1 (fun _ ↦ h) = (fderiv ℂ F 0) h := by
    rw [hp.fderiv_eq, continuousMultilinearCurryFin1_apply]
    congr 1
  have h2 (h : E) : p 2 (fun _ ↦ h) =
      (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 F 0) (fun _ ↦ h) := by
    obtain ⟨r, hr⟩ := hp
    have he := hr.factorial_smul h 2
    norm_num [nsmul_eq_mul] at he
    linear_combination (1 / 2 : ℂ) * he
  have hs (h : E) : p.partialSum 3 h =
      F 0 + (fderiv ℂ F 0) h +
        (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 F 0) (fun _ ↦ h) := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hp.coeff_zero, h1, h2]
  simpa only [zero_add, hs, sub_add_eq_sub_sub] using hb

end BanachTaylor

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

def logRadius (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (g : C(S, ℂ)) : ℂ := Complex.log (FiniteIrreducibleRadiusResponse.radius M hcrit g)

theorem logRadius_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (logRadius M hcrit) 0 := by
  have hlog : AnalyticAt ℂ Complex.log (FiniteIrreducibleRadiusResponse.radius M hcrit 0) := by
    simpa only [FiniteIrreducibleRadiusResponse.radius_base] using
      analyticAt_clog Complex.one_mem_slitPlane
  exact hlog.comp (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit)

@[simp] theorem logRadius_zero (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    logRadius M hcrit 0 = 0 := by
  simp [logRadius, FiniteIrreducibleRadiusResponse.radius_base]

theorem logRadius_fderiv (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f : C(S, ℂ)) :
    (fderiv ℂ (logRadius M hcrit) 0) f = -M.weightedFunctional hcrit f := by
  have hlog : HasDerivAt Complex.log
      (FiniteIrreducibleRadiusResponse.radius M hcrit 0)⁻¹
        (FiniteIrreducibleRadiusResponse.radius M hcrit 0) := by
    simpa only [FiniteIrreducibleRadiusResponse.radius_base] using
      Complex.hasDerivAt_log Complex.one_mem_slitPlane
  have hd := hlog.comp_hasFDerivAt 0
    (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit).differentiableAt.hasFDerivAt
  have he := congrArg (fun A : C(S, ℂ) →L[ℂ] ℂ ↦ A f) hd.fderiv
  change (fderiv ℂ (logRadius M hcrit) 0) f = _ at he
  simpa only [smul_apply, smul_eq_mul,
    FiniteIrreducibleRadiusResponse.radius_base, inv_one, one_mul,
    FiniteIrreducibleRadiusResponse.radius_fderiv_weighted] using he

theorem exists_radius_increment_bound (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : C(S, ℂ), ‖g‖ + ‖f‖ < ε →
      ‖FiniteIrreducibleRadiusResponse.radius M hcrit (g + f) -
          FiniteIrreducibleRadiusResponse.radius M hcrit g + M.weightedFunctional hcrit f‖ ≤
        C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
  obtain ⟨ε, C, hε, hC, hb⟩ := FieldLogRadiusTaylor.analytic_increment_bound
    (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit)
  refine ⟨ε, C, hε, hC, ?_⟩
  intro g f hgf
  simpa only [FiniteIrreducibleRadiusResponse.radius_fderiv_weighted, sub_neg_eq_add]
    using hb g f hgf

theorem exists_logRadius_increment_bound (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : C(S, ℂ), ‖g‖ + ‖f‖ < ε →
      ‖logRadius M hcrit (g + f) - logRadius M hcrit g + M.weightedFunctional hcrit f‖ ≤
        C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
  obtain ⟨ε, C, hε, hC, hb⟩ := FieldLogRadiusTaylor.analytic_increment_bound
    (logRadius_analytic M hcrit)
  refine ⟨ε, C, hε, hC, ?_⟩
  intro g f hgf
  simpa only [logRadius_fderiv, sub_neg_eq_add] using hb g f hgf

theorem radius_quadratic_remainder (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (fun h : C(S, ℂ) ↦ FiniteIrreducibleRadiusResponse.radius M hcrit h - 1 +
      M.weightedFunctional hcrit h - (1 / 2 : ℂ) *
        (iteratedFDeriv ℂ 2 (FiniteIrreducibleRadiusResponse.radius M hcrit) 0)
          (fun _ ↦ h)) =O[𝓝 0] (fun h ↦ ‖h‖ ^ 3) := by
  simpa only [FiniteIrreducibleRadiusResponse.radius_base,
    FiniteIrreducibleRadiusResponse.radius_fderiv_weighted, sub_neg_eq_add] using
      analytic_quadratic_remainder (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit)

theorem logRadius_quadratic_remainder (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (fun h : C(S, ℂ) ↦ logRadius M hcrit h + M.weightedFunctional hcrit h -
      (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 (logRadius M hcrit) 0) (fun _ ↦ h)) =O[𝓝 0]
        (fun h ↦ ‖h‖ ^ 3) := by
  simpa only [logRadius_zero, sub_zero, logRadius_fderiv, sub_neg_eq_add] using
    analytic_quadratic_remainder (logRadius_analytic M hcrit)

/-- A single explicit neighborhood and constant control the actual quadratic
log-radius remainder in every field direction. -/
theorem exists_logRadius_quadratic_bound (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ h : C(S, ℂ), ‖h‖ < ε →
      ‖logRadius M hcrit h + M.weightedFunctional hcrit h -
        (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 (logRadius M hcrit) 0) (fun _ ↦ h)‖ ≤
          C * ‖h‖ ^ 3 := by
  obtain ⟨C₀, hb⟩ := isBigO_iff.mp (logRadius_quadratic_remainder M hcrit)
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he : ∀ᶠ h : C(S, ℂ) in 𝓝 0,
      ‖logRadius M hcrit h + M.weightedFunctional hcrit h -
        (1 / 2 : ℂ) * (iteratedFDeriv ℂ 2 (logRadius M hcrit) 0) (fun _ ↦ h)‖ ≤
          C * ‖h‖ ^ 3 := by
    filter_upwards [hb] with h hh
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg h) 3)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (norm_nonneg h) 3))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨ε, C, hε, hC, fun h hh ↦
    hball (by simpa only [dist_zero_right] using hh)⟩

end PerronWright.FiniteIrreducibleRadiusTaylor
