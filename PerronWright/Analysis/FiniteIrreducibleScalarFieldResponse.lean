import PerronWright.Analysis.FiniteIrreducibleRadiusResponse
import PerronWright.Analysis.ScalarFieldSecond

/-!
# Literal finite irreducible scalar critical response

The field is the paper's `log t - (t - 1)d`. The radius and profile are
the constructed finite critical pair, without a primitive-kernel hypothesis.
The eigenvalue-one constraint fixes the Perron component of the profile tangent.
-/

open MeasureTheory Filter Topology
open scoped Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleScalarFieldResponse

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

def scalarField (M : FiniteIrreducibleModel S) : ℂ → C(S, ℂ) :=
  ScalarFieldResponse.scalarFieldComplex M.bjrModel

def scalarRadius (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (t : ℂ) : ℂ :=
  FiniteIrreducibleRadiusResponse.radius M hcrit (scalarField M t)

def scalarProfile (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (t : ℂ) : C(S, ℂ) :=
  FiniteIrreducibleRadiusResponse.profile M hcrit (scalarField M t)

@[simp] theorem scalarField_one (M : FiniteIrreducibleModel S) : scalarField M 1 = 0 :=
  ScalarFieldResponse.scalarFieldComplex_one M.bjrModel

theorem scalarField_analytic (M : FiniteIrreducibleModel S) :
    AnalyticAt ℂ (scalarField M) 1 :=
  ScalarFieldResponse.scalarFieldComplex_analyticAt_one M.bjrModel

theorem scalarField_hasDerivAt_one (M : FiniteIrreducibleModel S) :
    HasDerivAt (scalarField M) (1 - TreeCritical.degree M.bjrModel) 1 :=
  ScalarFieldResponse.scalarFieldComplex_hasDerivAt_one M.bjrModel

theorem scalarRadius_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (scalarRadius M hcrit) 1 :=
  (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit).comp_of_eq
    (scalarField_analytic M) (scalarField_one M)

theorem scalarProfile_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (scalarProfile M hcrit) 1 :=
  (FiniteIrreducibleRadiusResponse.profile_analytic M hcrit).comp_of_eq
    (scalarField_analytic M) (scalarField_one M)

@[simp] theorem scalarRadius_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    scalarRadius M hcrit 1 = 1 := by
  simp [scalarRadius, FiniteIrreducibleRadiusResponse.radius_base]

@[simp] theorem scalarProfile_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    scalarProfile M hcrit 1 = 1 := by
  simp [scalarProfile, FiniteIrreducibleRadiusResponse.profile_base]

theorem weightedFunctional_one_sub_degree_zero (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    M.weightedFunctional hcrit (1 - TreeCritical.degree M.bjrModel) = 0 := by
  rw [map_sub]
  change M.weightedFunctional hcrit 1 - M.weightedFunctional hcrit
    (M.complexOperator 1) = 0
  rw [M.weightedFunctional_action]
  exact sub_self _

theorem scalarRadius_deriv_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    deriv (scalarRadius M hcrit) 1 = 0 := by
  have hf := (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit).hasStrictFDerivAt.hasFDerivAt
  rw [← scalarField_one M] at hf
  have h := hf.comp_hasDerivAt 1 (scalarField_hasDerivAt_one M)
  have hd := h.deriv
  simp only [scalarField_one] at hd
  rw [FiniteIrreducibleRadiusResponse.radius_fderiv_weighted,
    weightedFunctional_one_sub_degree_zero] at hd
  change deriv (fun t ↦ FiniteIrreducibleRadiusResponse.radius M hcrit
    (scalarField M t)) 1 = 0
  simpa only [Function.comp_def, neg_zero] using hd

theorem scalarProfile_deriv_chain (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    deriv (scalarProfile M hcrit) 1 =
      (fderiv ℂ (FiniteIrreducibleRadiusResponse.profile M hcrit) 0)
        (1 - TreeCritical.degree M.bjrModel) := by
  have hf := (FiniteIrreducibleRadiusResponse.profile_analytic M hcrit).hasStrictFDerivAt.hasFDerivAt
  rw [← scalarField_one M] at hf
  change deriv (fun t ↦ FiniteIrreducibleRadiusResponse.profile M hcrit
    (scalarField M t)) 1 = _
  simpa only [Function.comp_def, scalarField_one] using
    (hf.comp_hasDerivAt 1 (scalarField_hasDerivAt_one M)).deriv

theorem scalarProfile_first_equation (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    deriv (scalarProfile M hcrit) 1 = 1 - TreeCritical.degree M.bjrModel +
      M.complexOperator (deriv (scalarProfile M hcrit) 1) := by
  rw [scalarProfile_deriv_chain]
  have hv := FiniteIrreducibleRadiusResponse.profile_fderiv_tree M hcrit
    (1 - TreeCritical.degree M.bjrModel)
  simpa only [FiniteIrreducibleRadiusResponse.radius_fderiv_weighted,
    weightedFunctional_one_sub_degree_zero, neg_zero, zero_smul, add_zero] using hv

theorem scalarProfile_critical_deriv_zero (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    (fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hcrit) 1)
      (deriv (scalarProfile M hcrit) 1) = 0 := by
  rw [scalarProfile_deriv_chain]
  exact FiniteIrreducibleRadiusResponse.profile_fderiv_eigenvalue_constraint M hcrit _

/-- The literal finite criticality constraint selects the exact profile tangent. -/
theorem scalarProfile_deriv_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    deriv (scalarProfile M hcrit) 1 = (1 : C(S, ℂ)) -
      ((M.alpha hcrit : ℂ) / (M.beta hcrit : ℂ)) • M.complexPerronFunction hcrit := by
  let U := deriv (scalarProfile M hcrit) 1
  let u := M.complexPerronFunction hcrit
  let D := fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hcrit) 1
  have hfirst := scalarProfile_first_equation M hcrit
  have hfix : M.complexOperator (U - 1) = U - 1 := by
    rw [map_sub]
    change M.complexOperator U - TreeCritical.degree M.bjrModel = U - 1
    change U = 1 - TreeCritical.degree M.bjrModel + M.complexOperator U at hfirst
    linear_combination -hfirst
  obtain ⟨c, hc⟩ := M.complex_fixed_eq_scalar_multiple hcrit (U - 1) hfix
  have hU : U = 1 + c • u := by
    change U - 1 = c • u at hc
    apply sub_eq_iff_eq_add.mp at hc
    rw [hc]
    abel
  have hD1 : D (1 : C(S, ℂ)) = 1 := by
    change (fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hcrit) 1) 1 = 1
    rw [FiniteIrreducibleCriticalPair.eigenvalue_fderiv, one_mul,
      M.normalizedPerronFunctional_perronFunction]
  have hDu : D u = (M.beta hcrit : ℂ) / (M.alpha hcrit : ℂ) :=
    FiniteIrreducibleCriticalPair.eigenvalue_fderiv_perron M hcrit
  have hconstraint := scalarProfile_critical_deriv_zero M hcrit
  change D U = 0 at hconstraint
  rw [hU, map_add, map_smul, smul_eq_mul, hD1, hDu] at hconstraint
  have ha : (M.alpha hcrit : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne'
  have hb : (M.beta hcrit : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hcrit).ne'
  have hmul : c * (M.beta hcrit : ℂ) = -(M.alpha hcrit : ℂ) := by
    field_simp [ha] at hconstraint
    linear_combination hconstraint
  have hcval : c = -((M.alpha hcrit : ℂ) / (M.beta hcrit : ℂ)) := by
    simpa only [neg_div] using (eq_div_iff hb).mpr hmul
  change U = 1 - ((M.alpha hcrit : ℂ) / (M.beta hcrit : ℂ)) • u
  rw [hU, hcval, neg_smul]
  rfl

theorem scalarRadius_real_positive_near_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ t : ℝ in 𝓝 1,
      (scalarRadius M hcrit (t : ℂ)).im = 0 ∧ 0 < (scalarRadius M hcrit (t : ℂ)).re := by
  obtain ⟨ε, hε, hpos⟩ := FiniteIrreducibleCriticalPair.criticalPair_real_positive_radius M hcrit
  have hc : ContinuousAt (fun t : ℝ ↦ scalarField M (t : ℂ)) 1 := by
    have hc' : ContinuousAt (scalarField M) ((1 : ℝ) : ℂ) := by
      simpa using (scalarField_analytic M).continuousAt
    exact hc'.comp Complex.continuous_ofReal.continuousAt
  have ht : Tendsto (fun t : ℝ ↦ scalarField M (t : ℂ)) (𝓝 1) (𝓝 (0 : C(S, ℂ))) := by
    simpa only [scalarField_one, Complex.ofReal_one] using hc.tendsto
  have he : ∀ᶠ t : ℝ in 𝓝 1, ‖scalarField M (t : ℂ)‖ < ε := by
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp ht ε hε
  filter_upwards [he, isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)] with t hg htp
  have hstar : star (scalarField M (t : ℂ)) = scalarField M (t : ℂ) := by
    rw [scalarField, ScalarFieldResponse.scalarFieldComplex_ofReal M.bjrModel t htp]
    ext x
    simp [CompactBJRModel.complexifyField_apply]
  exact ⟨(hpos _ hg hstar).1, (hpos _ hg hstar).2.1⟩

end PerronWright.FiniteIrreducibleScalarFieldResponse
