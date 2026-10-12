import PerronWright.Kernel.CountableApproximationOperator

/-!
# Square-root density features of actual atomic probability weights

Nonnegative weights summing to one give the actual common-space feature
`sqrt(w(a)/μ({a}))`.  Atomic absolute `ℓ¹` convergence implies `L²(μ)`
convergence of these features, via a proved square-root inequality.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem integral_eq_tsum_atom (M : CountableKernel) (f : ℕ → ℝ) :
    (∫ a, f a ∂M.mu) = ∑' a, M.mu.real {a} * f a := by
  have h := integral_sum_dirac (f := f) (x := fun a : ℕ ↦ a)
    (c := fun a ↦ M.mu {a}) (fun a ↦ measure_ne_top M.mu {a})
  rw [M.mu.sum_smul_dirac] at h
  simpa [measureReal_def, smul_eq_mul] using h

theorem integrable_of_summable_atomNorm (M : CountableKernel) (f : ℕ → ℝ)
    (hs : Summable (fun a ↦ M.mu.real {a} * ‖f a‖)) : Integrable f M.mu := by
  have h := integrable_sum_dirac (f := f) (x := fun a : ℕ ↦ a)
    (c := fun a ↦ M.mu {a}) (fun a ↦ measure_ne_top M.mu {a}) hs
  rwa [M.mu.sum_smul_dirac] at h

def weightFeatureFunction (M : CountableKernel) (w : ℕ → ℝ) (a : ℕ) : ℝ :=
  Real.sqrt (w a / M.mu.real {a})

theorem weightFeatureFunction_square (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (a : ℕ) :
    M.mu.real {a} * (M.weightFeatureFunction w a) ^ 2 = w a := by
  rw [weightFeatureFunction, Real.sq_sqrt (div_nonneg (hw a) (M.atomMass_pos a).le)]
  exact mul_div_cancel₀ _ (M.atomMass_pos a).ne'

theorem weightFeatureFunction_memLp (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) : MemLp (M.weightFeatureFunction w) 2 M.mu := by
  apply (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).mpr
  apply M.integrable_of_summable_atomNorm
  convert hs.summable using 1
  ext a
  rw [Real.norm_of_nonneg (sq_nonneg _), M.weightFeatureFunction_square w hw a]

def weightFeature (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) : M.L2 :=
  (M.weightFeatureFunction_memLp w hw hs).toLp (M.weightFeatureFunction w)

theorem weightFeature_apply (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (a : ℕ) :
    M.weightFeature w hw hs a = M.weightFeatureFunction w a :=
  M.forall_of_ae (M.weightFeatureFunction_memLp w hw hs).coeFn_toLp a

theorem norm_weightFeature (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) : ‖M.weightFeature w hw hs‖ = 1 := by
  have hn : ‖M.weightFeature w hw hs‖ ^ 2 = 1 := by
    rw [M.norm_sq_eq_integral, M.integral_eq_tsum_atom]
    simp_rw [M.weightFeature_apply, M.weightFeatureFunction_square w hw]
    exact hs.tsum_eq
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hn)

def baseFeature (M : CountableKernel) : M.L2 :=
  M.weightFeature (fun a ↦ M.mu.real {a}) (fun a ↦ (M.atomMass_pos a).le) M.atomMass_hasSum

theorem baseFeature_apply (M : CountableKernel) (a : ℕ) : M.baseFeature a = 1 := by
  rw [baseFeature, M.weightFeature_apply, weightFeatureFunction,
    div_self (M.atomMass_pos a).ne', Real.sqrt_one]

theorem weightedActionCLM_baseFeature (M : CountableKernel) :
    M.weightedActionCLM M.baseFeature = M.actionCLM := by
  have hrow : ∀ a, M.featureRow M.baseFeature a = M.row a := by
    intro a
    apply Lp.ext
    filter_upwards [M.row_coe_ae a] with b hb
    rw [M.featureRow_apply, M.baseFeature_apply, mul_one, hb]
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [M.action_coe_ae v] with a ha
  change M.featureActionCLM M.baseFeature M.baseFeature v a = M.action v a
  rw [M.featureActionCLM_apply, M.baseFeature_apply, one_mul, hrow a, ha]
  rfl

theorem sqrt_sub_sq_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
  have hx2 := Real.sq_sqrt hx
  have hy2 := Real.sq_sqrt hy
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hp : 0 ≤ (Real.sqrt y - Real.sqrt x) * Real.sqrt x :=
      mul_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hxy)) (Real.sqrt_nonneg _)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hp : 0 ≤ (Real.sqrt x - Real.sqrt y) * Real.sqrt y :=
      mul_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hyx)) (Real.sqrt_nonneg _)
    nlinarith

theorem weightFeatureFunction_sub_one_sq_le (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (a : ℕ) :
    M.mu.real {a} * (M.weightFeatureFunction w a - 1) ^ 2 ≤ |w a - M.mu.real {a}| := by
  have hm := M.atomMass_pos a
  have hs : 0 < Real.sqrt (M.mu.real {a}) := Real.sqrt_pos.mpr hm
  have he : M.mu.real {a} * (M.weightFeatureFunction w a - 1) ^ 2 =
      (Real.sqrt (w a) - Real.sqrt (M.mu.real {a})) ^ 2 := by
    rw [weightFeatureFunction, Real.sqrt_div (hw a)]
    have hm2 := Real.sq_sqrt hm.le
    field_simp
    nlinarith
  rw [he]
  exact sqrt_sub_sq_le_abs_sub (hw a) hm.le

theorem norm_weightFeature_sub_baseFeature_sq_le (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) :
    ‖M.weightFeature w hw hs - M.baseFeature‖ ^ 2 ≤ ∑' a, |w a - M.mu.real {a}| := by
  have habs : Summable (fun a ↦ |w a - M.mu.real {a}|) :=
    (hs.summable.sub M.atomMass_hasSum.summable).abs
  have hterms : Summable (fun a ↦ M.mu.real {a} * (M.weightFeatureFunction w a - 1) ^ 2) :=
    habs.of_nonneg_of_le (fun a ↦ mul_nonneg (M.atomMass_pos a).le (sq_nonneg _))
      (M.weightFeatureFunction_sub_one_sq_le w hw)
  rw [M.norm_sq_eq_integral, M.integral_eq_tsum_atom]
  simp_rw [M.coe_sub_at, M.weightFeature_apply, M.baseFeature_apply]
  exact hterms.tsum_le_tsum (M.weightFeatureFunction_sub_one_sq_le w hw) habs

theorem weightFeature_tendsto (M : CountableKernel) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Filter.Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ M.weightFeature (w n) (hw n) (hs n)) Filter.atTop (nhds M.baseFeature) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsquare : Filter.Tendsto (fun n ↦ ‖M.weightFeature (w n) (hw n) (hs n) - M.baseFeature‖ ^ 2)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n ↦ sq_nonneg _) (fun n ↦ M.norm_weightFeature_sub_baseFeature_sq_le _ _ _) herr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

theorem weighted_probability_operator_tendsto (M : CountableKernel) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Filter.Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ M.weightedActionCLM (M.weightFeature (w n) (hw n) (hs n)))
      Filter.atTop (nhds M.actionCLM) := by
  simpa only [M.weightedActionCLM_baseFeature] using
    M.weightedActionCLM_tendsto _ _ (M.weightFeature_tendsto w hw hs herr)

end PerronWright.CountableKernel
