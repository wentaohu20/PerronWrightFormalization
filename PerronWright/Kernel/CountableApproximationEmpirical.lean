import PerronWright.Kernel.CountableApproximationPerron
import PerronWright.Model.CountablePerronQuantitiesMoments
import PerronWright.Probability.CountableTypeRealization

/-!
# Spectral realization for the actual growing vertex-type assignments

This specializes the norm/spectral convergence to literal empirical Dirac
measures of the constructed vertex assignments.  Index `n` uses `n+1`
vertices, so every law is a probability measure.  This is analytic
infrastructure, not a random-graph limit law.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace PerronWright.CountableKernel

theorem probability_atomMass_hasSum (nu : Measure ℕ) [IsProbabilityMeasure nu] :
    HasSum (fun a : ℕ ↦ nu.real {a}) 1 := by
  have hsum : (∑' a : ℕ, nu {a}) = 1 := by
    have h := congrArg (fun nu : Measure ℕ ↦ nu Set.univ) nu.sum_smul_dirac
    simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one] using h
  have hs := ENNReal.hasSum_toReal (f := fun a : ℕ ↦ nu {a}) (by rw [hsum]; simp)
  have hr : (∑' a : ℕ, (nu {a}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a ↦ measure_ne_top nu {a}), hsum]
    simp
  simpa [measureReal_def, hr] using hs

def empiricalWeights (M : CountableKernel) (level : ℕ → ℕ) (n a : ℕ) : ℝ :=
  (CountableTypeRealization.empiricalMeasure M (level (n + 1)) (n + 1)).real {a}

theorem empiricalWeights_nonneg (M : CountableKernel) (level : ℕ → ℕ) (n a : ℕ) :
    0 ≤ M.empiricalWeights level n a := ENNReal.toReal_nonneg

theorem empiricalWeights_hasSum (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ) :
    HasSum (M.empiricalWeights level n) 1 := by
  let _ := CountableTypeRealization.empiricalMeasure_isProbability M (level (n + 1))
    (Nat.succ_pos n)
  exact probability_atomMass_hasSum _

theorem empiricalWeights_finite_support (M : CountableKernel) (level : ℕ → ℕ) (n a : ℕ)
    (ha : a ∉ Finset.range (level (n + 1) + 1)) : M.empiricalWeights level n a = 0 := by
  rw [empiricalWeights, CountableTypeRealization.empiricalMeasure_atom]
  simp only [Finset.mem_range] at ha
  exact dif_neg ha

def empiricalOperator (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ) : M.L2 →L[ℝ] M.L2 :=
  M.weightedActionCLM (M.weightFeature (M.empiricalWeights level n)
    (M.empiricalWeights_nonneg level n) (M.empiricalWeights_hasSum level n))

def empiricalSpectralRadius (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ) : ℝ :=
  M.weightedSpectralRadius (M.empiricalWeights level n)
    (M.empiricalWeights_nonneg level n) (M.empiricalWeights_hasSum level n)

theorem isCompactOperator_empiricalOperator (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ) :
    IsCompactOperator (M.empiricalOperator level n) :=
  M.isCompactOperator_weighted_probability_of_finite_support _ _ _
    (Finset.range (level (n + 1) + 1)) (M.empiricalWeights_finite_support level n)

/-- Actual empirical operators and their actual real spectral radii
converge; the only criticality assumption concerns the original operator. -/
theorem exists_empirical_spectral_realization (M : CountableKernel) (hcrit : M.IsCritical) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      Tendsto (M.empiricalOperator level) atTop (nhds M.actionCLM) ∧
      Tendsto (M.empiricalSpectralRadius level) atTop (nhds 1) := by
  obtain ⟨level, hm, ht, _, _, _, herr, _⟩ :=
    CountableTypeRealization.exists_positive_empirical_realization M
  have he : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, empiricalWeights] using herr.comp (tendsto_add_atTop_nat 1)
  exact ⟨level, hm, ht,
    M.weighted_probability_operator_tendsto _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) he,
    M.weightedSpectralRadius_tendsto_one hcrit _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) he⟩

theorem empiricalOperator_exists_nonnegative_perron (M : CountableKernel)
    (level : ℕ → ℕ) (n : ℕ) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < M.empiricalSpectralRadius level n ∧
      ∃ v : M.L2, ‖v‖ = 1 ∧ (∀ a, 0 ≤ v a) ∧
        M.empiricalOperator level n v = M.empiricalSpectralRadius level n • v :=
  M.exists_nonnegative_weighted_perron _ _ _ (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) hlower hlo

def empiricalPerronVector (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : M.L2 :=
  M.finitePerronVector (M.empiricalWeights level n) (M.empiricalWeights_nonneg level n)
    (M.empiricalWeights_hasSum level n) (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) hlower hlo

def empiricalPerronFunction (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : ℕ → ℝ :=
  M.finitePerronFunction (M.empiricalWeights level n) (M.empiricalWeights_nonneg level n)
    (M.empiricalWeights_hasSum level n) (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) hlower hlo

def empiricalPerronMoment (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (m : ℕ) : ℝ :=
  M.finitePerronMoment (M.empiricalWeights level n) (M.empiricalWeights_nonneg level n)
    (M.empiricalWeights_hasSum level n) (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) hlower hlo m

/-- A realized empirical sequence has convergent actual spectral radii,
unit Perron vectors, normalized positive kernel-law functions and every
power moment.  All empirical laws are literal vertex-assignment Dirac
measures; no spectral/Perron convergence interface is assumed. -/
theorem exists_empirical_perron_moment_realization (M : CountableKernel)
    (hM : M.IsRegularCritical) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      Tendsto (M.empiricalOperator level) atTop (nhds M.actionCLM) ∧
      Tendsto (M.empiricalSpectralRadius level) atTop (nhds 1) ∧
      ∃ (lower : ℝ) (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b),
        Tendsto (fun n ↦ M.empiricalPerronVector level n hlower hlo)
          atTop (nhds (M.unitPerronVector hM)) ∧
        (∀ a, Tendsto (fun n ↦ M.empiricalPerronFunction level n hlower hlo a)
          atTop (nhds (M.perronVector hM a))) ∧
        (∀ m, Tendsto (fun n ↦ M.empiricalPerronMoment level n hlower hlo m)
          atTop (nhds (∫ a, (M.perronVector hM a) ^ m ∂M.mu))) := by
  obtain ⟨level, hm, ht, _, _, _, herr, _⟩ :=
    CountableTypeRealization.exists_positive_empirical_realization M
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  have he : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, empiricalWeights] using herr.comp (tendsto_add_atTop_nat 1)
  refine ⟨level, hm, ht,
    M.weighted_probability_operator_tendsto _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) he,
    M.weightedSpectralRadius_tendsto_one hM.1 _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) he, lower, hlower, hlo, ?_, ?_, ?_⟩
  · exact M.finitePerronVector_tendsto hM _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo he
  · exact M.finitePerronFunction_tendsto hM _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo he
  · exact M.finitePerronMoment_tendsto hM _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo he

end PerronWright.CountableKernel
