import PerronWright.Probability.CountableEmpiricalFiniteModel

/-! # One actual empirical realization for all finite-model approximations

The same positive integer-count construction gives the critical finite
models, spectral roots, quadratic/cubic scales, and embedded Perron marks.
No separate chosen convergence sequence or graph-limit premise is used.
The eventual graph-limit diagonal remains a separate obligation.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

theorem empiricalFiniteModel_alpha_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (M.empiricalFiniteModel level hpos hlower hlo n).alpha
      (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)) atTop (𝓝 (M.alpha hM)) := by
  have ht := M.finitePerronAlpha_tendsto hM _ (M.empiricalWeights_nonneg level)
    (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo herr
  simpa only [empiricalFiniteModel, M.finiteCriticalModel_alpha] using ht

theorem empiricalFiniteModel_beta_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (M.empiricalFiniteModel level hpos hlower hlo n).beta
      (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)) atTop (𝓝 (M.beta hM)) := by
  have ht := M.finitePerronBeta_tendsto hM _ (M.empiricalWeights_nonneg level)
    (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo herr
  simpa only [empiricalFiniteModel, M.finiteCriticalModel_beta] using ht

theorem empiricalFiniteModel_perronMeasure_map (M : CountableKernel) (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (n : ℕ) :
    (FiniteIrreducibleConnectedTypeLaw.perronMeasure
      (M.empiricalFiniteModel level hpos hlower hlo n)
      (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)).map
        (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ)) =
      M.empiricalPerronLaw level n hlower hlo :=
  M.finiteCriticalModel_perronMeasure_map _ _ _ _ _ (hpos n) hlower hlo _

theorem empiricalFiniteModel_perronVariation_tendsto (M : CountableKernel)
    (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑' a : ℕ, |((FiniteIrreducibleConnectedTypeLaw.perronMeasure
      (M.empiricalFiniteModel level hpos hlower hlo n)
      (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)).map
        (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ))).real {a} -
          (M.perronLaw hM).real {a}|) atTop (𝓝 0) := by
  simp_rw [M.empiricalFiniteModel_perronMeasure_map]
  exact M.finitePerronLaw_atomic_variation_tendsto hM _ (M.empiricalWeights_nonneg level)
    (M.empiricalWeights_hasSum level) _ (M.empiricalWeights_finite_support level) hlower hlo herr

/-- A single actual positive-count realization simultaneously supplies
all spectral, scale and total-variation mark approximations, together
with its exact finite-model populations. This is not a graph limit. -/
theorem exists_actual_empiricalFiniteModel_approximation (M : CountableKernel)
    (hM : M.IsRegularCritical) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      ∃ (lower : ℝ) (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
        (hpos : ∀ n a, a ∈ Finset.range (level (n + 1) + 1) →
          0 < M.empiricalWeights level n a),
        Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|) atTop (𝓝 0) ∧
        (∀ B : ℝ, ∀ᶠ n in atTop, ∀ a : Finset.range (level (n + 1) + 1),
          B ≤ ((n + 1 : ℕ) : ℝ) ^ (1/3 : ℝ) * M.empiricalWeights level n a) ∧
        Tendsto (M.empiricalSpectralRadius level) atTop (𝓝 1) ∧
        (∀ n, (M.empiricalFiniteModel level hpos hlower hlo n).IsCritical) ∧
        (∀ n a, (FiniteIrreducibleTypePlacementMultiplicity.fiberCount
          (M.empiricalVertexTypes level n) a : ℝ) =
          (n + 1 : ℕ) * (M.empiricalFiniteModel level hpos hlower hlo n).weight a) ∧
        Tendsto (fun n ↦ (M.empiricalFiniteModel level hpos hlower hlo n).alpha
          (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)) atTop (𝓝 (M.alpha hM)) ∧
        Tendsto (fun n ↦ (M.empiricalFiniteModel level hpos hlower hlo n).beta
          (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)) atTop (𝓝 (M.beta hM)) ∧
        Tendsto (fun n ↦ ∑' a : ℕ, |((FiniteIrreducibleConnectedTypeLaw.perronMeasure
          (M.empiricalFiniteModel level hpos hlower hlo n)
          (M.empiricalFiniteModel_isCritical level hpos hlower hlo n)).map
            (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ))).real {a} -
              (M.perronLaw hM).real {a}|) atTop (𝓝 0) := by
  obtain ⟨level, hm, ht, _, hcounts, _, herr, hmin⟩ :=
    CountableTypeRealization.exists_positive_empirical_realization M
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  have hpos := M.empiricalWeights_pos_of_counts level hcounts
  have he : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, empiricalWeights] using
      herr.comp (tendsto_add_atTop_nat 1)
  refine ⟨level, hm, ht, lower, hlower, hlo, hpos, he, ?_,
    M.weightedSpectralRadius_tendsto_one hM.1 _ (M.empiricalWeights_nonneg level)
      (M.empiricalWeights_hasSum level) he,
    M.empiricalFiniteModel_isCritical level hpos hlower hlo, ?_,
    M.empiricalFiniteModel_alpha_tendsto hM level hpos hlower hlo he,
    M.empiricalFiniteModel_beta_tendsto hM level hpos hlower hlo he,
    M.empiricalFiniteModel_perronVariation_tendsto hM level hpos hlower hlo he⟩
  · intro B
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (hmin B)] with n hn
    intro a
    exact hn ⟨a, Finset.mem_range.mp a.property⟩
  · intro n a
    exact M.empiricalVertexTypes_exact_weights level n a

end PerronWright.CountableKernel
