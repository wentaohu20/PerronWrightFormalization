import PerronWright.Probability.CountableFixedSupportGrowingLocalMain

/-! # Literal raw-time/floor countable local-main on one actual realization

The clipped all-size convention equals the paper's raw time uniformly
on each bounded parameter interval. The terminal below expands the
actual graph factorial integral and literal floors while retaining the
same positive count realization and original countable Perron density.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

theorem growing_eventually_uniform_raw_hazards (M : CountableKernel)
    (level : ℕ → ℕ) (L : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ e : AnnealedGraph.Edge (n + 1),
        M.empiricalNormalizedHazards level lambda n e =
          (1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) *
            M.retainedPairKernel
              (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) e.val /
              (((n + 1 : ℕ) : ℝ) * M.empiricalSpectralRadius level n) := by
  have ht : Tendsto (fun n : ℕ ↦ L * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (CriticalParameterDrift.inverseScale_tendsto_zero.comp (tendsto_add_atTop_nat 1)).const_mul L
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn lambda hl
  have hi : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hl).1 hi
  have hp : 0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
  refine ⟨hp, fun e ↦ ?_⟩
  rw [empiricalNormalizedHazards, CriticalScaling.time, max_eq_left hp.le]

/-- Actual countable local-main: one monotone exhaustive support and its
literal positive integer counts work for every factorial order, bounded
surplus and positive size window, uniformly for bounded raw parameters. -/
theorem exists_actual_growing_paper_local_main
    (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ N, level N ≤ N) ∧
      (∀ N, ∑ a, GrowingTypeCounts.truncatedCounts
        (CountableTypeRealization.weights M) (level N) N a = N) ∧
      (∀ N > 0, ∀ a, 0 < GrowingTypeCounts.truncatedCounts
        (CountableTypeRealization.weights M) (level N) N a) ∧
      (∀ N > 0, IsProbabilityMeasure (CountableTypeRealization.empiricalMeasure M (level N) N)) ∧
      Tendsto (fun N ↦ ∑' s : ℕ,
        |(CountableTypeRealization.empiricalMeasure M (level N) N).real {s} - M.mu.real {s}|)
        atTop (𝓝 0) ∧
      (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ a : Fin (level N + 1),
        B ≤ (N : ℝ) ^ (1 / 3 : ℝ) *
          (CountableTypeRealization.empiricalMeasure M (level N) N).real {a.val}) ∧
      (∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
        0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
            (∫ G, (ComponentCounts.count G
              (fun i ↦ ⌊y i * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)⌋₊) r : ℝ)
              ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n) -
          FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hmain⟩ :=
    M.exists_actual_growing_local_main hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, ?_⟩
  intro q R a b L ha ε hε
  filter_upwards [hmain q R a b L ha ε hε,
    M.growing_eventually_uniform_raw_hazards level L] with n hn ht
  intro lambda hl
  exact ⟨(ht lambda hl).1, by simpa only [growingLocalExpectation, CriticalScaling.size] using hn lambda hl⟩

end PerronWright.CountableKernel
