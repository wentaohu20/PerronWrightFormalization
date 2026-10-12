import PerronWright.Probability.GraphGlobalSpatialLimit
import PerronWright.Probability.CountableWindowSpatialLimit

/-! # Actual countable full vague unmarked process limits

One actual rounded positive realization gives the local-main formulas
and the unique full spatial vague probability limit. All graph bridge
premises are discharged. Under the paper's actual empirical spectral
drift, the same integer sequence gives the unnormalized global limit
at lambda+theta. The original Perron TV window profile is retained.
Identification with Brownian/Aldous is not yet asserted.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GraphGlobalSpatialLimit FactorialDensity
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague

theorem exists_actual_growing_global_spatial_limits
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
      (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ a : Fin (level N+1),
        B ≤ (N : ℝ)^(1/3 : ℝ) *
          (CountableTypeRealization.empiricalMeasure M (level N) N).real {a.val}) ∧
      (∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level lambda hlower hlo n y r -
          density (M.alpha hM) (M.beta hM) lambda y r| < ε) ∧
      (∀ lambda : ℝ, ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
        Tendsto (processLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo))
          atTop (𝓝 ν)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
          Tendsto (processLaw (M.empiricalUnnormalizedGraphLaw level lambda))
            atTop (𝓝 ν)) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, _, _, _, hTV⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_, ?_, hTV⟩
  · intro lambda
    exact exists_unique_processLaw_limit _ (M.beta_pos hM)
      (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda)
  · intro theta hθ lambda
    exact exists_unique_processLaw_limit _ (M.beta_pos hM)
      (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)

end PerronWright.CountableKernel
