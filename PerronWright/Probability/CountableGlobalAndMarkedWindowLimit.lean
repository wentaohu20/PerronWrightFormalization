import PerronWright.Probability.CountableWindowMarkedLimit
import PerronWright.Probability.GraphGlobalSpatialLimit

/-! # One countable realization for global spatial and localized TV laws

A single realization is selected from the proved joint local and TV
requirements. Its already established actual marked window limits are
retained, and its genuine numerical local estimates give the full vague
unmarked law on the very same graph sequence. The two normalizations
remain on this one realization. No global vague topology for the TV
product, or Brownian identity, is asserted here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GraphWindowSource GraphWindowFactorialLimits GraphGlobalSpatialLimit
open CountableTVWindowConvergence CountableComponentWindowLaw CountableTVWindowProfile
open ComponentWindowPointMeasures FinitePointMeasureCompact FactorialDensity
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague

theorem exists_actual_growing_global_and_marked_window_limits
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
      (∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
        Tendsto (processLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo))
          atTop (𝓝 ξ)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
          Tendsto (processLaw (M.empiricalUnnormalizedGraphLaw level lambda))
            atTop (𝓝 ξ)) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        (∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
          Tendsto (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)
            atTop (𝓝 μ) ∧
          Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop
            (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ))) ∧
        (∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
          Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop (𝓝 ν))) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          (∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
            Tendsto (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R) atTop (𝓝 μ) ∧
            Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop
              (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ))) ∧
          (∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
            Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop (𝓝 ν))) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          Tendsto (fun n ↦ ∫ G, windowDistance
            (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R
            (CountablePerronMarkConvergence.perronMark M hM)
            ∂M.empiricalUnnormalizedGraphLaw level lambda n) atTop (𝓝 0) ∧
          ∀ δ > 0, Tendsto (fun n ↦ (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n :
            Measure (PointMeasure (MarkedWindow a b R))).real
              {η | 0 < count η (badMarkCell a b R (CountablePerronMarkConvergence.perronMark M hM) δ)})
            atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal,
    hmarked, hrawMarked, hTV, hrawTV⟩ :=
      M.exists_actual_growing_marked_window_limits hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal,
    ?_, ?_, hmarked, hrawMarked, hTV, hrawTV⟩
  · intro lambda
    exact exists_unique_processLaw_limit _ (M.beta_pos hM)
      (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda)
  · intro theta hθ lambda
    exact exists_unique_processLaw_limit _ (M.beta_pos hM)
      (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)

end PerronWright.CountableKernel
