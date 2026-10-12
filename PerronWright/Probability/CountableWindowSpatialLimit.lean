import PerronWright.Probability.GraphWindowSpatialLimit
import PerronWright.Probability.CountableWindowCountLimit

/-! # One actual growing realization with full spatial window limits

The numeric local input to the generic graph bridge is discharged by the
proved actual countable realization. The same positive integer sequence
provides all normalized spatial windows and the unnormalized windows at
lambda+theta under the literal empirical spectral drift. Its actual TV
profile conclusions are retained. No Brownian identity is asserted here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GraphWindowSource GraphWindowFactorialLimits GraphWindowSpatialLimit FactorialDensity
open ComponentWindowPointMeasures FinitePointMeasureCompact

theorem exists_actual_growing_window_spatial_limits
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
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
          Tendsto (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)
            atTop (𝓝 ν)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
            Tendsto (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R)
              atTop (𝓝 ν)) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, _, _, _, hTV⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_, ?_, hTV⟩
  · intro lambda a b ha hab R
    exact exists_unique_windowLaw_limit _ (M.beta_pos hM)
      (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda) ha hab R
  · intro theta hθ lambda a b ha hab R
    exact exists_unique_windowLaw_limit _ (M.beta_pos hM)
      (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)
      ha hab R

end PerronWright.CountableKernel
