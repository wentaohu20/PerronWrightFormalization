import PerronWright.Probability.CountableTVWindowConvergence
import PerronWright.Probability.CountableWindowCountLimit

/-! # One actual local-main realization with marked-window weak transfer

Every numeric local and TV-profile premise is discharged by the same
actual positive rounded realization. Its empirical marked window laws
have the constant-Perron bounded-test transfer and true joint weak
subsequences. No spatial-limit uniqueness or Brownian identification is
deduced merely from the already known component-number convergence.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1600000

namespace PerronWright.CountableKernel

open CountableComponentWindowLaw CountableTVWindowProfile CountableTVWindowConvergence
open FinitePointMeasureCompact GraphWindowSource

theorem exists_actual_growing_local_main_and_marked_window_transfer
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
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level lambda hlower hlo n y r -
          FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        (∀ F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ,
          Tendsto (fun n ↦
            (∫ η, F η ∂(M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n : Measure _)) -
              (∫ η, F η ∂(canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R
                (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n) : Measure _)))
            atTop (𝓝 0)) ∧
        (∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) ∧
        (∀ I : ℕ → ℕ, Tendsto I atTop atTop →
          ∃ μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)), ∃ N : ℕ → ℕ, StrictMono N ∧
            Tendsto (fun n ↦ windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
              a b R (I (N n))) atTop (𝓝 μ) ∧
            Tendsto (fun n ↦ M.empiricalMarkedWindowLaw level lambda a b R hlower hlo (I (N n))) atTop
              (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ)))) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, _, _, _, hTV⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_⟩
  intro lambda a b ha hab R
  have hl := M.growing_uniform_local_limit hM level hlower hlo hlocal lambda
  have hbad := (hTV lambda a b ha hab R).2
  refine ⟨?_, hbad, ?_⟩
  · intro F
    exact means_difference_tendsto_zero M hM level lambda a b ha hab R hlower hlo hl
      (CountablePerronMarkConvergence.perronMark M hM) hbad F
  · intro I hI
    exact exists_reindexed_actual_unmarked_and_marked_window_subseq M hM level lambda a b ha hab R
      hlower hlo hl (CountablePerronMarkConvergence.perronMark M hM) hbad I hI

end PerronWright.CountableKernel
