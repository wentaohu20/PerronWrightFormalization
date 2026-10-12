import PerronWright.Probability.GraphWindowFactorialLimits
import PerronWright.Probability.CountableUnnormalizedLocalTerminal
import PerronWright.Probability.CountableTVWindowTerminal

/-! # Actual growing countable window count limits

One literal positive integer realization gives the normalized window
component-number law and tightness of its actual point-measure laws.
The same realization also gives the unnormalized conclusions at exactly
lambda+theta under the paper's actual empirical spectral drift. All local
formula premises are discharged by the proved growing-realization theorem.
Full spatial process convergence and Brownian identification are not
asserted from the component-number limit alone.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GraphWindowSource GraphWindowFactorialLimits FactorialDensity
open FactorialCountDeterminacy ComponentWindowPointMeasures FinitePointMeasureCompact

theorem growing_uniform_local_limit (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level ell hlower hlo n y r -
          density (M.alpha hM) (M.beta hM) ell y r| < ε) (lambda : ℝ) :
    HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda := by
  intro q R _ a b ha _ ε hε
  filter_upwards [hlocal q R a b |lambda| ha ε hε] with n hn
  exact hn lambda le_rfl

theorem growing_unnormalized_uniform_local_limit
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level ell hlower hlo n y r -
          density (M.alpha hM) (M.beta hM) ell y r| < ε)
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta)) (lambda : ℝ) :
    HasUniformLocalLimit (M.empiricalUnnormalizedGraphLaw level lambda)
      (M.alpha hM) (M.beta hM) (lambda+theta) := by
  intro q R _ a b ha _ ε hε
  filter_upwards [M.growing_unnormalized_local_of_uniform_normalized hM level hlower hlo
    hlocal theta hθ lambda q R a b ha hε] with n hn
  exact hn.2

/-- Genuine component-number weak limits and actual compact-window
point-law tightness, for the same positive countable realization and both
normalizations. No density, tightness or convergence conclusion is an
additional hypothesis of this actual model terminal. -/
theorem exists_actual_growing_window_count_limits
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
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        (∃! ν : ProbabilityMeasure (Fin 1 → ℕ),
          (∀ q, Integrable (factorialPolynomial q) (ν : Measure (Fin 1 → ℕ))) ∧
          (∀ q, factorialMoment (ν : Measure (Fin 1 → ℕ)) q =
            windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R) ∧
          Tendsto (actualCountLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)
            atTop (𝓝 ν)) ∧
        IsTightMeasureSet (Set.range (fun n ↦
          (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n :
            Measure (PointMeasure (SurplusWindow a b R))))) ∧
        IsCompact (closure (Set.range
          (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)))) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          (∃! ν : ProbabilityMeasure (Fin 1 → ℕ),
            (∀ q, Integrable (factorialPolynomial q) (ν : Measure (Fin 1 → ℕ))) ∧
            (∀ q, factorialMoment (ν : Measure (Fin 1 → ℕ)) q =
              windowMass (q 0) (M.alpha hM) (M.beta hM) (lambda+theta) a b R) ∧
            Tendsto (actualCountLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R)
              atTop (𝓝 ν)) ∧
          IsTightMeasureSet (Set.range (fun n ↦
            (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R n :
              Measure (PointMeasure (SurplusWindow a b R))))) ∧
          IsCompact (closure (Set.range
            (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R)))) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, _, _, _, hTV⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, ?_, ?_, hTV⟩
  · intro lambda a b ha hab R
    have hl := M.growing_uniform_local_limit hM level hlower hlo hlocal lambda
    exact ⟨exists_unique_actualCountLaw_limit _ (M.beta_pos hM) hl ha hab R,
      isTight_windowLaws _ (M.beta_pos hM) hl ha hab R,
      isCompact_closure_windowLaws _ (M.beta_pos hM) hl ha hab R⟩
  · intro theta hθ lambda a b ha hab R
    have hl := M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda
    exact ⟨exists_unique_actualCountLaw_limit _ (M.beta_pos hM) hl ha hab R,
      isTight_windowLaws _ (M.beta_pos hM) hl ha hab R,
      isCompact_closure_windowLaws _ (M.beta_pos hM) hl ha hab R⟩

end PerronWright.CountableKernel
