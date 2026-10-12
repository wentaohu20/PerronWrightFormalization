import PerronWright.Probability.GraphGlobalSizeRescaling
import PerronWright.Probability.CountableGlobalAndMarkedWindowLimit

/-! # Literal starred global graph laws for an actual countable realization

The size multiplier is the original countable beta^(1/3), not the
empirical finite-support scale. These are literal finite graph Dirac
laws. Their full vague limits follow from proved original-parameter
local estimates, with the same actual spectral-drift shift for the raw
source. The model terminal discharges those estimates, without a
Brownian identity assumption.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableStarredGlobalSizeRescaling

open CountableKernel FactorialDensity GraphGlobalSizeRescaling
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague

def sizeScale (M : CountableKernel) (hM : M.IsRegularCritical) : ℝ :=
  (M.beta hM)^(1/3 : ℝ)

theorem sizeScale_pos (M : CountableKernel) (hM : M.IsRegularCritical) : 0 < sizeScale M hM :=
  Real.rpow_pos_of_pos (M.beta_pos hM) _

def normalizedStarredProcessLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda : ℝ) : ℕ → ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  scaledProcessLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) (sizeScale_pos M hM)

def unnormalizedStarredProcessLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda : ℝ) :
    ℕ → ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  scaledProcessLaw (M.empiricalUnnormalizedGraphLaw level lambda) (sizeScale_pos M hM)

variable (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
variable {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
variable (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
  ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
    ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
    (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
    |M.growingLocalExpectation level lambda hlower hlo n y r -
      density (M.alpha hM) (M.beta hM) lambda y r| < ε)

include hlocal

theorem normalized_limit_of_actual_estimates (lambda : ℝ) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (normalizedStarredProcessLaw M hM level hlower hlo lambda) atTop (𝓝 ν) :=
  exists_unique_scaledProcessLaw_limit _ (M.beta_pos hM)
    (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda) (sizeScale_pos M hM)

theorem unnormalized_limit_of_actual_estimates (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta)) (lambda : ℝ) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (unnormalizedStarredProcessLaw M hM level lambda) atTop (𝓝 ν) :=
  exists_unique_scaledProcessLaw_limit _ (M.beta_pos hM)
    (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)
    (sizeScale_pos M hM)

omit level hlocal in
theorem exists_actual_growing_starred_global_limits :
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
        Tendsto (normalizedStarredProcessLaw M hM level hlower hlo lambda) atTop (𝓝 ν)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
          Tendsto (unnormalizedStarredProcessLaw M hM level lambda) atTop (𝓝 ν)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, _, _, _, _⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_, ?_⟩
  · intro lambda
    exact normalized_limit_of_actual_estimates M hM level hlower hlo hlocal lambda
  · intro theta hθ lambda
    exact unnormalized_limit_of_actual_estimates M hM level hlower hlo hlocal theta hθ lambda

end PerronWright.CountableStarredGlobalSizeRescaling
