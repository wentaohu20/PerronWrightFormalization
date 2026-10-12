import PerronWright.Probability.CountableFixedSupportGrowingTerminal
import PerronWright.Probability.CountableEmpiricalSpectralDrift

/-! # Actual unnormalized countable local-main with the paper's spectral drift

The normalized local estimate is already proved uniformly in bounded
parameters for one actual growing realization. The entire unnormalized
graph law is its exact effective-parameter law; the stated critical-scale
spectral drift and the explicit density's compact uniform continuity give
the literal lambda+theta local formula for that same realization.
No graph convergence or marked process identification is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

def growingUnnormalizedLocalExpectation (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    ∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n + 1)) r : ℝ)
      ∂M.empiricalUnnormalizedGraphLaw level lambda n

theorem growingUnnormalizedLocalExpectation_eq_effective_normalized
    (M : CountableKernel) (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) :
    M.growingUnnormalizedLocalExpectation level lambda n y r =
      M.growingLocalExpectation level (M.empiricalEffectiveParameter level lambda n)
        hlower hlo n y r := by
  unfold growingUnnormalizedLocalExpectation growingLocalExpectation
  rw [M.empiricalUnnormalizedGraphLaw_eq_effective_normalized level lambda hlower hlo n]

/-- Composition with a proved uniform local estimate. The terminal below
discharges this estimate using the actual growing realization theorem. -/
theorem growing_unnormalized_local_of_uniform_normalized
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level ell hlower hlo n y r -
          FactorialDensity.density (M.alpha hM) (M.beta hM) ell y r| < ε)
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius level n - 1)) atTop (𝓝 theta))
    (lambda : ℝ) (q R : ℕ) (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingUnnormalizedLocalExpectation level lambda n y r -
          FactorialDensity.density (M.alpha hM) (M.beta hM) (lambda + theta) y r| < ε := by
  let ell := M.empiricalEffectiveParameter level lambda
  have hl : Tendsto ell atTop (𝓝 (lambda + theta)) :=
    M.empiricalEffectiveParameter_tendsto level lambda theta hθ
  have hbnd : ∀ᶠ n in atTop, |ell n| ≤ |lambda + theta| + 1 := by
    filter_upwards [hl.eventually (Icc_mem_nhds
      (a := lambda + theta - 1) (b := lambda + theta + 1)
      (by linarith) (by linarith))] with n hn
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (lambda + theta)
      linarith [hn.1]
    · have h := le_abs_self (lambda + theta)
      linarith [hn.2]
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [hbnd, hlocal q R a b (|lambda + theta| + 1) ha (ε / 2) hhalf,
    FiniteIrreducibleVaryingDensity.eventually_uniform_parameter_density
      (M.alpha hM) (M.beta hM) ell (lambda + theta) hl q R a b ha hhalf,
    M.growing_eventually_uniform_raw_hazards level |lambda|] with n hn he hd ht
  refine ⟨(ht lambda le_rfl).1, ?_⟩
  intro y r hya hyb hr
  rw [M.growingUnnormalizedLocalExpectation_eq_effective_normalized
    level lambda hlower hlo n y r]
  have he' := he (ell n) hn y r hya hyb hr
  have hd' := hd y r hya hyb hr
  exact (abs_sub_le
    (M.growingLocalExpectation level (ell n) hlower hlo n y r)
    (FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n) y r)
    (FactorialDensity.density (M.alpha hM) (M.beta hM) (lambda + theta) y r)).trans_lt
      (by linarith)

/-- A single actual growing positive integer realization also satisfies
the unnormalized local-main conclusion whenever its actual empirical
spectral roots satisfy the paper's stated critical-scale drift. -/
theorem exists_actual_growing_unnormalized_local_main
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
        ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
        ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        |M.growingLocalExpectation level ell hlower hlo n y r -
          FactorialDensity.density (M.alpha hM) (M.beta hM) ell y r| < ε) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
          (M.empiricalSpectralRadius level n - 1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∀ q R : ℕ, ∀ a b : ℝ, 0 < a → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop,
          0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
          ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
          (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
          |M.growingUnnormalizedLocalExpectation level lambda n y r -
            FactorialDensity.density (M.alpha hM) (M.beta hM) (lambda + theta) y r| < ε) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal⟩ :=
    M.exists_actual_growing_local_main hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_⟩
  intro theta hθ lambda q R a b ha ε hε
  exact M.growing_unnormalized_local_of_uniform_normalized hM level hlower hlo hlocal
    theta hθ lambda q R a b ha hε

end PerronWright.CountableKernel
