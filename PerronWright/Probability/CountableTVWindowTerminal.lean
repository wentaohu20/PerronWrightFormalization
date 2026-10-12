import PerronWright.Probability.CountableTVWindowExpectation
import PerronWright.Probability.CountableTVWindowLawProfile

/-! # One genuine growing local-main source with localized TV profiles

The realization is selected from the proved conjoined requirements.
All local factorial formulas and the whole-window empirical-TV profile
control consequently hold for the same literal counts and assignments.
The last event is intrinsic to the actual weak-Borel marked window law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.CountableKernel

open CountableVariationMarks CountableTVWindowProfile CountableComponentWindowLaw
open FinitePointMeasureCompact

def growingWindowBadProbability (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R : ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) (p : VariationMark) (δ : ℝ) : ℝ :=
  (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n :
    Measure (PointMeasure (MarkedWindow a b R))).real
      {η | 0 < count η (badMarkCell a b R p δ)}

theorem growing_windowBadProbability_zero_of_local_distance
    (M : CountableKernel) (level : ℕ → ℕ) (p : VariationMark)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r p < ε)
    (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (δ : ℝ) (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      M.growingWindowBadProbability level lambda a b R hlower hlo n p δ < ε := by
  filter_upwards [M.growing_windowDistance_zero_of_local_distance level p hlower hlo hTV
    a b L ha hab R (mul_pos hε hδ)] with n hn lambda hl
  have hb := M.empiricalMarkedWindowLaw_badProbability_le level lambda a b R hlower hlo n p δ hδ
  change M.growingWindowBadProbability level lambda a b R hlower hlo n p δ ≤
    M.growingWindowDistanceExpectation level lambda a b R hlower hlo n p / δ at hb
  exact hb.trans_lt ((div_lt_iff₀ hδ).mpr (hn lambda hl))

theorem growing_windowDistance_tendsto_zero_of_local_distance
    (M : CountableKernel) (level : ℕ → ℕ) (p : VariationMark)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r p < ε)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n p)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [M.growing_windowDistance_zero_of_local_distance level p hlower hlo hTV
    a b |lambda| ha hab R hε] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hn lambda le_rfl
  · exact integral_nonneg (fun G ↦ windowDistance_nonneg _ G a b R p)

theorem growing_windowBadProbability_tendsto_zero_of_local_distance
    (M : CountableKernel) (level : ℕ → ℕ) (p : VariationMark)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
      ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      M.growingDistanceLocalExpectation level lambda hlower hlo n y r p < ε)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [M.growing_windowBadProbability_zero_of_local_distance level p hlower hlo hTV
    a b |lambda| ha hab R δ hδ hε] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show
    0 ≤ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ from measureReal_nonneg)]
  exact hn lambda le_rfl

theorem exists_actual_growing_local_main_and_window_TV_profile
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
      (∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
        ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
        (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
        M.growingDistanceLocalExpectation level lambda hlower hlo n y r
          (CountablePerronMarkConvergence.perronMark M hM) < ε) ∧
      (∀ R : ℕ, ∀ a b L : ℝ, 0 < a → a ≤ b → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
        M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) < ε) ∧
      (∀ R : ℕ, ∀ a b L : ℝ, 0 < a → a ≤ b → ∀ δ > 0, ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
        M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ < ε) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, hTV⟩ :=
    M.exists_actual_growing_local_main_and_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, hTV, ?_, ?_, ?_⟩
  · intro R a b L ha hab ε hε
    exact M.growing_windowDistance_zero_of_local_distance level
      (CountablePerronMarkConvergence.perronMark M hM) hlower hlo hTV a b L ha hab R hε
  · intro R a b L ha hab δ hδ ε hε
    exact M.growing_windowBadProbability_zero_of_local_distance level
      (CountablePerronMarkConvergence.perronMark M hM) hlower hlo hTV a b L ha hab R δ hδ hε
  · intro lambda a b ha hab R
    refine ⟨M.growing_windowDistance_tendsto_zero_of_local_distance level
      (CountablePerronMarkConvergence.perronMark M hM) hlower hlo hTV lambda a b ha hab R, ?_⟩
    intro δ hδ
    exact M.growing_windowBadProbability_tendsto_zero_of_local_distance level
      (CountablePerronMarkConvergence.perronMark M hM) hlower hlo hTV lambda a b ha hab R δ hδ

end PerronWright.CountableKernel
