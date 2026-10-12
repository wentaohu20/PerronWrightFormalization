import PerronWright.Probability.CountableGrowingTVDistance
import PerronWright.Probability.CountableFixedSupportGrowingTerminal

/-! # One actual realization with local-main and TV-profile collapse

All the population and local-density conclusions hold for the very same
literal rounded assignments as the empirical mark-distance conclusions.
The TV observable is bounded and explicitly defined; no boundedness of
arbitrary continuous tests on the growing mark space is asserted.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

theorem exists_actual_growing_local_main_and_TV_profile
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
          (CountablePerronMarkConvergence.perronMark M hM) < ε) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hdiag⟩ :=
    M.exists_actual_local_and_TV_requirements hlower hlo
  have hlocal := fun j ↦ (hdiag j).mono (fun _ h ↦ h.1)
  have hTV := fun j ↦ (hdiag j).mono (fun _ h ↦ h.2)
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, ?_, ?_⟩
  · intro q R a b L ha ε hε
    by_cases hq : 0 < q
    · exact M.growing_local_main_of_actual_requirements hM hlower hlo level ht hlocal
        q R hq a b L ha hε
    · have hq0 : q = 0 := by omega
      subst q
      exact Eventually.of_forall (fun n lambda _ y r _ _ _ ↦ by
        rw [M.growingLocalExpectation_zero_order level lambda (M.alpha hM) (M.beta hM)
          hlower hlo n y r, sub_self, abs_zero]
        exact hε)
  · intro R a b L ha ε hε
    exact M.growing_perron_distance_zero_of_actual_requirements hM hlower hlo
      level ht hlocal hTV R a b L ha hε

end PerronWright.CountableKernel
