import PerronWright.Probability.CountableFixedSupportTVDistanceLocal
import PerronWright.Probability.CountableFixedSupportGrowingRequirements

/-! # Actual TV-distance requirements for the same local-main diagonal

Each requirement is a statement about an actual rounded graph source.
The two families are conjoined before the positive empirical realization
is selected, so the distance and unmarked density conclusions concern
one and the same vertex assignment sequence.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

def fixedSupportTVDistanceRequirement (M : CountableKernel)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (m j N : ℕ) : Prop :=
  ∀ lambda : ℝ, |lambda| ≤ (j + 1 : ℝ) →
    ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
    (∀ i, 1 / (j + 1 : ℝ) ≤ y i) → (∀ i, y i ≤ (j + 1 : ℝ)) →
    (∀ i, r i ≤ j + 1) →
    M.fixedSupportDistanceLocalExpectation m lambda hlower hlo (N - 1) y r < 1 / (j + 1 : ℝ)

theorem fixedSupportTVDistanceRequirement_eventually (M : CountableKernel)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (m j : ℕ) : ∀ᶠ N in atTop, M.fixedSupportTVDistanceRequirement hlower hlo m j N := by
  have hp : Tendsto (fun N : ℕ ↦ N - 1) atTop atTop := tendsto_atTop.mpr (fun b ↦ by
    filter_upwards [eventually_ge_atTop (b + 1)] with N hN
    omega)
  exact hp.eventually (M.fixedSupport_eventually_uniform_parameter_distance_local_zero
    m (j + 1) (1 / (j + 1 : ℝ)) (j + 1) (j + 1) (by positivity) (by positivity)
    hlower hlo (by positivity))

theorem exists_actual_local_and_TV_requirements (M : CountableKernel)
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
      (∀ j, ∀ᶠ N in atTop,
        M.fixedSupportLocalRequirement hlower hlo (level N) j N ∧
        M.fixedSupportTVDistanceRequirement hlower hlo (level N) j N) := by
  exact CountableTypeRealization.exists_positive_empirical_realization_refined M
    (fun m j N ↦ M.fixedSupportLocalRequirement hlower hlo m j N ∧
      M.fixedSupportTVDistanceRequirement hlower hlo m j N)
    (fun m j ↦ (M.fixedSupportLocalRequirement_eventually hlower hlo m j).and
      (M.fixedSupportTVDistanceRequirement_eventually hlower hlo m j)) |>.imp fun level h ↦
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

end PerronWright.CountableKernel
