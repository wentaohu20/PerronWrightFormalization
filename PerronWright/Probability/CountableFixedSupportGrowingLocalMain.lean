import PerronWright.Probability.CountableFixedSupportGrowingRequirements
import PerronWright.Probability.CountableFixedSupportGrowingSource
import PerronWright.Probability.CountableFixedSupportReferenceUniform

/-! # One actual growing realization with the countable local-main density

The same literal rounded positive count vectors and vertex assignments
satisfy all local errors. The countable diagonal controls every tuple
order, bounded surplus, positive size box and bounded scalar interval.
Its target is the original countable Perron density. No graph-limit or
spectral-drift conclusion is assumed; marked process convergence is not
asserted in this unmarked local theorem.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

/-- Zeroth order is exactly one for the genuine graph probability law,
including every small graph size, so it needs no asymptotic estimate. -/
theorem growingLocalExpectation_zero_order (M : CountableKernel) (level : ℕ → ℕ)
    (lambda alpha beta : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (y : Fin 0 → ℝ) (r : Fin 0 → ℕ) :
    M.growingLocalExpectation level lambda hlower hlo n y r =
      FactorialDensity.density alpha beta lambda y r := by
  have hc (G : SimpleGraph (Fin (n + 1))) (k : Fin 0 → ℕ) :
      ComponentCounts.count G k r = 1 := by
    rw [ComponentCounts.count_eq_sum_blocks]
    simp
  unfold growingLocalExpectation
  simp_rw [hc]
  simp [FactorialDensity.density, FactorialDensity.criticalExponent]

private theorem exists_local_window_index (q R : ℕ) (a b L ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ j : ℕ, q ≤ j + 1 ∧ R ≤ j + 1 ∧ L ≤ (j + 1 : ℝ) ∧ b ≤ (j + 1 : ℝ) ∧
      1 / (j + 1 : ℝ) ≤ a ∧ 1 / (j + 1 : ℝ) < ε / 2 := by
  have ht : Tendsto (fun j : ℕ ↦ (j + 1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := ht.inv_tendsto_atTop
  have hε2 : 0 < ε / 2 := by positivity
  have he : ∀ᶠ j : ℕ in atTop,
      q ≤ j + 1 ∧ R ≤ j + 1 ∧ L ≤ (j + 1 : ℝ) ∧ b ≤ (j + 1 : ℝ) ∧
        1 / (j + 1 : ℝ) ≤ a ∧ 1 / (j + 1 : ℝ) < ε / 2 := by
    filter_upwards [eventually_ge_atTop q, eventually_ge_atTop R,
      ht.eventually_ge_atTop L, ht.eventually_ge_atTop b,
      hinv.eventually (Iio_mem_nhds ha), hinv.eventually (Iio_mem_nhds hε2)]
      with j hq hR hL hb hja hje
    exact ⟨by omega, by omega, hL, hb, (by simpa only [one_div, Pi.inv_apply] using hja.le),
      (by simpa only [one_div, Pi.inv_apply] using hje)⟩
  exact he.exists

/-- Decoding the proved local requirements gives the actual growing-source
local formula, including uniformity on a bounded scalar interval. This
lemma is used below with the genuinely constructed refined realization. -/
theorem growing_local_main_of_actual_requirements
    (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (level : ℕ → ℕ) (ht : Tendsto level atTop atTop)
    (hdiag : ∀ j, ∀ᶠ N in atTop, M.fixedSupportLocalRequirement hlower hlo (level N) j N)
    (q R : ℕ) (hq : 0 < q) (a b L : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |M.growingLocalExpectation level lambda hlower hlo n y r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  obtain ⟨j, hqj, hRj, hLj, hbj, haj, hej⟩ := exists_local_window_index q R a b L ε ha hε
  have hd := M.fixedSupport_eventually_uniform_reference_density
    hM q R a b L ha hlower hlo (show 0 < ε / 2 by positivity)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hdiag j),
    (ht.comp (tendsto_add_atTop_nat 1)).eventually hd]
    with n hn hdn lambda hl y r hya hyb hr
  have he1 := hn (⟨q, Nat.lt_succ_of_le hqj⟩ : Fin (j + 2)) hq lambda (hl.trans hLj) y r
    (fun i ↦ haj.trans (hya i)) (fun i ↦ (hyb i).trans hbj)
    (fun i ↦ (hr i).trans hRj)
  simp only [Nat.add_sub_cancel] at he1
  rw [← M.growingLocalExpectation_eq_fixedSupport level lambda hlower hlo n y r] at he1
  have he2 := hdn lambda hl y r hya hyb hr
  change |M.fixedSupportReferenceDensity (level (n + 1)) lambda hlower hlo y r -
    FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε / 2 at he2
  exact (abs_sub_le (M.growingLocalExpectation level lambda hlower hlo n y r)
    (M.fixedSupportReferenceDensity (level (n + 1)) lambda hlower hlo y r)
    (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r)).trans_lt
      (by linarith)

/-- One single actual positive integer realization has all the countable
unmarked local-main formulas, simultaneously in every fixed order/window
and uniformly on every bounded parameter interval. The empirical law and
population minimum properties hold for these very same vertex types. -/
theorem exists_actual_growing_local_main
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
          FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, _, hdiag⟩ :=
    CountableTypeRealization.exists_positive_empirical_realization_refined M
      (M.fixedSupportLocalRequirement hlower hlo)
      (M.fixedSupportLocalRequirement_eventually hlower hlo)
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, ?_⟩
  intro q R a b L ha ε hε
  by_cases hq : 0 < q
  · exact M.growing_local_main_of_actual_requirements hM hlower hlo level ht hdiag
      q R hq a b L ha hε
  · have hq0 : q = 0 := by omega
    subst q
    exact Eventually.of_forall (fun n lambda _ y r _ _ _ ↦ by
      rw [M.growingLocalExpectation_zero_order level lambda (M.alpha hM) (M.beta hM)
        hlower hlo n y r, sub_self, abs_zero]
      exact hε)

end PerronWright.CountableKernel
