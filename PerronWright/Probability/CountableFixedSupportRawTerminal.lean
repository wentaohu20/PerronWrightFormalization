import PerronWright.Probability.CountableFixedSupportTVLocal

/-! # Literal raw-time fixed-truncation local terminals

The actual empirical-normalized graph source agrees eventually with
the paper's unclipped critical time. Both floor terminals below concern
that genuine source and the literal natural-number vertex assignment.
They do not assert growing-support point-process convergence.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

theorem fixedSupport_eventually_raw_hazards (M : CountableKernel) (m : ℕ) (lambda : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ e : AnnealedGraph.Edge (n + 1),
        M.empiricalNormalizedHazards (fun _ ↦ m) lambda n e =
          (1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) *
            M.retainedPairKernel (CountableTypeRealization.vertexTypes M m (n + 1)) e.val /
              (((n + 1 : ℕ) : ℝ) * M.empiricalSpectralRadius (fun _ ↦ m) n) := by
  have hp := (CriticalScaling.raw_time_tendsto lambda).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hp,
    (tendsto_add_atTop_nat 1).eventually (CriticalScaling.time_eq_raw_eventually lambda)]
    with n hn he
  refine ⟨hn, fun e ↦ ?_⟩
  rw [empiricalNormalizedHazards, he]

theorem fixedSupport_eventually_uniform_paper_floor_TV_marked_factorial_density
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, CountableVariationComponentCounts.markedCount
            (CountableTypeRealization.vertexTypes M m (n + 1)) G
            (fun i ↦ ⌊y i * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)⌋₊) r Ψ
            ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) -
        FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r * Ψ (fun _ ↦ M.fixedSupportPerronMark m hlower hlo)| < ε := by
  filter_upwards [M.fixedSupport_eventually_raw_hazards m lambda,
    M.fixedSupport_eventually_uniform_TV_marked_factorial_density
      m q R hq lambda a b ha hb hlower hlo Ψ hΨ hε] with n hp hn
  exact ⟨hp.1, by simpa only [CriticalScaling.size] using hn⟩

theorem fixedSupport_eventually_uniform_paper_floor_factorial_density
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + lambda * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, (ComponentCounts.count G
            (fun i ↦ ⌊y i * ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ)⌋₊) r : ℝ)
            ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) -
        FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r| < ε := by
  filter_upwards [M.fixedSupport_eventually_raw_hazards m lambda,
    M.fixedSupport_eventually_uniform_factorial_density
      m q R hq lambda a b ha hb hlower hlo hε] with n hp hn
  exact ⟨hp.1, by simpa only [CriticalScaling.size] using hn⟩

end PerronWright.CountableKernel
