import PerronWright.Probability.CountableFixedSupportLocalMain
import PerronWright.Probability.FiniteIrreducibleCountableMarkLocal

/-! # Actual fixed-truncation factorial integrals with countable TV marks

The marks here are the literal empirical probability measures of the
natural-number types, in the actual atomic variation metric. Their
continuous coupled tests are transported to the proved fixed finite
reference theorem. The limiting mark is identified with the literal
finite-law Perron measure, not supplied as an interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open FiniteProbabilityVariationEmbedding (embed continuous_coupled_test)

/-- The canonical retained Perron mark, embedded into the original
natural-number type space with its actual total-variation metric. -/
def fixedSupportPerronMark (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    CountableVariationMarks.VariationMark :=
  embed (fun s : Finset.range (m + 1) ↦ (s : ℕ))
    (FiniteIrreducibleConnectedTypeLaw.perronLaw (M.fixedSupportModel m hlower hlo)
      (M.fixedSupportModel_isCritical m hlower hlo))

/-- Exact identity with the genuine finite-law Perron measure. -/
theorem fixedSupportPerronMark_measure (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    (M.fixedSupportPerronMark m hlower hlo).val.toMeasure =
      M.finitePerronLaw (M.fixedSupportWeights m) (M.fixedSupportWeights_nonneg m)
        (M.fixedSupportWeights_hasSum m) (Finset.range (m + 1))
        (M.fixedSupportWeights_zero m) hlower hlo := by
  unfold fixedSupportPerronMark embed CountableVariationMarks.ofProbability
  rw [ProbabilityMeasure.toMeasure_map]
  exact M.finiteCriticalModel_perronMeasure_map _ _ _ _ _ _ hlower hlo _

/-- Actual countable empirical-TV-marked component factorial integrals,
uniformly throughout the critical size window, under the literal
empirical-spectral-normalized graph source. -/
theorem fixedSupport_eventually_uniform_TV_marked_factorial_density
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, CountableVariationComponentCounts.markedCount
            (CountableTypeRealization.vertexTypes M m (n + 1)) G
            (fun i ↦ CriticalScaling.size (y i) (n + 1)) r Ψ
            ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) -
        FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r * Ψ (fun _ ↦ M.fixedSupportPerronMark m hlower hlo)| < ε := by
  let f : Finset.range (m + 1) → ℕ := fun s ↦ s.val
  filter_upwards [M.fixedSupport_eventually_uniform_marked_factorial_density
    m q R hq lambda a b ha hb hlower hlo
    (fun ν ↦ Ψ (fun i ↦ embed f (ν i))) (continuous_coupled_test f Ψ hΨ) hε] with n hn
  intro y r hya hyb hr
  have he := hn y r hya hyb hr
  simp only [FiniteIrreducibleNativeMarkConcentration.perronMarks] at he
  change |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    (∫ G, CountableVariationComponentCounts.markedCount
      (fun v ↦ f (M.fixedSupportVertexTypes m (n + 1) v)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r Ψ
      ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) - _| < ε
  simpa only [CountableVariationComponentCounts.markedCount_map_types,
    fixedSupportPerronMark, f] using he

end PerronWright.CountableKernel
