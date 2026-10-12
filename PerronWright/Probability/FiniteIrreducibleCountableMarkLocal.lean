import PerronWright.Probability.FiniteProbabilityVariationEmbedding
import PerronWright.Probability.CountableEmpiricalComponentMarks
import PerronWright.Probability.FiniteIrreducibleVaryingLocalTerminal

/-! # Actual finite graph factorial limits with countable TV marks

Each retained finite type is assigned its genuine natural-number type.
The ordered component tuple count uses those actual empirical measures
in the countable variation metric. Continuous coupled TV-mark tests
pull back continuously to finite weak marks, so the already proved
actual varying-time local theorem applies. No growing-support graph
limit is asserted by this fixed finite-support result.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableVariationComponentCounts

def markedCount {n q : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (k r : Fin q → ℕ) (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) : ℝ :=
  ∑ c : ComponentCounts.GoodComponentTuples G k r,
    Ψ (fun i ↦ CountableVariationMarks.ofProbability (EmpiricalTypeMarks.componentMark x (c.val i)))

theorem markedCount_map_types {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
    [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]
    {n q : ℕ} (x : Fin n → S) (f : S → ℕ) (G : SimpleGraph (Fin n)) (k r : Fin q → ℕ)
    (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) :
    markedCount (fun v ↦ f (x v)) G k r Ψ =
      AnnealedMarkedFactorialCounting.markedCount x G k r
        (fun ν ↦ Ψ (fun i ↦ FiniteProbabilityVariationEmbedding.embed f (ν i))) := by
  unfold markedCount AnnealedMarkedFactorialCounting.markedCount
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  funext i
  exact congrArg CountableVariationMarks.ofProbability
    (EmpiricalTypeMarks.componentMark_map x (c.val i) f (measurable_of_countable f)).symm

end PerronWright.CountableVariationComponentCounts

namespace PerronWright.FiniteIrreducibleCountableMarkLocal

open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open FiniteProbabilityVariationEmbedding (embed continuous_coupled_test)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem eventually_uniform_paper_floor_TV_marked_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (f : S → ℕ) (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ)
    (hΨ : Continuous Ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      0 < 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ ht : 0 ≤ 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)),
      ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |(n : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, CountableVariationComponentCounts.markedCount (fun v ↦ f (x v)) G
            (fun i ↦ ⌊y i * (n : ℝ) ^ (2 / 3 : ℝ)⌋₊) r Ψ
            ∂FiniteIrreducibleTypedGraphLaw.law M
              (1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ))) ht x) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r *
          Ψ (fun _ ↦ embed f (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM))| < ε := by
  filter_upwards [FiniteIrreducibleVaryingLocalTerminal.eventually_uniform_paper_floor_marked_factorial_density
    M hM q R hq ell lambda a b hl ha hb c D hD hround
    (fun ν ↦ Ψ (fun i ↦ embed f (ν i))) (continuous_coupled_test f Ψ hΨ) hε] with n hn
  refine ⟨hn.1, ?_⟩
  intro ht x hc y r hya hyb hr
  simpa only [CountableVariationComponentCounts.markedCount_map_types,
    FiniteIrreducibleNativeMarkConcentration.perronMarks] using hn.2 ht x hc y r hya hyb hr

end PerronWright.FiniteIrreducibleCountableMarkLocal
