import PerronWright.Probability.EmpiricalMarkConcentration
import PerronWright.Probability.EmpiricalWeakNeighborhood

/-!
# Weak concentration of genuine compact-model empirical marks

All conclusions use the actual connected type laws (or their actual
independent product). The center is the literal Perron probability
measure. This is a mark-concentration theorem, not a marked graph
point-process limit or a density-transfer assumption.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped Topology Real BigOperators

noncomputable section

namespace PerronWright.EmpiricalMarkWeakConcentration

open ConnectedTypeLaw EmpiricalTypeMarks EmpiricalMarkConcentration
open EmpiricalWeakNeighborhood ProfileFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Under the actual connected type laws, the empirical probability
measure concentrates in every neighborhood of the literal Perron law
in the genuine weak topology. -/
theorem connectedMark_probability_outside_weak_nhds_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n))
    (hkTop : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMark M hM)) :
    Tendsto (fun n ↦ (law M (g n) (k n) (r n) (hC n)).real
      {p | connectedMark (hk n) p ∉ U}) atTop (𝓝 0) := by
  have : ∀ n, IsFiniteMeasure (law M (g n) (k n) (r n) (hC n)) := fun _ ↦ inferInstance
  apply probability_outside_nhds_tendsto_zero
    (fun n ↦ law M (g n) (k n) (r n) (hC n))
    (fun n ↦ connectedMark (hk n)) (perronMark M hM) _ U hU
  intro f ε hε
  exact test_probability_tendsto_zero M hM R L hL k r hk g hC hkTop hr hg
    f.toContinuousMap ε hε

/-- Weak concentration of the actual pooled empirical mark under a
fixed finite independent component collection. Individual sizes may
stay bounded; only the total size must tend to infinity. -/
theorem pooledMark_probability_outside_weak_nhds_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S, ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMark M hM)) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | pooledMark hq (k n) (hk n) p ∉ U}) atTop (𝓝 0) := by
  have : ∀ n, IsFiniteMeasure (productLaw M (k n) (r n) (g n) (hC n)) := fun _ ↦ inferInstance
  apply probability_outside_nhds_tendsto_zero
    (fun n ↦ productLaw M (k n) (r n) (g n) (hC n))
    (fun n ↦ pooledMark hq (k n) (hk n)) (perronMark M hM) _ U hU
  intro f ε hε
  exact pooled_test_probability_tendsto_zero M hM R q hq L hL k r hk g hC hKTop hr hg
    f.toContinuousMap ε hε

end PerronWright.EmpiricalMarkWeakConcentration
