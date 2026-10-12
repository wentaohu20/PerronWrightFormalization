import PerronWright.Probability.CountableFixedSupportGraphLaw
import PerronWright.Probability.FiniteIrreducibleVaryingLocalTerminal

/-! # Actual fixed-truncation local factorial laws

The graph source uses the actual rounded countable vertex assignment and
its empirical spectral root. The fixed reference model, its criticality,
the O(1) population error and the varying effective parameter are all proved.
Consequently the local theorem has no spectral-drift or profile interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open FiniteIrreducibleMarkedLocalMain (scaledMarkedFactorialExpectation)
open FiniteIrreducibleNativeMarkConcentration (perronMarks)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open AnnealedMarkedFactorialCounting (markedCount markedCount_one)

/-- Genuine empirical-normalized graph factorial integrals, including
arbitrary coupled continuous tests of the actual finite-support marks. -/
theorem fixedSupport_eventually_uniform_marked_factorial_density
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (Ψ : (Fin q → ProbabilityMeasure (Finset.range (m + 1))) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, markedCount (M.fixedSupportVertexTypes m (n + 1)) G
            (fun i ↦ CriticalScaling.size (y i) (n + 1)) r Ψ
            ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) -
        FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r * Ψ (perronMarks (M.fixedSupportModel m hlower hlo)
            (M.fixedSupportModel_isCritical m hlower hlo) q)| < ε := by
  let F := M.fixedSupportModel m hlower hlo
  let hF : F.IsCritical := M.fixedSupportModel_isCritical m hlower hlo
  let c : ℕ → (Finset.range (m + 1)) → ℕ := fun n ↦ fiberCount (M.fixedSupportVertexTypes m n)
  have hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * F.weight s| ≤ 2 * (m + 1 : ℝ) :=
    Eventually.of_forall (fun n s ↦ M.fixedSupportVertexTypes_rounding_bound m n hlower hlo s)
  have h := FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
    F hF q R hq (M.fixedSupportEffectiveParameter m lambda) lambda a b
    (M.fixedSupportEffectiveParameter_tendsto m lambda hlower hlo) ha hb c
    (2 * (m + 1 : ℝ)) (by positivity) hround Ψ hΨ hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h] with n hn
  intro y r hya hyb hr
  have he := hn (M.fixedSupportVertexTypes m (n + 1)) (fun _ ↦ rfl) y r hya hyb hr
  unfold scaledMarkedFactorialExpectation at he
  change |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    (∫ G, markedCount (M.fixedSupportVertexTypes m (n + 1)) G
      (fun i ↦ CriticalScaling.size (y i) (n + 1)) r Ψ
      ∂FiniteIrreducibleComponentProcess.graphLaw F
        (M.fixedSupportEffectiveParameter m lambda (n + 1)) (n + 1)
        (M.fixedSupportVertexTypes m (n + 1))) - _| < ε at he
  rw [M.fixedSupportModel_graphLaw_eq_actual m n lambda hlower hlo] at he
  exact he

/-- The unmarked actual fixed-truncation source is obtained with the
constant joint mark test, with no law-convergence assumption. -/
theorem fixedSupport_eventually_uniform_factorial_density
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n + 1)) r : ℝ)
            ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n) -
        FactorialDensity.density
          ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
          ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
          lambda y r| < ε := by
  filter_upwards [M.fixedSupport_eventually_uniform_marked_factorial_density
    m q R hq lambda a b ha hb hlower hlo (fun _ ↦ 1) continuous_const hε] with n hn
  intro y r hya hyb hr
  simpa only [markedCount_one, mul_one] using hn y r hya hyb hr

end PerronWright.CountableKernel
