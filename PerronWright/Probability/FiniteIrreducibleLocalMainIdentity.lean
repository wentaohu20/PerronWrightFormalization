import PerronWright.Probability.FiniteIrreducibleNumericalFactorialAssembly
import PerronWright.Probability.FiniteIrreducibleResidualNormalization

/-! # Exact deterministic factorial expectation with normalized residual

The measure below is the literal independent-edge graph law at an actual
fixed vertex-type assignment. No types are annealed. Its ordered genuine
component tuple count factors exactly into the numerical density-scale
factor and the normalized actual connected-state residual expectation.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleLocalMainIdentity

open FiniteIrreducibleDeterministicConnectedLawFormula
open FiniteIrreducibleDeterministicResidualWeights (residual)
open FiniteIrreducibleResidualNormalization (normalizedResidual)
open FiniteIrreducibleNumericalFactorialAssembly (numericalFactor)
open FiniteIrreducibleCriticalTuplePrefactor (enumerationPrefactor)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open FiniteIrreduciblePerronCountExpansion (mainExponent)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The literal scaled factorial expectation, conditional on the actual
deterministic type assignment, at the actual critical time. -/
def scaledFactorialExpectation (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) {q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) : ℝ :=
  (n : ℝ)^(2*(q : ℝ)/3) *
    (∫ G, (ComponentCounts.count G k r : ℝ)
      ∂FiniteIrreducibleTypedGraphLaw.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) x)

/-- Exact normalized expectation identity; its normalizers will later be
constructed from the genuine finite enumeration, not assumed in a terminal. -/
theorem scaledFactorialExpectation_eq_numericalFactor_mul_integral
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (ht : 0 < CriticalScaling.time lambda n)
    (x : Fin n → S) (c : S → ℕ) (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    scaledFactorialExpectation M lambda n x k r =
      numericalFactor M hM n k r (CriticalScaling.time lambda n) *
        (∫ p, normalizedResidual M hM lambda n c p
          ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) := by
  let E := mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n)
  have hcancel : Real.exp E *
      (∫ p, normalizedResidual M hM lambda n c p
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) =
      (∫ p, residual M (CriticalScaling.time lambda n) n c p
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) := by
    unfold normalizedResidual
    rw [integral_mul_const, Real.exp_neg]
    change Real.exp E * (_ * (Real.exp E)⁻¹) = _
    field_simp
  have hexact := factorial_expectation_connectedLaw_residual_formula M
    (CriticalScaling.time lambda n) ht hn x c hc k r hk pos
  unfold scaledFactorialExpectation
  rw [hexact]
  change ((n : ℝ)^(2*(q : ℝ)/3) * (enumerationPrefactor M n k r (CriticalScaling.time lambda n) * _)) = _
  unfold numericalFactor
  rw [Nat.cast_sum]
  change _ = ((n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (CriticalScaling.time lambda n) *
    Real.exp E) * _
  rw [← hcancel]
  ring

end PerronWright.FiniteIrreducibleLocalMainIdentity
