import PerronWright.Probability.FiniteIrreducibleDeterministicResidualWeights
import PerronWright.Probability.FiniteIrreducibleDeterministicDepletion

/-!
# Exact finite-population factorization of the deterministic residual

The actual pooled type counts are used throughout. This separates the
proved raw residual into literal descending-factorial depletion, the
empirical population correction, the quadratic/diagonal isolation
exponent, and the zero-safe edge-odds correction. No asymptotic premise
or criticality assumption is used.
-/

open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleDeterministicResidualFactorization

open AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawProduct
open FiniteIrreducibleTypePlacementMultiplicity FiniteIrreducibleConnectedLawFiniteSum
open FiniteIrreducibleConnectedOddsFactorialFormula
open FiniteIrreducibleDeterministicResidualWeights FiniteIrreducibleDeterministicDepletion

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem targetSelectionRatio_eq_depletion_populationProduct
    (M : FiniteIrreducibleModel S) {n : ℕ} (hn : 0 < n)
    (c : S → ℕ) (hc : ∀ a, 0 < c a) {q : ℕ} {k : Fin q → ℕ}
    (y : SelectedVertices k → S) :
    targetSelectionRatio M n c y =
      normalizedDepletion c (fiberCount y) *
        (∏ a, ((c a : ℝ) / ((n : ℝ) * M.weight a)) ^ fiberCount y a) := by
  unfold targetSelectionRatio normalizedDepletion
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [div_pow]
  field_simp [(Nat.cast_pos.mpr (hc a) : (0 : ℝ) < c a).ne',
    (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne', (M.weight_pos a).ne']

theorem degreeCorrection_typeCount_identity
    (M : FiniteIrreducibleModel S) (n : ℕ) (c K : S → ℕ) :
    (∑ a, (K a : ℝ) * degreeCorrection M n c a) =
      (∑ a, ∑ b, (K a : ℝ) * M.kernel a b * (c b : ℝ)) / (n : ℝ) -
        ∑ a, (K a : ℝ) * (∑ b, M.kernel a b * M.weight b) := by
  unfold degreeCorrection empiricalFrequency
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    ← mul_div_assoc, ← Finset.sum_div, mul_assoc]

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem residual_exponent_eq_populationCorrection
    (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    t * targetDegreeSum M p -
        t / (n : ℝ) * countIsolationBudget M c (pooledTypes p) =
      -t * (∑ a, (fiberCount (pooledTypes p) a : ℝ) * degreeCorrection M n c a) +
        t / (2 * (n : ℝ)) *
          ((∑ a, ∑ b, (fiberCount (pooledTypes p) a : ℝ) * M.kernel a b *
              (fiberCount (pooledTypes p) b : ℝ)) +
           ∑ a, (fiberCount (pooledTypes p) a : ℝ) * M.kernel a a) := by
  rw [degreeCorrection_typeCount_identity, targetDegreeSum_eq_typeCount_sum]
  unfold countIsolationBudget
  ring

/-- Exact factorization for arbitrary positive deterministic population
counts, including profiles whose descending factorial is zero. -/
theorem residual_eq_depletion_population_isolation_odds
    (M : FiniteIrreducibleModel S) (t : ℝ) {n : ℕ} (hn : 0 < n)
    (c : S → ℕ) (hc : ∀ a, 0 < c a)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    residual M t n c p =
      normalizedDepletion c (fiberCount (pooledTypes p)) *
        populationCorrection M n c (fiberCount (pooledTypes p)) t *
          Real.exp (t / (2 * (n : ℝ)) *
            ((∑ a, ∑ b, (fiberCount (pooledTypes p) a : ℝ) * M.kernel a b *
                (fiberCount (pooledTypes p) b : ℝ)) +
             ∑ a, (fiberCount (pooledTypes p) a : ℝ) * M.kernel a a)) *
          oddsCorrection M t n p := by
  unfold FiniteIrreducibleDeterministicResidualWeights.residual
  rw [targetSelectionRatio_eq_depletion_populationProduct M hn c hc,
    residual_exponent_eq_populationCorrection, Real.exp_add]
  unfold populationCorrection
  ring

end PerronWright.FiniteIrreducibleDeterministicResidualFactorization

