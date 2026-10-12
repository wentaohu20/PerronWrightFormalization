import PerronWright.Probability.FiniteIrreducibleIsolationBounds
import PerronWright.Probability.FiniteIrreducibleNativeProfileAveraging

/-! # Actual native isolation averages from proved Perron profile moments

Every count in this file is the literal fibre cardinality of the genuine
component-state tuple. The nonlinear isolation fluctuation is controlled
on the entire count-vector space. Its actual L1 exponential average is
derived from finite field enumeration and the proved native moments.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleIsolationAveraging

open FiniteIrreduciblePerronCountExpansion FiniteIrreducibleIsolationBounds
open FiniteIrreducibleNativeProfileAveraging FiniteIrreduciblePearsonProfile
open FiniteIrreducibleProfileFiniteCollection
open FiniteIrreducibleTypePlacementMultiplicity FiniteIrreducibleConnectedLawFiniteSum
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)

def pooledCountReal {S : Type*} {q : ℕ} (k : Fin q → ℕ)
    (p : StateFamily (S := S) k) (a : S) : ℝ := (fiberCount (pooledTypes p) a : ℝ)

theorem pooledCountReal_nonneg {S : Type*} {q : ℕ} (k : Fin q → ℕ)
    (p : StateFamily (S := S) k) (a : S) : 0 ≤ pooledCountReal k p a := Nat.cast_nonneg _

theorem pooledCountReal_sum {S : Type*} [Fintype S] [DecidableEq S]
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    ∑ a, pooledCountReal k p a = ∑ i, (k i : ℝ) := by
  simpa only [pooledCountReal, ← aggregateCount_eq_pooledFiberCount] using sum_aggregateCount_real k p

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem countPearson_pooled (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    countPearson M hM (∑ i, (k i : ℝ)) (pooledCountReal k p) = pearson M hM k p := by
  unfold countPearson pearson deviation fluctuation
  simp only [pooledCountReal, aggregateCount_eq_pooledFiberCount]

def isolationFluctuation (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) : ℝ :=
  isolationCore M (n : ℝ) (CriticalScaling.time lambda n) (pooledCountReal k p) -
    mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem eventually_uniform_isolationFluctuation_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda C : ℝ) (hC : 0 ≤ C)
    (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin q → ℕ,
      (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      ∀ p : StateFamily (S := S) k, |isolationFluctuation M hM lambda n k p| ≤
        (isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p +
          criticalLinearEnvelope M hM lambda C n := by
  filter_upwards [eventually_uniform_critical_isolation_bound M hM lambda C hC] with n hn
  intro k hsize p
  simpa only [isolationFluctuation, countPearson_pooled] using
    hn (∑ i, (k i : ℝ)) (pooledCountReal k p) (pooledCountReal_nonneg k p) (pooledCountReal_sum k p) hsize

theorem native_isolation_exponential_L1_tendsto_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda C : ℝ) (hC : 0 ≤ C) (k r : ℕ → Fin q → ℕ)
    (hk : ∀ n i, 0 < k n i)
    (pos : ∀ n i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k n i) (r n i))
    (hKt : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun n ↦ ∫ p, |Real.exp (isolationFluctuation M hM lambda n (k n) p) - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
        (k n) (r n) (pos n)) atTop (𝓝 0) := by
  apply native_pearson_with_remainder_exponential_L1_limit M hM R q hq lambda
    (isolationBudget M hM C 2) C (isolationBudget_nonneg M hM hC (by norm_num)) hC k r hk pos
    hKt hr hsize (fun n ↦ isolationFluctuation M hM lambda n (k n))
    (criticalLinearEnvelope M hM lambda C) (criticalLinearEnvelope_tendsto_zero M hM lambda C)
  filter_upwards [eventually_uniform_isolationFluctuation_bound M hM lambda C hC q, hsize]
    with n hn hs
  exact hn (k n) hs

/-- Actual native isolation L1 terminal from the finite model alone.
In particular no positive normalizer, profile concentration, or UI
statement is assumed. The spectral value -1 remains admissible. -/
theorem exists_actual_native_isolation_L1_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda C : ℝ) (hC : 0 ≤ C) :
    ∃ K₀ : ℕ, ∃ _hK₀ : 0 < K₀,
      ∃ pos : ∀ k : ℕ, K₀ ≤ k → ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g k r,
      ∀ k r : ℕ → Fin q → ℕ, ∀ hk : ∀ n i, K₀ ≤ k n i,
      ∀ hr : ∀ n i, r n i ≤ R,
      Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop →
      (∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) →
      Tendsto (fun n ↦ ∫ p, |Real.exp (isolationFluctuation M hM lambda n (k n) p) - 1|
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n))
          (k n) (r n) (fun i ↦ pos (k n i) (hk n i) (r n i) (hr n i)
            (M.bjrModel.scalarField (CriticalScaling.time lambda n)))) atTop (𝓝 0) := by
  obtain ⟨K₀, hK₀, pos, _⟩ := exists_actual_native_population_L1_limit M hM R q lambda
  refine ⟨K₀, hK₀, pos, ?_⟩
  intro k r hk hr hKt hsize
  exact native_isolation_exponential_L1_tendsto_zero M hM R q hq lambda C hC k r
    (fun n i ↦ hK₀.trans_le (hk n i)) _ hKt (Eventually.of_forall hr) hsize

end PerronWright.FiniteIrreducibleIsolationAveraging
