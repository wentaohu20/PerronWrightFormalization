import PerronWright.Probability.FiniteIrreducibleIsolationAveraging
import PerronWright.Probability.FiniteIrreducibleDeterministicResidualFactorization
import PerronWright.Probability.FiniteIrreducibleOddsCorrectionMoments

/-! # Literal deterministic residual normalization

The residual in the exact finite graph formula is normalized by its
proved Perron size exponent. Its exponent consists of the actual
selection remainder, population correction, isolation fluctuation,
diagonal correction, and zero-safe odds correction. All identities use
the literal pooled type fibres, not an auxiliary profile interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleResidualNormalization

open FiniteIrreduciblePerronCountExpansion FiniteIrreducibleIsolationBounds
open FiniteIrreducibleIsolationAveraging FiniteIrreducibleNativeProfileAveraging
open FiniteIrreducibleDeterministicDepletion FiniteIrreducibleDepletionRounding
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleProfileFiniteCollection FiniteIrreduciblePearsonProfile
open FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleDeterministicResidualFactorization
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleOddsCorrectionBounds (criticalLogOddsEnvelope)
open FiniteIrreducibleOddsCorrectionMoments (connectedProductLaw_abs_log_oddsCorrection_ae_le)

variable {S : Type*} [Fintype S] [DecidableEq S]

def diagonalBudget (M : FiniteIrreducibleModel S) : ℝ := ∑ a, |M.kernel a a|

theorem diagonalBudget_nonneg (M : FiniteIrreducibleModel S) :
    0 ≤ diagonalBudget M := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem diagonalCount_abs_le (M : FiniteIrreducibleModel S) (v : S → ℝ)
    (hv : ∀ a, 0 ≤ v a) :
    |∑ a, v a * M.kernel a a| ≤ diagonalBudget M * ∑ a, v a := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold diagonalBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul, abs_of_nonneg (hv a)]
  have ha := Finset.single_le_sum (fun b _ ↦ hv b) (Finset.mem_univ a)
  calc
    _ ≤ (∑ b, v b) * |M.kernel a a| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ = _ := by ring

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def selectionRemainder (M : FiniteIrreducibleModel S) (n : ℕ) (c : S → ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : StateFamily (S := S) k) : ℝ :=
  Real.log (normalizedDepletion c (fiberCount (pooledTypes p))) +
    (∑ a, (fiberCount (pooledTypes p) a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a)) +
    ∑ a, (fiberCount (pooledTypes p) a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)

def diagonalExponent (M : FiniteIrreducibleModel S) (n : ℕ) (t : ℝ)
    {q : ℕ} {k : Fin q → ℕ} (p : StateFamily (S := S) k) : ℝ :=
  t / (2 * (n : ℝ)) * ∑ a, pooledCountReal k p a * M.kernel a a

def residualExponent (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (c : S → ℕ) {q : ℕ} (k : Fin q → ℕ)
    (p : StateFamily (S := S) k) : ℝ :=
  selectionRemainder M n c p +
    Real.log (populationCorrection M n c (fiberCount (pooledTypes p))
      (CriticalScaling.time lambda n)) +
    isolationFluctuation M hM lambda n k p +
    diagonalExponent M n (CriticalScaling.time lambda n) p +
    Real.log (oddsCorrection M (CriticalScaling.time lambda n) n p)

def normalizedResidual (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (c : S → ℕ) {q : ℕ} {k : Fin q → ℕ}
    (p : StateFamily (S := S) k) : ℝ :=
  residual M (CriticalScaling.time lambda n) n c p *
    Real.exp (-mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem pooled_target_square (M : FiniteIrreducibleModel S) (n : ℕ)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    (∑ a, (fiberCount (pooledTypes p) a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a)) =
      weightedSquare M (pooledCountReal k p) / (2 * (n : ℝ)) := by
  unfold weightedSquare pooledCountReal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem pooled_target_cube (M : FiniteIrreducibleModel S) (n : ℕ)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k) :
    (∑ a, (fiberCount (pooledTypes p) a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)) =
      weightedCube M (pooledCountReal k p) / (6 * (n : ℝ) ^ 2) := by
  unfold weightedCube pooledCountReal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow]
  ring

/-- Exact positive residual exponent, on the actual whole profile space. -/
theorem normalizedResidual_eq_exp (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {n : ℕ} (hn : 0 < n) (c : S → ℕ) (hc : ∀ a, 0 < c a)
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k)
    (hd : 0 < normalizedDepletion c (fiberCount (pooledTypes p))) :
    normalizedResidual M hM lambda n c p = Real.exp (residualExponent M hM lambda n c k p) := by
  have hp := populationCorrection_pos M hn c (fiberCount (pooledTypes p)) hc
    (CriticalScaling.time lambda n)
  have ho := oddsCorrection_pos M (CriticalScaling.time_nonneg lambda n) n p
  unfold normalizedResidual
  rw [residual_eq_depletion_population_isolation_odds M _ hn c hc p,
    ← Real.exp_log hd, ← Real.exp_log hp, ← Real.exp_log ho]
  simp only [← Real.exp_add]
  congr 1
  unfold residualExponent selectionRemainder isolationFluctuation diagonalExponent
  rw [pooled_target_square, pooled_target_cube]
  unfold isolationCore bilinear pooledCountReal
  ring

def diagonalEnvelope (M : FiniteIrreducibleModel S) (C : ℝ) (n : ℕ) : ℝ :=
  diagonalBudget M * C * (n : ℝ) ^ (-(1 / 3 : ℝ))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem diagonalEnvelope_tendsto_zero (M : FiniteIrreducibleModel S) (C : ℝ) :
    Tendsto (diagonalEnvelope M C) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ diagonalBudget M * C * (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul (diagonalBudget M * C)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem diagonalExponent_critical_bound (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : |t| ≤ 2) {C : ℝ}
    {q : ℕ} (k : Fin q → ℕ) (p : StateFamily (S := S) k)
    (hsize : (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    |diagonalExponent M n t p| ≤ diagonalEnvelope M C n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hb := diagonalCount_abs_le M (pooledCountReal k p) (pooledCountReal_nonneg k p)
  rw [pooledCountReal_sum] at hb
  unfold diagonalExponent
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
  have hpow : (n : ℝ) ^ (2 / 3 : ℝ) / n = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hh := Real.rpow_sub hnR (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at hh
    convert hh.symm using 1
  calc
    _ ≤ (2 / (2 * (n : ℝ))) * (diagonalBudget M * ∑ i, (k i : ℝ)) :=
      mul_le_mul (div_le_div_of_nonneg_right ht (by positivity)) hb (abs_nonneg _) (by positivity)
    _ = diagonalBudget M * (∑ i, (k i : ℝ)) / n := by ring
    _ ≤ diagonalBudget M * (C * (n : ℝ) ^ (2 / 3 : ℝ)) / n := by
      gcongr
      exact diagonalBudget_nonneg M
    _ = diagonalBudget M * C * ((n : ℝ) ^ (2 / 3 : ℝ) / n) := by ring
    _ = diagonalEnvelope M C n := by rw [hpow]; rfl

end PerronWright.FiniteIrreducibleResidualNormalization
