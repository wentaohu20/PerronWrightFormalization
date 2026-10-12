import PerronWright.Probability.FiniteIrreducibleVaryingCriticalTime
import PerronWright.Probability.FiniteIrreducibleIsolationAveraging

/-! # Actual isolation domination for convergent critical parameters -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FiniteIrreducibleVaryingIsolation

open FiniteIrreducibleIsolationBounds FiniteIrreducibleIsolationAveraging
open FiniteIrreduciblePerronCountExpansion FiniteIrreducibleProfileFiniteCollection
open FiniteIrreduciblePearsonProfile
open FiniteIrreducibleVaryingCriticalTime

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem eventually_uniform_critical_isolation_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (ell : ℕ → ℝ) (lambda C : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, ∀ v : S → ℝ,
      (∀ a, 0 ≤ v a) → (∑ a, v a = K) → K ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      |isolationCore M (n : ℝ) (CriticalScaling.time (ell n) n) v -
        mainExponent M hM (n : ℝ) K (CriticalScaling.time (ell n) n)| ≤
      (isolationBudget M hM C 2 / (n : ℝ)) * countPearson M hM K v +
        criticalLinearEnvelope M hM (|lambda| + 1) C n := by
  filter_upwards [eventually_time_abs_le_two ell lambda hl,
    eventually_time_eq_raw ell lambda hl, eventually_parameter_bound ell lambda hl,
    eventually_ge_atTop (1 : ℕ)] with n htn hraw hpar hn1
  intro K v hv hs hsize
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hK : 0 ≤ K := hs ▸ Finset.sum_nonneg (fun a _ ↦ hv a)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hs' : K ≤ C * (n : ℝ) := hsize.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num : (2 / 3 : ℝ) ≤ 1)) hC)
  have hb := isolationCore_error_bound M hM hnR hC (by norm_num) htn v hv hs hs'
  have hlin := critical_linear_remainder_bound hn hK hsize (lambda := ell n)
  have heq : CriticalScaling.time (ell n) n - 1 = ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [hraw]
    unfold FiniteIrreducibleCriticalPrefactorScaling.rawTime
    ring
  rw [heq] at hb
  have hsq : (ell n) ^ 2 ≤ (|lambda| + 1) ^ 2 := by
    nlinarith [sq_abs (ell n), abs_nonneg (ell n)]
  have hφ : 0 ≤ linearBudget (M.perronFunction hM) := Finset.sum_nonneg (fun a _ ↦ sq_nonneg _)
  have hφ4 : 0 ≤ linearBudget (fun a ↦ (M.perronFunction hM a) ^ 2) :=
    Finset.sum_nonneg (fun a _ ↦ sq_nonneg _)
  refine hb.trans ?_
  have hlin1 : (n : ℝ) * ((ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)) * K / n) ^ 2) ≤
      (|lambda| + 1) ^ 2 * C ^ 2 * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
    hlin.1.trans (by gcongr)
  have h1 := mul_le_mul_of_nonneg_right hlin1 hφ
  have h2 := mul_le_mul_of_nonneg_right hlin.2 hφ4
  exact (add_le_add (add_le_add le_rfl h1) h2).trans_eq (by
    dsimp only [criticalLinearEnvelope]
    ring)


omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem eventually_uniform_isolationFluctuation_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ → ℝ) (lambda C : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) (hC : 0 ≤ C) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin q → ℕ,
      (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      ∀ p : StateFamily (S := S) k, |isolationFluctuation M hM (ell n) n k p| ≤
        (isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p +
          criticalLinearEnvelope M hM (|lambda| + 1) C n := by
  filter_upwards [eventually_uniform_critical_isolation_bound M hM ell lambda C hl hC] with n hn
  intro k hsize p
  simpa only [isolationFluctuation, countPearson_pooled] using
    hn (∑ i, (k i : ℝ)) (pooledCountReal k p) (pooledCountReal_nonneg k p) (pooledCountReal_sum k p) hsize


end PerronWright.FiniteIrreducibleVaryingIsolation

