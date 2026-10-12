import PerronWright.Analysis.FiniteIrreducibleConnectedFieldAsymptotic

/-!
# Literal critical Perron--Wright formula for finite irreducible types

This is the total original annealed simple connected-graph weight at t = 1,
not a cubic-part contribution. The real main term has the paper's Wright
constant, beta factor, exponential and exact real power of k. The statement
requires only the literal finite model and its actual matrix criticality.
Tree and unicyclic surpluses are not included.
-/

open Filter Topology Asymptotics
open scoped Classical Topology Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleCriticalConnectedWright

open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The literal real positive-surplus Perron--Wright main term at criticality. -/
def criticalConnectedMain
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell k : ℕ) : ℝ :=
  (Real.sqrt (M.beta hM)) ^ ell * positiveSurplusWrightConstantReal ell *
    Real.exp (-(k : ℝ)) *
      (k : ℝ) ^ ((k : ℝ) + 3 * (ell : ℝ) / 2 - 1 / 2)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalConnectedMain_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) :
    0 < criticalConnectedMain M hM ell k := by
  unfold criticalConnectedMain
  exact mul_pos
    (mul_pos
      (mul_pos (pow_pos (Real.sqrt_pos.2 (M.beta_pos hM)) _)
        (positiveSurplusWrightConstantReal_pos ell hell))
      (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The complex transfer normalization equals the cast of the literal
real Perron--Wright main term. -/
theorem criticalConnectedMain_ofReal
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) :
    (criticalConnectedMain M hM ell k : ℂ) =
      (Real.sqrt (M.beta hM) : ℂ) ^ ell *
        positiveSurplusCubicFactorialMain ell k := by
  rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hk,
    positiveSurplusWrightConstant_eq_ofReal]
  unfold criticalConnectedMain positiveSurplusCubicExponent
  push_cast
  ring

/-- At t = 1 the literal scalar graph weight is exactly its zero-field
complexification. This uses only the model-data scalar identity. -/
theorem connectedWeight_one_ofReal
    (M : FiniteIrreducibleModel S) (k r : ℕ) :
    (M.bjrModel.connectedWeight 1 k r : ℂ) =
      M.bjrModel.complexFieldConnectedWeight 0 k r := by
  simpa only [Complex.ofReal_one, one_zpow, one_mul,
    ScalarFieldResponse.scalarFieldComplex_one] using
      ScalarFieldResponse.connectedWeight_scalarFieldComplex
        M.bjrModel 1 zero_lt_one k r

/-- The total genuine critical connected-graph weight has relative error
O(k^(-1/2)) in the literal real Perron--Wright formula, for every fixed
positive surplus and every literal finite irreducible critical model. -/
theorem exists_connectedWeight_one_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      |M.bjrModel.connectedWeight 1 k (ell + 1) /
          criticalConnectedMain M hM ell k - 1| ≤
        K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ :=
    FiniteIrreducibleConnectedFieldAsymptotic.exists_complexFieldConnectedWeight_zero_relative_bound
      M hM hell
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with k hk hkpos
  have hnorm :
      |M.bjrModel.connectedWeight 1 k (ell + 1) /
          criticalConnectedMain M hM ell k - 1| =
        ‖M.bjrModel.complexFieldConnectedWeight 0 k (ell + 1) /
          ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
            positiveSurplusCubicFactorialMain ell k) - 1‖ := by
    rw [← criticalConnectedMain_ofReal M hM hell hkpos,
      ← connectedWeight_one_ofReal]
    norm_cast
  rw [hnorm]
  exact hk

/-- An asymptotic form of the same actual real relative-error estimate. -/
theorem connectedWeight_one_relative_error_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    (fun k : ℕ ↦ M.bjrModel.connectedWeight 1 k (ell + 1) /
      criticalConnectedMain M hM ell k - 1) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_connectedWeight_one_relative_bound M hM hell
  apply IsBigO.of_bound K
  filter_upwards [hbound] with k hk
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)] using hk

/-- In particular the genuine connected weight divided by the literal
Perron--Wright main term tends to one. -/
theorem tendsto_connectedWeight_one_div_main
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    Tendsto (fun k : ℕ ↦ M.bjrModel.connectedWeight 1 k (ell + 1) /
      criticalConnectedMain M hM ell k) atTop (𝓝 1) := by
  have hpow : Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have herr :=
    (connectedWeight_one_relative_error_isBigO M hM hell).trans_tendsto hpow
  have hsum := herr.add_const 1
  simpa only [zero_add, sub_add_cancel] using hsum

end PerronWright.FiniteIrreducibleCriticalConnectedWright
