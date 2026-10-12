import PerronWright.Analysis.FiniteIrreduciblePerronWrightFormulaMainTerm
import PerronWright.Analysis.FiniteIrreducibleConnectedPerronWrightFormula

/-!
# Genuine finite positive-surplus formula in the unified Wright notation

The already proved total connected EGF estimate is used directly, not merely
its cubic-core part. This file only changes the normalization and makes the
physical real connected-graph numerator explicit.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleUnifiedPositiveSurplus

open GraphCore

namespace Main
export PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm
  (perronWrightRadiusMainTerm perronWrightRadiusMainTerm_positive)
end Main

namespace Connected
export PerronWright.FiniteIrreducibleConnectedPerronWrightFormula
  (scalarConnectedRadiusMainTerm scalarConnectedRadiusMainTerm_eq_exp_rpow
   scalarConnectedContribution scalarConnectedContribution_eq_connectedWeight
   exists_scalarConnected_radius_relative_bound_uniform_eta)
end Connected

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- A shrinking scalar window eventually lies in any prescribed neighbourhood
of one. This is a model-independent filter fact. -/
theorem shrinkingWindow_eventually_mem_nhds
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (nhds 0))
    {p : ℝ → Prop} (hp : ∀ᶠ t : ℝ in nhds 1, p t) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k → p t := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hp
  have hnear : ∀ᶠ k : ℕ in atTop, eta k < delta :=
    heta.eventually (isOpen_Iio.mem_nhds hdelta)
  filter_upwards [hnear] with k hk
  intro t ht
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  exact ht.trans_lt hk

/-- The actual finite total-connected radius main term is exactly the cast
of the paper's unified real Wright main term. -/
theorem scalarConnectedRadiusMainTerm_eq_perronWrightRadiusMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    Connected.scalarConnectedRadiusMainTerm M hM ell k t =
      (Main.perronWrightRadiusMainTerm M hM k (ell + 1) t : ℂ) := by
  have hbeta : 0 ≤ M.beta hM := (M.beta_pos hM).le
  have hsqrtPow : Real.sqrt (M.beta hM) ^ ell =
      (M.beta hM) ^ ((ell : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbeta]
    congr 1
    ring
  have hsqrtCast : (Real.sqrt (M.beta hM) : ℂ) ^ ell =
      ((M.beta hM) ^ ((ell : ℝ) / 2) : ℝ) := by
    exact_mod_cast hsqrtPow
  rw [Connected.scalarConnectedRadiusMainTerm_eq_exp_rpow M hM hell hk t,
    Main.perronWrightRadiusMainTerm_positive M hM hell k t,
    positiveSurplusWrightConstant_eq_ofReal]
  unfold positiveSurplusCubicExponent
    FiniteIrreducibleTreePerronWrightFormula.physicalTreeRadius
  rw [hsqrtCast]
  push_cast
  ring

/-- The literal connected weight at every fixed positive excess satisfies
the unified radius formula. The constant is chosen before any shrinking
window sequence is supplied. -/
theorem exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k (ell + 1) /
            Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    Connected.exists_scalarConnected_radius_relative_bound_uniform_eta M hM hell
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have htposWindow := shrinkingWindow_eventually_mem_nhds eta heta
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hbound eta hetaNonneg heta, htposWindow,
      eventually_ge_atTop (1 : ℕ)] with k hk hkt hkone
  intro t ht
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have h := hk t ht
  rw [Connected.scalarConnectedContribution_eq_connectedWeight M t (hkt t ht) ell k,
    scalarConnectedRadiusMainTerm_eq_perronWrightRadiusMainTerm M hM hell hkpos t] at h
  have hnorm :
      ‖(M.bjrModel.connectedWeight t k (ell + 1) : ℂ) /
          (Main.perronWrightRadiusMainTerm M hM k (ell + 1) t : ℂ) - 1‖ =
        |M.bjrModel.connectedWeight t k (ell + 1) /
          Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1| := by norm_cast
  rw [hnorm] at h
  exact h

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_positiveSurplusPerronWright_radius_relative_bound_of_tendsto
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k (ell + 1) /
            Main.perronWrightRadiusMainTerm M hM k (ell + 1) t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_positiveSurplusPerronWright_radius_relative_bound_uniform_eta M hM hell
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

end PerronWright.FiniteIrreducibleUnifiedPositiveSurplus
