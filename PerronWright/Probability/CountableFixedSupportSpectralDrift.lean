import PerronWright.Probability.CountableFixedSupportReference
import PerronWright.Probability.CountableFixedSupportSpectralPerturbation
import PerronWright.Probability.CriticalParameterDrift

/-! # Proved critical-scale spectral drift for the actual fixed truncation

Literal rounding gives O(1/n) atomic variation. The actual shared-space
spectral perturbation gives O(n^(-1/2)) spectral error, so its critical
n^(1/3) multiple tends to zero. No spectral drift is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GrowingTypeCounts CountableTypeRealization

theorem fixedSupport_empirical_error_le (M : CountableKernel) (m n : ℕ) :
    (∑' a, |M.empiricalWeights (fun _ ↦ m) n a - M.fixedSupportWeights m a|) ≤
      2 * (m + 1 : ℝ) / (n + 1 : ℕ) := by
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun a ha ↦ by
    rw [M.empiricalWeights_finite_support (fun _ ↦ m) n a ha,
      M.fixedSupportWeights_zero m a ha, sub_self, abs_zero])]
  rw [← Fin.sum_univ_eq_sum_range]
  have he (a : Fin (m + 1)) :
      M.empiricalWeights (fun _ ↦ m) n a = empiricalLaw (weights M) m (n + 1) a := by
    rw [empiricalWeights, empiricalMeasure_atom, extendedLaw_fin]
  simp_rw [he, M.fixedSupportWeights_fin]
  simpa only [empiricalLaw, Fintype.card_fin, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    FiniteTypeCounts.sum_empirical_error_le (0 : Fin (m + 1)) (truncatedLaw (weights M) m)
      (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
      (sum_truncatedLaw (weights M) M.atomMass_pos m) (Nat.succ_pos n)

theorem fixedSupport_spectral_error_square_le (M : CountableKernel) (m n : ℕ) :
    (M.empiricalSpectralRadius (fun _ ↦ m) n - M.fixedSupportSpectralRadius m) ^ 2 ≤
      8 * M.upper ^ 2 * (m + 1 : ℝ) / (n + 1 : ℕ) := by
  have h := M.weightedSpectralRadius_sub_square_le
    (M.empiricalWeights (fun _ ↦ m) n) (M.fixedSupportWeights m)
    (M.empiricalWeights_nonneg (fun _ ↦ m) n) (M.fixedSupportWeights_nonneg m)
    (M.empiricalWeights_hasSum (fun _ ↦ m) n) (M.fixedSupportWeights_hasSum m)
  refine h.trans ?_
  calc
    _ ≤ 4 * M.upper ^ 2 * (2 * (m + 1 : ℝ) / (n + 1 : ℕ)) := by
      gcongr
      exact M.fixedSupport_empirical_error_le m n
    _ = _ := by ring

theorem fixedSupport_scaled_spectral_error_square_le (M : CountableKernel) (m n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius (fun _ ↦ m) n - M.fixedSupportSpectralRadius m)) ^ 2 ≤
      (8 * M.upper ^ 2 * (m + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have he : (((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) ^ 2 =
      ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn.le]
    norm_num
  have hs : ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) / (n + 1 : ℕ) =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have h := Real.rpow_sub hn (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at h
    convert h.symm using 1
  rw [mul_pow, he]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) *
        (8 * M.upper ^ 2 * (m + 1 : ℝ) / (n + 1 : ℕ)) := by
      gcongr
      exact M.fixedSupport_spectral_error_square_le m n
    _ = (8 * M.upper ^ 2 * (m + 1 : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) / (n + 1 : ℕ)) := by ring
    _ = _ := by rw [hs]

theorem fixedSupport_scaled_spectral_drift_tendsto_zero (M : CountableKernel) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius (fun _ ↦ m) n - M.fixedSupportSpectralRadius m))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ ↦ (8 * M.upper ^ 2 * (m + 1 : ℝ)) *
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)).const_mul
          (8 * M.upper ^ 2 * (m + 1 : ℝ))
  have hsq := squeeze_zero (fun n ↦ sq_nonneg _) (M.fixedSupport_scaled_spectral_error_square_le m) ht
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] using habs

def fixedSupportEmpiricalRoot (M : CountableKernel) (m n : ℕ) : ℝ :=
  M.empiricalSpectralRadius (fun _ ↦ m) (n - 1)

theorem fixedSupportEmpiricalRoot_pos (M : CountableKernel) (m n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < M.fixedSupportEmpiricalRoot m n :=
  (M.empiricalOperator_exists_nonnegative_perron (fun _ ↦ m) (n - 1) hlower hlo).1

theorem fixedSupportEmpiricalRoot_scaled_drift (M : CountableKernel) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) *
      (M.fixedSupportEmpiricalRoot m n - M.fixedSupportSpectralRadius m)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := tendsto_atTop.mpr (fun b ↦ by
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega)
  apply ((M.fixedSupport_scaled_spectral_drift_tendsto_zero m).comp hp).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Function.comp_def, fixedSupportEmpiricalRoot, Nat.sub_add_cancel hn]

theorem fixedSupportEmpiricalRoot_tendsto (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (M.fixedSupportEmpiricalRoot m) atTop (𝓝 (M.fixedSupportSpectralRadius m)) := by
  have hr := M.fixedSupportSpectralRadius_pos m hlower hlo
  have hd := (M.fixedSupportEmpiricalRoot_scaled_drift m).div_const (M.fixedSupportSpectralRadius m)
  simp only [zero_div] at hd
  have hd' : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) *
      (M.fixedSupportEmpiricalRoot m n / M.fixedSupportSpectralRadius m - 1)) atTop (𝓝 0) := by
    convert hd using 1
    ext n
    field_simp
  have h := (CriticalParameterDrift.sigma_tendsto_one hd').mul_const (M.fixedSupportSpectralRadius m)
  simpa only [div_mul_cancel₀ _ hr.ne', one_mul] using h

end PerronWright.CountableKernel
