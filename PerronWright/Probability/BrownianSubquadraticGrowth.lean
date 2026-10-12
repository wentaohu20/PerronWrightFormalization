import PerronWright.Probability.BrownianGrowingDyadicWindows
import PerronWright.Probability.BrownianParabolicReflection

/-!
# Actual full-horizon subquadratic Brownian growth

The constructed Gaussian Brownian process is controlled uniformly on
growing windows by summable fourth-moment tails and dyadic chaining.
Its ratio to the square of time tends to zero almost surely. This is a
proved path property, not an excursion or Brownian growth hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianSubquadraticGrowth

open BrownianGaussianSkeleton BrownianDyadicGrid BrownianDyadicModulus
open BrownianContinuousModification BrownianGrowingDyadicWindows

theorem ae_eventually_uniform_window_bound :
    ∀ᵐ x ∂rationalLaw, ∀ᶠ N in atTop, ∀ t : ℝ≥0, (t : ℝ) < (2 : ℝ) ^ N →
      ‖process t x‖ ≤ 9 * (3 : ℝ) ^ N := by
  filter_upwards [ae_eventually_all_level_bound, ae_eventually_base_bound,
    ae_dyadicSamples_localBound, ae_all_dyadic_process_eq, process_zero_ae_eq_zero]
    with x hlevels hbase hlocal hmatch hzero
  have hqzero : rationalProcess (dyadicTime 0 0) x = 0 := by
    have h := hmatch 0 0
    simpa only [DyadicFloorGeometry.coordinate, pow_zero, Nat.cast_zero, zero_div,
      NNReal.mk_zero, hzero] using h.symm
  filter_upwards [hlevels, hbase] with N hn hb
  intro t ht
  have ht' : (t : ℝ) < (2 ^ N : ℕ) := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using ht
  have hneighbor : ∀ n k : ℕ, k < 2 ^ N * 2 ^ n →
      ‖dyadicSamples x n (k+1) - dyadicSamples x n k‖ ≤
        (3 : ℝ) ^ N * DyadicGeometricApproximation.ratio ^ n := by
    simpa only [dyadicSamples, increment, DyadicGeometricApproximation.ratio, decay] using hn
  have hdist := DyadicGeometricApproximation.samples_extension_distance
    (dyadicSamples_compatible x) hlocal (by positivity : 0 ≤ (3 : ℝ) ^ N)
    hneighbor ht' 0
  have hvalue := hb (DyadicFloorGeometry.index 0 t)
    (by simpa using DyadicFloorGeometry.index_lt_window ht' 0)
  rw [hqzero, sub_zero] at hvalue
  calc
    ‖process t x‖ ≤
      ‖process t x - DyadicGeometricApproximation.samples (dyadicSamples x) t 0‖ +
        ‖DyadicGeometricApproximation.samples (dyadicSamples x) t 0‖ := by
      simpa only [add_comm, norm_sub_rev] using
        norm_le_insert (DyadicGeometricApproximation.samples (dyadicSamples x) t 0) (process t x)
    _ ≤ (3 : ℝ) ^ N / (1 - DyadicGeometricApproximation.ratio) + (3 : ℝ) ^ N := by
      apply add_le_add
      · simpa only [process, dist_eq_norm, norm_sub_rev, pow_zero, mul_one] using hdist
      · exact hvalue
    _ = _ := by norm_num [DyadicGeometricApproximation.ratio]; ring

theorem tendsto_div_sq_of_window_bound (f : ℝ≥0 → ℝ)
    (hf : ∀ᶠ N in atTop, ∀ t : ℝ≥0, (t : ℝ) < (2 : ℝ) ^ N →
      ‖f t‖ ≤ 9 * (3 : ℝ) ^ N) :
    Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)^2) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hg : Tendsto (fun n : ℕ ↦ 27 * (3 / 4 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4)
        (by norm_num : (3 / 4 : ℝ) < 1)).const_mul 27
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hg.eventually (Iio_mem_nhds hε))
  let K := max A B
  filter_upwards [eventually_ge_atTop (NNReal.mk ((2 : ℝ)^K) (by positivity))] with t ht
  have htK : (2 : ℝ)^K ≤ t := ht
  have ht1 : (1 : ℝ) ≤ t := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans htK
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ht1 (by norm_num : (1 : ℝ) < 2)
  have hnK : K ≤ n := by
    by_contra h
    have hnk : n+1 ≤ K := by omega
    have hp : (2 : ℝ)^(n+1) ≤ (2 : ℝ)^K := by gcongr; norm_num
    exact (not_lt_of_ge (hp.trans htK)) hn'
  have hf' := hA (n+1) (by dsimp [K] at hnK; omega) t hn'
  have hpow : (t : ℝ)^2 ≥ (4 : ℝ)^n := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2^n) hn 2
    have hp : ((2 : ℝ)^n)^2 = (4 : ℝ)^n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rwa [hp] at h
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht1
  have hratio : ‖f t / (t : ℝ)^2‖ ≤ 27 * (3 / 4 : ℝ)^n := by
    rw [norm_div, Real.norm_of_nonneg (sq_nonneg (t : ℝ))]
    calc
      ‖f t‖ / (t : ℝ)^2 ≤ (9 * (3 : ℝ)^(n+1)) / (4 : ℝ)^n := by
        exact div_le_div₀ (by positivity) hf' (by positivity) hpow
      _ = _ := by rw [pow_succ, div_pow]; ring
  simpa only [dist_zero_right] using hratio.trans_lt
    (hB n (by dsimp [K] at hnK; omega))

theorem ae_subquadratic_process :
    ∀ᵐ x ∂rationalLaw, Tendsto (fun t : ℝ≥0 ↦ process t x / (t : ℝ)^2)
      atTop (𝓝 0) :=
  ae_eventually_uniform_window_bound.mono (fun _ hx ↦ tendsto_div_sq_of_window_bound _ hx)

end PerronWright.BrownianSubquadraticGrowth
