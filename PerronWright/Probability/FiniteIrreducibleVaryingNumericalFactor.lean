import PerronWright.Probability.FiniteIrreducibleNumericalFactorialAssembly
import PerronWright.Probability.FiniteIrreducibleVaryingCriticalTime

/-! # Actual enumeration and numerical factors for varying critical times

The Gaussian enumerator estimate is applied with the single fixed radius
sqrt(b) (abs(lambda)+1), derived from convergence of the literal parameter.
This controls the actual graph prefactor, rather than a limit-law parameter map.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleVaryingNumericalFactor

open FiniteIrreducibleCriticalPrefactorScaling FiniteIrreducibleCriticalTuplePrefactor
open FiniteIrreducibleNumericalFactorialAssembly
open FiniteIrreducibleCriticalEnumerationNormalization
open FiniteIrreducibleVaryingCriticalTime

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem eventually_uniform_single_component_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : ℕ,
      a ≤ normalizedSize n k → normalizedSize n k ≤ b → r ≤ R →
      |scaledEnumerator M (ell n) n k r / gaussianSizeFactor M hM (ell n) n k r - 1| ≤ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_uniform_factorial_divided_gaussian_ratio M hM R
      (Real.sqrt b * (|lambda| + 1)) (by positivity) hε)
  filter_upwards [eventually_all_sizes_ge a ha (max 1 K), eventually_ge_atTop (1 : ℕ), eventually_parameter_bound ell lambda hl]
    with n hn hn1 hpar k r hka hkb hr
  have hkpos : 0 < k := by have := hn k hka; omega
  rw [scaledEnumerator_ratio_eq_factorial_divided_ratio M hM (ell n) (by omega) hkpos]
  exact hK k ((le_max_right 1 K).trans (hn k hka)) r hr (rawTime (ell n) n)
    ((rawTime_sqrt_bound (ell n) b hb (by omega) k hkb).trans
      (mul_le_mul_of_nonneg_left hpar (Real.sqrt_nonneg b)))

/-- Common full integer-window relative convergence for the literal
prefactor, including trees and unicycles. The tuple order is fixed but
arbitrary; all bounded surplus vectors are covered at one threshold. -/
theorem eventually_uniform_tuple_prefactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |((n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (rawTime (ell n) n)) /
        tupleGaussianMainTerm M hM (ell n) n k r - 1| ≤ ε := by
  obtain ⟨δ, hδ, htolerance⟩ := exists_product_tolerance q hε
  filter_upwards [eventually_uniform_single_component_ratio M hM R ell lambda a b hl ha hb hδ,
    eventually_all_sizes_ge a ha 1, eventually_ge_atTop (1 : ℕ)]
    with n hn hpos hn1 k r hka hkb hr
  rw [scaled_prefactor_ratio_eq_prod M hM (ell n) (by omega) k r
    (fun i ↦ by have := hpos (k i) (hka i); omega)]
  exact htolerance _ (fun i ↦ hn (k i) (r i) (hka i) (hkb i) (hr i))

theorem eventually_uniform_numericalFactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (rawTime (ell n) n) /
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
          (fun i ↦ normalizedSize n (k i)) r - 1| ≤ ε := by
  filter_upwards [eventually_uniform_tuple_prefactor_ratio M hM q R ell lambda a b hl ha hb hε,
    eventually_ge_atTop (1 : ℕ)] with n hratio hn k r hka hkb hr
  rw [numericalFactor_div_density_eq_prefactor_ratio M hM (ell n) (by omega) k r]
  exact hratio k r hka hkb hr

private theorem abs_error_le {A d B η : ℝ} (hd : 0 < d) (hB : d ≤ B)
    (hη : 0 ≤ η) (hr : |A/d-1| ≤ η) : |A-d| ≤ η*B := by
  have he : A-d = (A/d-1)*d := by field_simp
  rw [he, abs_mul, abs_of_pos hd]
  exact (mul_le_mul_of_nonneg_right hr hd.le).trans (mul_le_mul_of_nonneg_left hB hη)

/-- Uniform absolute convergence on the full actual integer-size window.
The bound is derived from continuous actual size factors, not postulated. -/
theorem eventually_uniform_numericalFactor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (rawTime (ell n) n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
          (fun i ↦ normalizedSize n (k i)) r| < ε := by
  obtain ⟨C, hC, hbound⟩ := FactorialDensity.exists_density_window_bound
    (b := b) (M.beta_pos hM) ha R
  let B := C^q * Real.exp (-M.beta hM * (a*q)^3/24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  have hη : 0 < ε/(B+1) := div_pos hε (by linarith)
  filter_upwards [eventually_uniform_numericalFactor_ratio M hM q R ell lambda a b hl ha hb hη]
    with n hn k r hka hkb hr
  have hd := FactorialDensity.density_pos (M.alpha hM) (ell n) (M.beta_pos hM)
    (fun i ↦ normalizedSize n (k i)) r (fun i ↦ ha.trans_le (hka i))
  have hbnd := hbound q (M.alpha hM) (ell n) (fun i ↦ normalizedSize n (k i)) r
    (fun i ↦ ⟨hka i, hkb i⟩) hr
  have he := abs_error_le hd hbnd hη.le (hn k r hka hkb hr)
  apply he.trans_lt
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < B+1)).mpr
  nlinarith

/-- The true clipped critical time agrees eventually, uniformly for all
integer tuples, with the raw-time numerical density approximation. -/
theorem eventually_uniform_numericalFactor_actual_time
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (CriticalScaling.time (ell n) n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) (ell n)
          (fun i ↦ normalizedSize n (k i)) r| < ε := by
  filter_upwards [eventually_uniform_numericalFactor M hM q R ell lambda a b hl ha hb hε,
    eventually_time_eq_raw ell lambda hl] with n hn ht k r hka hkb hr
  change CriticalScaling.time (ell n) n = rawTime (ell n) n at ht
  rw [ht]
  exact hn k r hka hkb hr


end PerronWright.FiniteIrreducibleVaryingNumericalFactor
