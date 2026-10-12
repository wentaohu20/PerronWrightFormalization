import PerronWright.Probability.FiniteIrreducibleFactorialMainIdentity
import PerronWright.Probability.FiniteIrreducibleFactorialDensityFloor

/-! # Genuine numeric finite factorial-density assembly

The enumerator is the literal finite connected weighted graph enumerator,
including factorials, population scale and edge scale. Its product with
the constructed Perron population *main* exponential converges uniformly
to the paper density, also for actual floor sizes and clipped critical
time. This does not assert an asymptotic for the raw random residual.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleNumericalFactorialAssembly

open FiniteIrreducibleCriticalPrefactorScaling FiniteIrreducibleCriticalTuplePrefactor
open FiniteIrreducibleFactorialMainIdentity FiniteIrreducibleFactorialDensityFloor
open FiniteIrreduciblePerronCountExpansion (mainExponent)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Only the deterministic main part of the true exact factorial formula. -/
def numericalFactor (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (n : ℕ) {q : ℕ} (k r : Fin q → ℕ) (t : ℝ) : ℝ :=
  (n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r t *
    Real.exp (mainExponent M hM (n : ℝ) ((∑ i, k i : ℕ) : ℝ) t)

theorem numericalFactor_div_density_eq_prefactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ) :
    numericalFactor M hM n k r (rawTime lambda n) /
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
        (fun i ↦ normalizedSize n (k i)) r =
      ((n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (rawTime lambda n)) /
        tupleGaussianMainTerm M hM lambda n k r := by
  rw [← tupleGaussian_mul_main_eq_density M hM lambda hn k r]
  unfold numericalFactor
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

theorem eventually_uniform_numericalFactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (rawTime lambda n) /
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r - 1| ≤ ε := by
  filter_upwards [eventually_uniform_tuple_prefactor_ratio M hM q R lambda a b ha hb hε,
    eventually_ge_atTop (1 : ℕ)] with n hratio hn k r hka hkb hr
  rw [numericalFactor_div_density_eq_prefactor_ratio M hM lambda (by omega) k r]
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
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (rawTime lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r| < ε := by
  obtain ⟨C, hC, hbound⟩ := FactorialDensity.exists_density_window_bound
    (b := b) (M.beta_pos hM) ha R
  let B := C^q * Real.exp (-M.beta hM * (a*q)^3/24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  have hη : 0 < ε/(B+1) := div_pos hε (by linarith)
  filter_upwards [eventually_uniform_numericalFactor_ratio M hM q R lambda a b ha hb hη]
    with n hn k r hka hkb hr
  have hd := FactorialDensity.density_pos (M.alpha hM) lambda (M.beta_pos hM)
    (fun i ↦ normalizedSize n (k i)) r (fun i ↦ ha.trans_le (hka i))
  have hbnd := hbound q (M.alpha hM) lambda (fun i ↦ normalizedSize n (k i)) r
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
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |numericalFactor M hM n k r (CriticalScaling.time lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r| < ε := by
  filter_upwards [eventually_uniform_numericalFactor M hM q R lambda a b ha hb hε,
    CriticalScaling.time_eq_raw_eventually lambda] with n hn ht k r hka hkb hr
  change CriticalScaling.time lambda n = rawTime lambda n at ht
  rw [ht]
  exact hn k r hka hkb hr

/-- Literal floors and the actual positive critical time have the paper
density uniformly in the whole size window and bounded surplus family. -/
theorem eventually_uniform_floor_numericalFactor_actual_time
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) → (∀ i, r i ≤ R) →
      |numericalFactor M hM n (fun i ↦ CriticalScaling.size (x i) n) r
          (CriticalScaling.time lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda x r| < ε := by
  filter_upwards [eventually_uniform_numericalFactor M hM q R lambda (a/2) b
      (by linarith) hb (show 0 < ε/2 by linarith),
    eventually_uniform_floor_density (M.alpha hM) (M.beta hM) lambda q R a b ha
      (show 0 < ε/2 by linarith),
    eventually_floor_normalized_box q a b ha,
    CriticalScaling.time_eq_raw_eventually lambda] with n hn hd hbnd ht x r hxa hxb hr
  change CriticalScaling.time lambda n = rawTime lambda n at ht
  rw [ht]
  have hw := hbnd x hxa hxb
  have he1 := hn (fun i ↦ CriticalScaling.size (x i) n) r hw.1 hw.2 hr
  have he2 := hd x r hxa hxb hr
  calc
    _ ≤ |numericalFactor M hM n (fun i ↦ CriticalScaling.size (x i) n) r (rawTime lambda n) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) r| +
        |FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda x r| := abs_sub_le _ _ _
    _ < ε/2+ε/2 := add_lt_add he1 he2
    _ = ε := by ring

/-- Any diverging ambient-size sequence and actual integer-size tuple in
the positive window inherits the literal density limit. -/
theorem tendsto_numericalFactor_actual_time
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (k : ℕ → Fin q → ℕ)
    (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hka : ∀ᶠ m in atTop, ∀ i, a ≤ normalizedSize (N m) (k m i))
    (hkb : ∀ᶠ m in atTop, ∀ i, normalizedSize (N m) (k m i) ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hks : ∀ i, Tendsto (fun m ↦ normalizedSize (N m) (k m i)) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ numericalFactor M hM (N m) (k m) r (CriticalScaling.time lambda (N m)))
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  have hd := density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r
    (fun m i ↦ normalizedSize (N m) (k m i)) s hs hks
  have he : Tendsto (fun m ↦
      numericalFactor M hM (N m) (k m) r (CriticalScaling.time lambda (N m)) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize (N m) (k m i)) r) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (eventually_uniform_numericalFactor M hM q R lambda a b ha hb hε),
      hNt.eventually (CriticalScaling.time_eq_raw_eventually lambda), hka, hkb]
      with m hm ht hma hmb
    change CriticalScaling.time lambda (N m) = rawTime lambda (N m) at ht
    rw [Real.dist_eq, sub_zero, ht]
    exact hm (k m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

/-- The paper's literal floors, including varying target coordinates,
have the numeric factorial-density limit along every diverging subsequence. -/
theorem tendsto_floor_numericalFactor_actual_time
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (x : ℕ → Fin q → ℝ)
    (hxa : ∀ᶠ m in atTop, ∀ i, a ≤ x m i)
    (hxb : ∀ᶠ m in atTop, ∀ i, x m i ≤ b)
    (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ numericalFactor M hM (N m)
      (fun i ↦ CriticalScaling.size (x m i) (N m)) r (CriticalScaling.time lambda (N m)))
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  have hd := density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r x s hs hxs
  have he : Tendsto (fun m ↦ numericalFactor M hM (N m)
      (fun i ↦ CriticalScaling.size (x m i) (N m)) r (CriticalScaling.time lambda (N m)) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (x m) r)
        atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (eventually_uniform_floor_numericalFactor_actual_time
      M hM q R lambda a b ha hb hε), hxa, hxb] with m hm hma hmb
    rw [Real.dist_eq, sub_zero]
    exact hm (x m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

end PerronWright.FiniteIrreducibleNumericalFactorialAssembly
