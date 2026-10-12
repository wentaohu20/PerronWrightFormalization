import PerronWright.Probability.FiniteIrreducibleCriticalEnumerationNormalization
import PerronWright.Probability.FiniteIrreducibleCriticalPrefactorScaling
import PerronWright.Probability.FiniteIrreducibleDeterministicConnectedLawFormula

/-!
# Genuine deterministic finite connected enumeration prefactors

The prefactor in the exact arbitrary-count factorial formula is rescaled
by the literal local graph scale. Its Gaussian size-factor product is
identified exactly and its relative error tends uniformly to zero on a
positive bounded integer-size window, for every fixed tuple order and
bounded surplus. No residual asymptotic is assumed or asserted.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleCriticalTuplePrefactor

open FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleCriticalEnumerationNormalization

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The literal numeric prefactor from the exact deterministic formula. -/
def enumerationPrefactor (M : FiniteIrreducibleModel S) (n : ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (t : ℝ) : ℝ :=
  (populationScale n k * edgeScale n k r / ∏ i, ((k i).factorial : ℝ)) *
    ∏ i, M.bjrModel.connectedWeight t (k i) (r i)

def scaledEnumerator (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n k r : ℕ) : ℝ :=
  (n : ℝ)^(5/3-(r : ℝ)) *
    (M.bjrModel.connectedWeight (rawTime lambda n) k r / (k.factorial : ℝ))

def gaussianSizeFactor (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n k r : ℕ) : ℝ :=
  FactorialDensity.sizeFactor (M.beta hM) (normalizedSize n k) r *
    Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (lambda^2 * normalizedSize n k))

def tupleGaussianMainTerm (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (k r : Fin q → ℕ) : ℝ :=
  ∏ i, gaussianSizeFactor M hM lambda n (k i) (r i)

def limitingTupleGaussianMainTerm (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {q : ℕ} (s : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  ∏ i, FactorialDensity.sizeFactor (M.beta hM) (s i) (r i) *
    Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (lambda^2 * s i))

theorem scaled_prefactor_eq_prod_scaledEnumerators (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (rawTime lambda n) =
      ∏ i, scaledEnumerator M lambda n (k i) (r i) := by
  unfold enumerationPrefactor scaledEnumerator populationScale edgeScale
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib,
    ← CriticalTuplePrefactor.critical_power_identity hn k r hk]
  ring

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem gaussianSizeFactor_pos (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (r : ℕ) :
    0 < gaussianSizeFactor M hM lambda n k r :=
  mul_pos (FactorialDensity.sizeFactor_pos (M.beta_pos hM) (normalizedSize_pos hn hk) r)
    (Real.exp_pos _)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem tupleGaussianMainTerm_pos (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    0 < tupleGaussianMainTerm M hM lambda n k r :=
  Finset.prod_pos (fun i _ ↦ gaussianSizeFactor_pos M hM lambda hn (hk i) (r i))

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem gaussianSizeFactor_eq_scaled_gaussian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (r : ℕ) :
    gaussianSizeFactor M hM lambda n k r =
      (n : ℝ)^(5/3-(r : ℝ)) * FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
        Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
          (k : ℝ) * (rawTime lambda n - 1)^2) := by
  have he : -FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (lambda^2 * normalizedSize n k) =
      -FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
        (k : ℝ) * (rawTime lambda n - 1)^2 := by
    rw [← rawTime_square_size lambda hn k]
    ring
  unfold gaussianSizeFactor
  rw [he]
  unfold normalizedSize
  rw [← CriticalLocalSizeFactor.sizeFactor_scaled_identity (M.beta hM) hk hn]

theorem scaledEnumerator_ratio_eq_factorial_divided_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (r : ℕ) :
    scaledEnumerator M lambda n k r / gaussianSizeFactor M hM lambda n k r =
      (M.bjrModel.connectedWeight (rawTime lambda n) k r / (k.factorial : ℝ)) /
        (FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
          Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
            (k : ℝ) * (rawTime lambda n - 1)^2)) := by
  rw [gaussianSizeFactor_eq_scaled_gaussian M hM lambda hn hk]
  unfold scaledEnumerator
  have hp : (n : ℝ)^(5/3-(r : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'
  have hs := (FactorialDensity.sizeFactor_pos (M.beta_pos hM) (Nat.cast_pos.mpr hk) r).ne'
  have he := (Real.exp_pos (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
    (k : ℝ) * (rawTime lambda n - 1)^2)).ne'
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

theorem scaled_prefactor_ratio_eq_prod (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {n q : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    ((n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (rawTime lambda n)) /
      tupleGaussianMainTerm M hM lambda n k r =
      ∏ i, scaledEnumerator M lambda n (k i) (r i) /
        gaussianSizeFactor M hM lambda n (k i) (r i) := by
  rw [scaled_prefactor_eq_prod_scaledEnumerators M lambda hn k r hk]
  unfold tupleGaussianMainTerm
  rw [Finset.prod_div_distrib]

/-- The actual integer-size and raw-time windows supply every input
needed by the finite Gaussian enumeration and its factorial correction. -/
theorem eventually_uniform_single_component_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : ℕ,
      a ≤ normalizedSize n k → normalizedSize n k ≤ b → r ≤ R →
      |scaledEnumerator M lambda n k r / gaussianSizeFactor M hM lambda n k r - 1| ≤ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_uniform_factorial_divided_gaussian_ratio M hM R
      (Real.sqrt b * |lambda|) (by positivity) hε)
  filter_upwards [eventually_all_sizes_ge a ha (max 1 K), eventually_ge_atTop (1 : ℕ)]
    with n hn hn1 k r hka hkb hr
  have hkpos : 0 < k := by have := hn k hka; omega
  rw [scaledEnumerator_ratio_eq_factorial_divided_ratio M hM lambda (by omega) hkpos]
  exact hK k ((le_max_right 1 K).trans (hn k hka)) r hr (rawTime lambda n)
    (rawTime_sqrt_bound lambda b hb (by omega) k hkb)

/-- Common full integer-window relative convergence for the literal
prefactor, including trees and unicycles. The tuple order is fixed but
arbitrary; all bounded surplus vectors are covered at one threshold. -/
theorem eventually_uniform_tuple_prefactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) → (∀ i, normalizedSize n (k i) ≤ b) →
      (∀ i, r i ≤ R) →
      |((n : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M n k r (rawTime lambda n)) /
        tupleGaussianMainTerm M hM lambda n k r - 1| ≤ ε := by
  obtain ⟨δ, hδ, htolerance⟩ := exists_product_tolerance q hε
  filter_upwards [eventually_uniform_single_component_ratio M hM R lambda a b ha hb hδ,
    eventually_all_sizes_ge a ha 1, eventually_ge_atTop (1 : ℕ)]
    with n hn hpos hn1 k r hka hkb hr
  rw [scaled_prefactor_ratio_eq_prod M hM lambda (by omega) k r
    (fun i ↦ by have := hpos (k i) (hka i); omega)]
  exact htolerance _ (fun i ↦ hn (k i) (r i) (hka i) (hkb i) (hr i))

/-- Every sequence in the actual full integer window inherits the
prefactor ratio limit, with varying bounded surplus and ambient size. -/
theorem tendsto_tuple_prefactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (k r : ℕ → Fin q → ℕ)
    (hka : ∀ᶠ m in atTop, ∀ i, a ≤ normalizedSize (N m) (k m i))
    (hkb : ∀ᶠ m in atTop, ∀ i, normalizedSize (N m) (k m i) ≤ b)
    (hr : ∀ᶠ m in atTop, ∀ i, r m i ≤ R) :
    Tendsto (fun m ↦
      ((N m : ℝ)^(2*(q : ℝ)/3) * enumerationPrefactor M (N m) (k m) (r m) (rawTime lambda (N m))) /
        tupleGaussianMainTerm M hM lambda (N m) (k m) (r m)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hN.eventually (eventually_uniform_tuple_prefactor_ratio M hM q R
    lambda a b ha hb (show 0 < ε/2 by linarith)), hka, hkb, hr] with m hm hma hmb hmr
  rw [Real.dist_eq]
  exact (hm (k m) (r m) hma hmb hmr).trans_lt (by linarith)

/-- The genuine prefactor itself has the literal Gaussian product limit
when the actual integer sizes converge on their normalized scale. -/
theorem tendsto_scaled_tuple_prefactor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (k : ℕ → Fin q → ℕ) (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hka : ∀ᶠ m in atTop, ∀ i, a ≤ normalizedSize (N m) (k m i))
    (hkb : ∀ᶠ m in atTop, ∀ i, normalizedSize (N m) (k m i) ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hks : ∀ i, Tendsto (fun m ↦ normalizedSize (N m) (k m i)) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ (N m : ℝ)^(2*(q : ℝ)/3) *
      enumerationPrefactor M (N m) (k m) r (rawTime lambda (N m)))
      atTop (𝓝 (limitingTupleGaussianMainTerm M hM lambda s r)) := by
  have hratio := tendsto_tuple_prefactor_ratio M hM R lambda a b ha hb N hN k
    (fun _ ↦ r) hka hkb (Eventually.of_forall (fun _ ↦ hr))
  have hmain : Tendsto (fun m ↦ tupleGaussianMainTerm M hM lambda (N m) (k m) r)
      atTop (𝓝 (limitingTupleGaussianMainTerm M hM lambda s r)) := by
    apply tendsto_finsetProd Finset.univ
    intro i _
    have hSF := (CriticalLocalSizeFactor.sizeFactor_continuousAt_positive
      (M.beta hM) (r i) (hs i)).tendsto.comp (hks i)
    have hE := (Real.continuous_exp.tendsto _).comp
      ((hks i).const_mul
        (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM * lambda^2))
    simpa only [gaussianSizeFactor, mul_assoc, Function.comp_def] using hSF.mul hE
  have hresult := hratio.mul hmain
  rw [one_mul] at hresult
  apply hresult.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop (1 : ℕ)),
    hN.eventually (eventually_all_sizes_ge a ha 1), hka] with m hn hpos hlow
  exact div_mul_cancel₀ _ (tupleGaussianMainTerm_pos M hM lambda (by omega) (k m) r
    (fun i ↦ by have := hpos (k m i) (hlow i); omega)).ne'

end PerronWright.FiniteIrreducibleCriticalTuplePrefactor

