import PerronWright.Probability.AnnealedMarkedFactorialFormula
import PerronWright.Probability.CompactAnnealedFactorialLocal

/-!
# Genuine compact marked local factorial asymptotics

The literal typed-graph marked count is exactly the unmarked expectation
times the genuine residual-weighted mark-test expectation.  This identity,
proved from the exact marked formula, joins the actual moving-floor limit
to the actual component-wise weak-mark concentration.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactAnnealedMarkedFactorialLocal

open AnnealedMarkedFactorialCounting AnnealedMarkedFactorialFormula
  AnnealedMarkedResidualLaw AnnealedMarkedResidualConcentration AnnealedMarkedResidualTests
  AnnealedProfileFunctionalObservable AnnealedTupleResidualCounting
  AnnealedTupleResidualConnectedLawCoordinates ProfileFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def localMarkedExpectation (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ)
    {q : ℕ} (x : Fin q → ℝ) (r : Fin q → ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  (n:ℝ)^(2*(q:ℝ)/3) * ∫ p,
    markedCount p.1 (AnnealedTypedGraph.graph p) (fun i ↦ CriticalScaling.size (x i) n) r Ψ
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n

/-- Division by the actual residual expectation cancels the deterministic
normalization exactly, even on a zero-time finite prefix. -/
theorem rawResidual_integral_eq_mass_mul_weightedLawIntegral {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (G : StateFamily (S := S) k → ℝ) :
    (∫ p, residualObservable M (CriticalScaling.time lambda n) hk f s₀ p * G p
      ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight) =
      (∫ p, residualObservable M (CriticalScaling.time lambda n) hk f s₀ p
        ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight) *
          ∫ p, G p ∂(weightedLaw M hM lambda hn hk f s₀ hweight).toMeasure := by
  let μ := productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hweight
  let c := Real.exp (-((∑ i,(k i:ℝ))^2/(2*(n:ℝ))) -
    (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) - perronExponent M hM lambda n (∑ i,k i))
  let R := residualObservable M (CriticalScaling.time lambda n) hk f s₀
  have hc : c ≠ 0 := (Real.exp_pos _).ne'
  have hd : (∫ p, normalizedResidualObservable M hM lambda hk f s₀ p ∂μ) = c * ∫ p, R p ∂μ :=
    integral_const_mul c R
  have hn' : (∫ p, normalizedResidualObservable M hM lambda hk f s₀ p * G p ∂μ) =
      c * ∫ p, R p * G p ∂μ := by
    change (∫ p, (c*R p)*G p ∂μ) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  have hz : (∫ p, R p ∂μ) ≠ 0 := by
    intro hz
    have hh := (residualExpectation_pos M hM lambda hn hk f s₀ hweight).ne'
    apply hh
    rw [hd,hz,mul_zero]
  have he := weightedLaw_integral M hM lambda hn hk f s₀ hweight G
  rw [hd,hn'] at he
  change (∫ p, R p*G p ∂μ) = (∫ p, R p ∂μ) * _
  rw [he]
  field_simp [hc,hz]

/-- Finite-n marked/unmarked factorization derived from both actual graph
formulas and the genuine weighted probability law, not assumed. -/
theorem localMarkedExpectation_factorization (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (ht : 0 < CriticalScaling.time lambda n)
    (x : Fin q → ℝ) (r : Fin q → ℕ) (hk : ∀ i, 0 < CriticalScaling.size (x i) n)
    (f : Placements n (fun i ↦ CriticalScaling.size (x i) n)) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n))
      (CriticalScaling.size (x i) n) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    localMarkedExpectation M lambda n x r Ψ = CompactAnnealedFactorialLocal.localExpectation M lambda n x r *
      ∫ p, Ψ (componentMarks hk p) ∂(weightedLaw M hM lambda hn hk f s₀ hweight).toMeasure := by
  unfold localMarkedExpectation CompactAnnealedFactorialLocal.localExpectation
  rw [markedFactorial_expectation_connectedLaw_residual_formula M _ ht hn _ r hk f s₀ hweight Ψ hΨ,
    AnnealedTupleResidualConnectedLawFormula.factorial_expectation_connectedLaw_residual_formula M _ ht hn _ r hk f s₀ hweight]
  have he := rawResidual_integral_eq_mass_mul_weightedLawIntegral M hM lambda hn hk f s₀ hweight
    (fun p ↦ Ψ (componentMarks hk p))
  simp only [productLaw,AnnealedTupleResidualConnectedLawProduct.law] at he ⊢
  rw [he]
  ring

/-- Moving-floor marked local factorial limit on ready positive sequences.
Every empirical mark concentrates separately under the actual law. -/
theorem ready_marked_sequence_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (R : ℕ) (hr : ∀ i, r i ≤ R)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i) (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i)))
    (hk : ∀ m i, 0 < CriticalScaling.size (x m i) (N m))
    (f : ∀ m, Placements (N m) (fun i ↦ CriticalScaling.size (x m i) (N m)))
    (hweight : ∀ m i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N m)))
      (CriticalScaling.size (x m i) (N m)) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun m ↦ localMarkedExpectation M lambda (N m) (x m) r Ψ) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r * Ψ (perronMarks M hM q))) := by
  let k m i := CriticalScaling.size (x m i) (N m)
  have hx (m) (i) : 0 ≤ x m i := ha.le.trans (hxa m i)
  have hsizei (m) (i) : (k m i:ℝ) ≤ b*(N m:ℝ)^(2/3:ℝ) :=
    (CriticalSizeTuple.size_le_scaled (hx m i) _).trans
      (mul_le_mul_of_nonneg_right (hxb m i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hkTop (i : Fin q) : Tendsto (fun m ↦ k m i) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [CriticalConnectedSampling.eventually_size_ge_on_window N hNt a ha K] with m hm
    exact hm _ (hxa m i)
  obtain ⟨L,hL,hfield⟩ := CriticalScalarField.exists_sqrt_scalarField_bound M N hN hNt lambda b hb
  have hg : ∀ᶠ m in atTop, ∀ i, Real.sqrt (k m i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N m))‖ ≤ L := hfield.mono (fun m hm i ↦ hm _ (hsizei m i))
  have hsize : ∀ᶠ m in atTop, (∑ i,(k m i:ℝ)) ≤ (q:ℝ)*b*(N m:ℝ)^(2/3:ℝ) := by
    apply Eventually.of_forall
    intro m
    simpa only [k,← Nat.cast_sum] using CriticalSizeTuple.totalSize_le_on_window (x m) b (hx m) (hxb m)
  have hnorm := CriticalSizeTuple.totalSize_normalized_tendsto N hN hNt x hx s hxs
  let s₀ : S := Classical.choice (nonempty_of_isProbabilityMeasure M.mu)
  have hm := weightedLaw_jointContinuousTest_integral_tendsto M hM hQP R q hq L ((q:ℝ)*b) hL
    (mul_nonneg (Nat.cast_nonneg q) hb) lambda N k (fun _ ↦ r) hk f s₀ hweight hN hNt hkTop
    (Eventually.of_forall (fun _ ↦ hr)) hg hsize hnorm Ψ hΨ
  have hu := CompactAnnealedFactorialLocal.ready_sequence_tendsto M hM hQP hq r R hr N hN hNt x
    lambda a b ha hb hxa hxb s hs hxs hk f hweight
  apply (hu.mul hm).congr'
  filter_upwards [((CriticalScaling.time_tendsto lambda).comp hNt).eventually
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))] with m hmt
  exact (localMarkedExpectation_factorization M hM lambda (hN m) hmt (x m) r (hk m) (f m) s₀ (hweight m) Ψ hΨ).symm

end PerronWright.CompactAnnealedMarkedFactorialLocal
