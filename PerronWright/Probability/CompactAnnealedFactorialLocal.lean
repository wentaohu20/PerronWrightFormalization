import PerronWright.Probability.AnnealedProfileFunctionalAsymptotic
import PerronWright.Probability.CriticalTupleEnumerationLimit

/-! # The actual compact annealed factorial expectation on ready floor sequences

All probabilistic asymptotics are derived from the actual graph law. The
ready-sequence lemma below is subsequently applied after an eventual shift;
its sampling normalizers and placements are not new analytic assumptions.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactAnnealedFactorialLocal

open AnnealedTupleResidualCounting AnnealedProfileFunctionalAsymptotic

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The paper's literal scaled ordered distinct-component expectation. -/
def localExpectation (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ)
    {q : ℕ} (x : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  (n : ℝ)^(2*(q : ℝ)/3) *
    ∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (x i) n) r : ℝ)
      ∂AnnealedGraph.law M (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n

theorem localExpectation_factorization (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n)
    (ht : 0 < CriticalScaling.time lambda n) (x : Fin q → ℝ) (r : Fin q → ℕ)
    (hk : ∀ i, 0 < CriticalScaling.size (x i) n)
    (f : Placements n (fun i ↦ CriticalScaling.size (x i) n)) (s₀ : S)
    (hweight : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n))
      (CriticalScaling.size (x i) n) (r i)) :
    localExpectation M lambda n x r =
      (∏ i, (n : ℝ)^(5/3-(r i : ℝ)) *
        (M.connectedWeight (CriticalScaling.time lambda n) (CriticalScaling.size (x i) n) (r i) /
          ((CriticalScaling.size (x i) n).factorial : ℝ))) *
      annealedResidual M lambda hk f s₀ hweight := by
  unfold localExpectation
  rw [AnnealedTupleResidualConnectedLawFormula.factorial_expectation_connectedLaw_residual_formula
    M _ ht hn _ r hk f s₀ hweight]
  have hp := CriticalTuplePrefactor.tuple_prefactor_scaled hn
    (fun i ↦ CriticalScaling.size (x i) n) r hk
    (fun i ↦ M.connectedWeight (CriticalScaling.time lambda n) (CriticalScaling.size (x i) n) (r i))
  have hi := congrArg (fun z : ℝ ↦ z *
    ∫ p, AnnealedTupleResidualConnectedLawCoordinates.residualObservable M
      (CriticalScaling.time lambda n) hk f s₀ p
      ∂AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField (CriticalScaling.time lambda n))
        (fun i ↦ CriticalScaling.size (x i) n) r hweight) hp
  unfold annealedResidual
  simp only [ProfileFiniteCollection.productLaw, AnnealedTupleResidualConnectedLawProduct.law] at hi ⊢
  convert hi using 1 <;> ring

theorem total_floor_tendsto_atTop {q : ℕ} (hq : 0 < q)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (a : ℝ) (ha : 0 < a) (hxa : ∀ m i, a ≤ x m i) :
    Tendsto (fun m ↦ ∑ i, (CriticalScaling.size (x m i) (N m) : ℝ)) atTop atTop := by
  let i₀ : Fin q := ⟨0,hq⟩
  have hk : Tendsto (fun m ↦ CriticalScaling.size (x m i₀) (N m)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [CriticalConnectedSampling.eventually_size_ge_on_window N hNt a ha K] with m hm
    exact hm _ (hxa m i₀)
  exact tendsto_atTop_mono (fun m ↦
    Finset.single_le_sum (fun i _ ↦ Nat.cast_nonneg (CriticalScaling.size (x m i) (N m)))
      (Finset.mem_univ i₀)) (tendsto_natCast_atTop_atTop.comp hk)

/-- Sequential local factorial asymptotics after removing finitely many
small sizes. No residual, field-scale or integrability premise remains. -/
theorem ready_sequence_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (R : ℕ) (hr : ∀ i, r i ≤ R)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i)))
    (hk : ∀ m i, 0 < CriticalScaling.size (x m i) (N m))
    (f : ∀ m, Placements (N m) (fun i ↦ CriticalScaling.size (x m i) (N m)))
    (hweight : ∀ m i, 0 < M.fieldConnectedWeight
      (M.scalarField (CriticalScaling.time lambda (N m))) (CriticalScaling.size (x m i) (N m)) (r i)) :
    Tendsto (fun m ↦ localExpectation M lambda (N m) (x m) r) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  let k m i := CriticalScaling.size (x m i) (N m)
  have hx (m) (i) : 0 ≤ x m i := ha.le.trans (hxa m i)
  have hsizei (m) (i) : (k m i : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ) :=
    (CriticalSizeTuple.size_le_scaled (hx m i) _).trans
      (mul_le_mul_of_nonneg_right (hxb m i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  obtain ⟨L,hL,hfield⟩ := CriticalScalarField.exists_sqrt_scalarField_bound M N hN hNt lambda b hb
  have hg : ∀ᶠ m in atTop, ∀ i, Real.sqrt (k m i : ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N m))‖ ≤ L :=
    hfield.mono (fun m hm i ↦ hm _ (hsizei m i))
  have hsize : ∀ᶠ m in atTop, (∑ i,(k m i : ℝ)) ≤ (q : ℝ)*b*(N m : ℝ)^(2/3 : ℝ) := by
    apply Eventually.of_forall
    intro m
    simpa only [k,← Nat.cast_sum] using
      CriticalSizeTuple.totalSize_le_on_window (x m) b (hx m) (hxb m)
  have hnorm := CriticalSizeTuple.totalSize_normalized_tendsto N hN hNt x hx s hxs
  let s₀ : S := Classical.choice (nonempty_of_isProbabilityMeasure M.mu)
  have hres := annealedResidual_tendsto M hM hQP R q hq L ((q : ℝ)*b) hL
    (mul_nonneg (Nat.cast_nonneg q) hb) lambda N k (fun _ ↦ r) hk f s₀ hweight hN hNt
    (total_floor_tendsto_atTop hq N hNt x a ha hxa)
    (Eventually.of_forall (fun _ ↦ hr)) hg hsize hnorm
  have hen := CriticalTupleEnumerationLimit.tuple_enumeration_tendsto M hM r N hN hNt
    x lambda a b ha hb hxa hxb s hs hxs
  have hlim := hen.mul hres
  have hid : (∏ i, FactorialDensity.sizeFactor (M.beta hM) (s i) (r i) *
      Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM*(lambda^2*s i))) *
      Real.exp (lambda*M.alpha hM*(∑ i,s i)^2/2-M.beta hM*(∑ i,s i)^3/6) =
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r := by
    rw [mul_comm]
    exact CriticalTupleEnumerationLimit.density_factorization _ _ _ s r
  rw [hid] at hlim
  apply hlim.congr'
  filter_upwards [((CriticalScaling.time_tendsto lambda).comp hNt).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm
  exact (localExpectation_factorization M lambda (hN m) hm (x m) r (hk m) (f m) s₀ (hweight m)).symm

end PerronWright.CompactAnnealedFactorialLocal
