import PerronWright.Probability.AnnealedProfileFunctionalObservable

/-!
# The actual normalized annealed residual expectation

Illegal graph patterns have zero mass under the genuine connected product
law.  The literal logarithmic Taylor/odds error and the explicit diagonal
correction have a vanishing deterministic envelope on that support.  This
transfers the proved profile exponential L1 limit to the actual residual.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalExpectation

open AnnealedProfileFunctionalObservable AnnealedProfileFunctionalFiniteError
  AnnealedProfileFunctionalResidual AnnealedResidualCriticalError
  AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedTupleResidualConnectedLawCoordinates FreshTypeCumulantExpansion
  ExactFactorialExpectation ProjectiveFiniteCollection ProfileFiniteCollection
  BoundedConcentrationTransfer

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem abs_exp_add_sub_one_le_perturbation (a b E : ℝ) (hb : |b| ≤ E) :
    |Real.exp (a+b)-1| ≤ Real.exp E * |Real.exp a-1| + Real.exp E * E := by
  have he : Real.exp (a+b)-1 = Real.exp b * (Real.exp a-1) + (Real.exp b-1) := by
    rw [Real.exp_add]
    ring
  rw [he]
  calc
    _ ≤ |Real.exp b * (Real.exp a-1)| + |Real.exp b-1| := abs_add_le _ _
    _ = Real.exp b * |Real.exp a-1| + |Real.exp b-1| := by
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp E * |Real.exp a-1| + Real.exp E * E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr ((le_abs_self b).trans hb)) (abs_nonneg _)
      · exact (abs_exp_sub_one_le_bound hb).trans
          (mul_le_mul_of_nonneg_left hb (Real.exp_pos E).le)

theorem integral_abs_perturbation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F X L : Ω → ℝ) (E : ℝ)
    (hF : Integrable F μ) (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ)
    (heq : ∀ ω, F ω = Real.exp (L ω))
    (hpert : ∀ᵐ ω ∂μ, |L ω-X ω| ≤ E) :
    (∫ ω, |F ω-1| ∂μ) ≤
      Real.exp E * (∫ ω, |Real.exp (X ω)-1| ∂μ) + Real.exp E * E := by
  have hFi := (hF.sub (integrable_const 1)).abs
  have hXi := (hX.sub (integrable_const 1)).abs
  have hUi : Integrable (fun ω ↦ Real.exp E * |Real.exp (X ω)-1| + Real.exp E * E) μ :=
    (hXi.const_mul _).add (integrable_const _)
  have hpoint : (fun ω ↦ |F ω-1|) ≤ᵐ[μ]
      (fun ω ↦ Real.exp E * |Real.exp (X ω)-1| + Real.exp E * E) := by
    filter_upwards [hpert] with ω hω
    rw [heq ω,show L ω = X ω+(L ω-X ω) by ring]
    exact abs_exp_add_sub_one_le_perturbation _ _ _ hω
  have hh := integral_mono_ae hFi hUi hpoint
  simp only [Pi.sub_apply] at hXi hh
  rw [integral_add (hXi.const_mul _) (integrable_const _),integral_const_mul,integral_const] at hh
  simpa only [probReal_univ,smul_eq_mul,one_mul] using hh

def errorEnvelope (M : CompactBJRModel S) (lambda : ℝ) (n K q R : ℕ) : ℝ :=
  finiteCorrectionEnvelope M (CriticalScaling.time lambda n) n K +
    envelope n K q R (2*‖M.kernel.toContinuousMap‖)

theorem errorEnvelope_tendsto_zero (M : CompactBJRModel S) (lambda : ℝ)
    (N K : ℕ → ℕ) (q R : ℕ) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ n in atTop, (K n:ℝ) ≤ C*(N n:ℝ)^(2/3:ℝ)) :
    Tendsto (fun n ↦ errorEnvelope M lambda (N n) (K n) q R) atTop (𝓝 0) := by
  simpa only [errorEnvelope,zero_add] using
    (finiteCorrectionEnvelope_tendsto_zero M lambda N K hN hNt hC hsize).add
      (envelope_tendsto_zero N K q R (2*‖M.kernel.toContinuousMap‖) (by positivity) hN hNt hC hsize)

/-- The literal normalized residual converges to one in L1 under the
actual scalar-field connected product law.  The support, the expansion,
and all integrability assertions are proved, not assumed. -/
theorem normalizedResidualObservable_l1_and_mean_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
      (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
      ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ∫ p, |normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p-1|
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 0) ∧
    Tendsto (fun n ↦ ∫ p, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 1) := by
  let K n : ℕ := ∑ i,k n i
  let t n := CriticalScaling.time lambda (N n)
  let g n (_ : Fin q) := M.scalarField (t n)
  let μ n := productLaw M (k n) (r n) (g n) (hweight n)
  let F n := normalizedResidualObservable M hM lambda (hk n) (f n) s₀
  let X n := centeredProfileExponent M hM lambda (N n) hq (k n) (hk n)
  let A n := fun p : StateFamily (S := S) (k n) ↦
    Real.log (residualObservable M (t n) (hk n) (f n) s₀ p) -
      (∑ i,(k n i:ℝ))^2/(2*(N n:ℝ)) - (∑ i,(k n i:ℝ))^3/(6*(N n:ℝ)^2) -
        perronExponent M hM lambda (N n) (K n)
  let E n := errorEnvelope M lambda (N n) (K n) q R
  have hsizeK : ∀ᶠ n in atTop, (K n:ℝ) ≤ C*(N n:ℝ)^(2/3:ℝ) := by
    simpa only [K,Nat.cast_sum] using hsize
  have hEt : Tendsto E atTop (𝓝 0) := errorEnvelope_tendsto_zero M lambda N K q R hN hNt hC hsizeK
  have hXt := (centeredProfileExponent_l1_and_mean_tendsto M hM hQP R q hq L C hL hC lambda
    N k r hk g hweight hN hNt hKTop hr hg hsize hs).1
  have ht : Tendsto t atTop (𝓝 1) := (CriticalScaling.time_tendsto lambda).comp hNt
  have htr := ht.eventually (Ioo_mem_nhds (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2))
  have hsmallt : Tendsto (fun n ↦ t n*‖M.kernel.toContinuousMap‖*((K n:ℝ)/(N n:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (ht.mul_const ‖M.kernel.toContinuousMap‖).mul
      (FinitePopulationLog.critical_size_ratio_tendsto_zero N K hN hNt hC hsizeK)
  have hsmall := hsmallt.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hFi : ∀ᶠ n in atTop, Integrable (F n) (μ n) := by
    filter_upwards [htr] with n hn
    exact normalizedResidualObservable_integrable M hM lambda (hN n) hn.1 (hk n) (f n) s₀ (hweight n)
  have hXi (n : ℕ) : Integrable (fun p ↦ Real.exp (X n p)) (μ n) :=
    centeredProfileExponent_exp_integrable M hM hQP lambda (N n) hq (k n) (r n) (hk n) (g n) (hweight n)
  have hpert : ∀ᶠ n in atTop, ∀ᵐ p ∂μ n, |A n p-X n p| ≤ E n := by
    filter_upwards [htr,hr,hsmall] with n htn hrn hsn
    filter_upwards [productLaw_eligible_ae M (k n) (r n) (g n) (hweight n)] with p hp
    have hsmall' : t n * exposureBound
        (I := ↥(selectedUnion (blocksOfPlacement (hk n) (f n)))) M / (N n:ℝ) ≤ 1/2 := by
      rw [exposureBound,Fintype.card_coe,selectedUnion_blocksOfPlacement_card]
      have he : t n*((K n:ℝ)*‖M.kernel.toContinuousMap‖)/(N n:ℝ) =
        t n*‖M.kernel.toContinuousMap‖*((K n:ℝ)/(N n:ℝ)) := by ring
      simpa only [K,he] using hsn.le
    exact normalizedResidualObservable_exponent_bound M hM lambda 2 (hN n) hq
      (hk n) (f n) s₀ p htn.2.le hrn hp hsmall'
  have hupper : Tendsto (fun n ↦ Real.exp (E n)*(∫ p, |Real.exp (X n p)-1| ∂μ n) +
      Real.exp (E n)*E n) atTop (𝓝 0) := by
    have he := Real.continuous_exp.tendsto 0 |>.comp hEt
    simpa only [Real.exp_zero,mul_zero,add_zero,Function.comp_apply,X,μ] using (he.mul hXt).add (he.mul hEt)
  have hL : Tendsto (fun n ↦ ∫ p, |F n p-1| ∂μ n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) _ hupper
    filter_upwards [hFi,hpert] with n hFn hpn
    exact integral_abs_perturbation_le (μ n) (F n) (X n) (A n) (E n) hFn (hXi n)
      (normalizedResidualObservable_eq_exp_log M hM lambda (hk n) (f n) s₀) hpn
  have hmean : Tendsto (fun n ↦ ∫ p, F n p ∂μ n) atTop (𝓝 1) := by
    have habs : Tendsto (fun n ↦ |(∫ p, F n p ∂μ n)-1|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _ hL
      filter_upwards [hFi] with n hFn
      have hh := abs_integral_le_integral_abs (μ := μ n) (f := fun p ↦ F n p-1)
      rw [integral_sub hFn (integrable_const 1),integral_const] at hh
      simpa only [probReal_univ,smul_eq_mul,one_mul] using hh
    rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  exact ⟨hL,hmean⟩

end PerronWright.AnnealedProfileFunctionalExpectation
