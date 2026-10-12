import PerronWright.Probability.AnnealedProfileFunctionalResidual

/-!
# Explicit diagonal and retained-cumulant finite-size corrections

The two corrections in the literal pooled exponent are bounded uniformly
in every sampled type configuration.  Their envelope tends to zero on
the full bounded critical size scale, even if the total size stays bounded.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalFiniteError

open AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalSampled
  AnnealedProfileFunctionalExponent AnnealedProfileFunctionalResidual
  AnnealedProfileFunctionalL1 FreshTypeEmpiricalIdentities FreshTypePerronCentering
  EmpiricalTypeMarks EmpiricalMarkConcentration ProjectiveFiniteCollection ProfileFiniteCollection
  AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawCoordinates
  ProfileSquareMoment BoundedConcentrationTransfer

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def diagonalMap (M : CompactBJRModel S) : C(S,ℝ) :=
  ⟨fun x ↦ M.kernel x x,M.kernel.toContinuousMap.continuous.comp (continuous_id.prodMk continuous_id)⟩

def diagonalFunctional (M : CompactBJRModel S) := linearFunctional (diagonalMap M)

theorem diagonalFunctional_continuous (M : CompactBJRModel S) : Continuous (diagonalFunctional M) :=
  linearFunctional_continuous _

theorem diagonalFunctional_bound (M : CompactBJRModel S) (ν : ProbabilityMeasure S) :
    |diagonalFunctional M ν| ≤ ‖M.kernel.toContinuousMap‖ := by
  have hi := (diagonalMap M).continuous.integrable_of_hasCompactSupport
    isClosed_closure.isCompact (μ := (ν:Measure S))
  have ha := abs_integral_le_integral_abs (μ := (ν:Measure S)) (f := diagonalMap M)
  have hb := integral_mono hi.norm (integrable_const ‖M.kernel.toContinuousMap‖)
    (fun x ↦ M.kernel.toContinuousMap.norm_coe_le_norm (x,x))
  simp only [Real.norm_eq_abs] at hb
  rw [integral_const] at hb
  simpa only [diagonalFunctional,linearFunctional,probReal_univ,smul_eq_mul,one_mul] using ha.trans hb

def thirdCumulantBound (M : CompactBJRModel S) : ℝ :=
  ‖BoundedContinuousFunction.mkOfCompact
    (⟨thirdCumulantFunctional M,thirdCumulantFunctional_continuous M⟩ : C(ProbabilityMeasure S,ℝ))‖

theorem thirdCumulantBound_nonneg (M : CompactBJRModel S) : 0 ≤ thirdCumulantBound M := norm_nonneg _

theorem thirdCumulantFunctional_bound (M : CompactBJRModel S) (ν : ProbabilityMeasure S) :
    |thirdCumulantFunctional M ν| ≤ thirdCumulantBound M := by
  exact BoundedContinuousFunction.norm_coe_le_norm
    (BoundedContinuousFunction.mkOfCompact
      (⟨thirdCumulantFunctional M,thirdCumulantFunctional_continuous M⟩ : C(ProbabilityMeasure S,ℝ))) ν

theorem diagonalKernelSum_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) :
    diagonalKernelSum M (x ∘ e) = diagonalKernelSum M x :=
  Equiv.sum_comp e (fun i ↦ M.kernel (x i) (x i))

theorem diagonalFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i)
    (f : Placements n k) (p : StateFamily (S := S) k) :
    diagonalFunctional M (pooledMark hq k hk p) =
      (∑ i,(k i:ℝ))⁻¹ * diagonalKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) := by
  have he := diagonalKernelSum_comp_equiv M (selectedPooledEquiv hk f)
    (selectedTypes hk f (fun i ↦ (p i).1))
  rw [selectedTypes_comp_selectedPooledEquiv] at he
  unfold diagonalFunctional linearFunctional
  rw [pooledMark,typesMark_integral,pooled_card_real]
  change _ * diagonalKernelSum M (pooledTypes k p) = _
  rw [he]

def finiteCorrection {q : ℕ} (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) : ℝ :=
  let K : ℝ := ∑ i,(k i:ℝ)
  let ν := pooledMark hq k hk p
  t*K/(2*(n:ℝ)) * diagonalFunctional M ν +
    t^3*K^4/(6*(n:ℝ)^3) * thirdCumulantFunctional M ν

def finiteCorrectionEnvelope (M : CompactBJRModel S) (t : ℝ) (n K : ℕ) : ℝ :=
  |t| * ‖M.kernel.toContinuousMap‖ * ((K:ℝ)/(n:ℝ)) / 2 +
    |t|^3 * thirdCumulantBound M * ((K:ℝ)^4/(n:ℝ)^3) / 6

theorem finiteCorrectionEnvelope_nonneg (M : CompactBJRModel S) (t : ℝ) (n K : ℕ) :
    0 ≤ finiteCorrectionEnvelope M t n K := by
  unfold finiteCorrectionEnvelope
  have := thirdCumulantBound_nonneg M
  positivity

theorem finiteCorrection_bound {q : ℕ} (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) (p : StateFamily (S := S) k) :
    |finiteCorrection M t n hq k hk p| ≤ finiteCorrectionEnvelope M t n (∑ i,k i) := by
  unfold finiteCorrection
  dsimp only
  have hD := diagonalFunctional_bound M (pooledMark hq k hk p)
  have hC := thirdCumulantFunctional_bound M (pooledMark hq k hk p)
  have hK : 0 ≤ ∑ i,(k i:ℝ) := Finset.sum_nonneg (fun i _ ↦ Nat.cast_nonneg (k i))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  calc
    _ ≤ |t*(∑ i,(k i:ℝ))/(2*(n:ℝ))*diagonalFunctional M (pooledMark hq k hk p)| +
        |t^3*(∑ i,(k i:ℝ))^4/(6*(n:ℝ)^3)*thirdCumulantFunctional M (pooledMark hq k hk p)| :=
      abs_add_le _ _
    _ = |t| * (∑ i,(k i:ℝ))/(2*(n:ℝ)) * |diagonalFunctional M (pooledMark hq k hk p)| +
        |t|^3*(∑ i,(k i:ℝ))^4/(6*(n:ℝ)^3) * |thirdCumulantFunctional M (pooledMark hq k hk p)| := by
      simp only [abs_mul,abs_div,abs_pow,abs_of_nonneg hK,
        abs_of_nonneg hn,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by norm_num : (0:ℝ)<6)]
    _ ≤ |t| * (∑ i,(k i:ℝ))/(2*(n:ℝ))*‖M.kernel.toContinuousMap‖ +
        |t|^3*(∑ i,(k i:ℝ))^4/(6*(n:ℝ)^3)*thirdCumulantBound M := by
      exact add_le_add (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hC (by positivity))
    _ = _ := by unfold finiteCorrectionEnvelope; rw [Nat.cast_sum]; ring

/-- The retained fourth-size coefficient tends to zero directly from the
proved deterministic critical-scale fourth-order bound. -/
theorem fourth_size_ratio_tendsto_zero (N K : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hNt : Tendsto N atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ n in atTop, (K n:ℝ) ≤ C*(N n:ℝ)^(2/3:ℝ)) :
    Tendsto (fun n ↦ (K n:ℝ)^4/(N n:ℝ)^3) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp
    (tendsto_natCast_atTop_atTop.comp hNt)
  have hh : Tendsto (fun n ↦ 2*(K n:ℝ)^4/(N n:ℝ)^3) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity))
      (hsize.mono (fun n hn ↦ FinitePopulationLog.fourth_remainder_bound (hN n) hC hn))
      (by simpa only [mul_zero,Function.comp_apply] using hp.const_mul (2*C^4))
  have hh2 := hh.const_mul (1/2:ℝ)
  simp only [mul_zero] at hh2
  exact hh2.congr' (Eventually.of_forall (fun n ↦ by dsimp only; ring))

theorem finiteCorrectionEnvelope_tendsto_zero (M : CompactBJRModel S) (lambda : ℝ)
    (N K : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ n in atTop, (K n:ℝ) ≤ C*(N n:ℝ)^(2/3:ℝ)) :
    Tendsto (fun n ↦ finiteCorrectionEnvelope M (CriticalScaling.time lambda (N n)) (N n) (K n))
      atTop (𝓝 0) := by
  have ht := (CriticalScaling.time_tendsto lambda |>.comp hNt).abs
  have h1 := FinitePopulationLog.critical_size_ratio_tendsto_zero N K hN hNt hC hsize
  have h4 := fourth_size_ratio_tendsto_zero N K hN hNt hC hsize
  have hh := (((ht.mul_const ‖M.kernel.toContinuousMap‖).mul h1).div_const 2).add
    ((((ht.pow 3).mul_const (thirdCumulantBound M)).mul h4).div_const 6)
  simpa only [finiteCorrectionEnvelope,mul_zero,zero_div,add_zero,Function.comp_apply] using hh

/-- Terminal exact relation between the selected cumulant exponent and
the centered profile exponent whose actual expectation is controlled. -/
theorem pooledCumulantExponent_eq_centered_add_finiteCorrection {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) :
    let K : ℝ := ∑ i,(k i:ℝ)
    let t := CriticalScaling.time lambda n
    pooledCumulantExponent M hM t hq hk f p - M.alpha hM/2*((t-1)*K^2/(n:ℝ)) +
      M.beta hM/6*(K^3/(n:ℝ)^2) =
      centeredProfileExponent M hM lambda n hq k hk p + finiteCorrection M t n hq k hk p := by
  dsimp only
  rw [pooledCumulantExponent_decomposition]
  unfold centeredProfileExponent actualProfileRemainder profileRemainder residualParameter finiteCorrection
  dsimp only
  rw [diagonalFunctional_pooledMark_eq_selected M hq hk f p,Nat.cast_sum]
  have hK0 := (totalSize_pos hq k hk).ne'
  field_simp
  ring

end PerronWright.AnnealedProfileFunctionalFiniteError
