import PerronWright.Probability.AnnealedProfileFunctionalL1
import PerronWright.Probability.PooledResidualExponential
import PerronWright.Probability.CriticalResidualScaling

/-!
# Actual centered thermal/cubic errors and their quadratic exponential

The coefficients are the literal critical time and total component size.
The errors are continuous functionals of the actual pooled sampled mark.
Their boundedness and concentration are derived, and the QP exponential
moment is the already proved actual product-law moment.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalResidual

open AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalExponent
  AnnealedProfileFunctionalL1 EmpiricalTypeMarks EmpiricalMarkConcentration
  ProjectiveFiniteCollection ProfileFiniteCollection ProjectiveKernelClosure
  BoundedConcentrationTransfer ProfileCollectionScaleMatched CriticalResidualScaling

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def profileRemainder (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (z : ℝ × ℝ × ℝ) (ν : ProbabilityMeasure S) : ℝ :=
  z.2.1 * (thermalFunctional M z.1 ν - M.alpha hM / 2) +
    z.2.2 * (gammaFunctional M z.1 ν + M.beta hM / 6)

theorem profileRemainder_joint_continuous (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Continuous (fun z : (ℝ × ℝ × ℝ) × ProbabilityMeasure S ↦ profileRemainder M hM z.1 z.2) := by
  have hc : Continuous (fun z : (ℝ × ℝ × ℝ) × ProbabilityMeasure S ↦ (z.1.1,z.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have ht := (thermalFunctional_joint_continuous M).comp hc
  have hg := (gammaFunctional_joint_continuous M).comp hc
  exact ((continuous_fst.snd.fst).mul (ht.sub continuous_const)).add
    ((continuous_fst.snd.snd).mul (hg.add continuous_const))

theorem profileRemainder_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) : profileRemainder M hM (1,a,b) (perronMark M hM) = 0 := by
  simp only [profileRemainder,thermalFunctional_one_perronMark,gammaFunctional_one_perronMark]
  ring

def residualParameter (lambda : ℝ) (n K : ℕ) : ℝ × ℝ × ℝ :=
  (CriticalScaling.time lambda n,
    (CriticalScaling.time lambda n-1)*(K:ℝ)^2/(n:ℝ), (K:ℝ)^3/(n:ℝ)^2)

theorem residualParameter_tendsto (N K : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hNt : Tendsto N atTop atTop) (lambda : ℝ) {s : ℝ}
    (hs : Tendsto (fun n ↦ (K n:ℝ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ residualParameter lambda (N n) (K n)) atTop
      (𝓝 (1,lambda*s^2,s^3)) := by
  simpa only [nhds_prod_eq,Function.comp_apply,residualParameter] using
    (CriticalScaling.time_tendsto lambda |>.comp hNt).prodMk
      ((thermal_size_coefficient_tendsto N K hN hNt lambda hs).prodMk
        (cubic_size_coefficient_tendsto N K hN hs))

def actualProfileRemainder {q : ℕ} (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) : ℝ :=
  profileRemainder M hM (residualParameter lambda n (∑ i,k i)) (pooledMark hq k hk p)

def centeredProfileExponent {q : ℕ} (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) : ℝ :=
  ((∑ i,(k i:ℝ))/(2*(n:ℝ))) * pooledQuadratic M hM hq k hk (residualKernel M) p +
    actualProfileRemainder M hM lambda n hq k hk p

/-- Actual bounded thermal/cubic sampling errors converge in L1. -/
theorem actualProfileRemainder_l1_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ)*‖g n i‖ ≤ L)
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ∫ p, |actualProfileRemainder M hM lambda (N n) hq (k n) (hk n) p|
      ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 0) := by
  have hh := pooled_jointContinuousFunctional_l1_tendsto_zero
    M hM R q hq L hL k r hk g hC hKTop hr hg
    (fun n ↦ residualParameter lambda (N n) (∑ i,k n i))
    (residualParameter_tendsto N (fun n ↦ ∑ i,k n i) hN hNt lambda hs)
    (profileRemainder M hM) (profileRemainder_joint_continuous M hM)
  simpa only [profileRemainder_perronMark,sub_zero,actualProfileRemainder] using hh

/-- Combining the actual profile errors with the genuine QP quadratic
moment gives an L1 exponential limit, without assuming UI. -/
theorem centeredProfileExponent_l1_and_mean_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
    (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S,ℝ))
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hKTop : Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ)*‖g n i‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
    {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n ↦ ∫ p, |Real.exp (centeredProfileExponent M hM lambda (N n) hq (k n) (hk n) p)-1|
      ∂productLaw M (k n) (r n) (g n) (hweight n)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ ∫ p, Real.exp (centeredProfileExponent M hM lambda (N n) hq (k n) (hk n) p)
      ∂productLaw M (k n) (r n) (g n) (hweight n)) atTop (𝓝 1) := by
  let μ n := productLaw M (k n) (r n) (g n) (hweight n)
  let γ n : ℝ := (∑ i,(k n i:ℝ))/(2*(N n:ℝ))
  let Q n (p : StateFamily (S := S) (k n)) :=
    γ n * pooledQuadratic M hM hq (k n) (hk n) (residualKernel M) p
  let Z n := actualProfileRemainder M hM lambda (N n) hq (k n) (hk n)
  let z n := residualParameter lambda (N n) (∑ i,k n i)
  have hz := residualParameter_tendsto N (fun n ↦ ∑ i,k n i) hN hNt lambda hs
  have hF := profileRemainder_joint_continuous M hM
  have hγ (n : ℕ) : 0 ≤ γ n := by dsimp only [γ]; positivity
  obtain ⟨a,f,hrep,he⟩ := residualKernel_hasRepresentation M hQP
  have hQ (n : ℕ) : Measurable (Q n) := by
    dsimp only [Q]
    rw [he]
    exact (pooledQuadratic_measurable_of_representation M hM hq (k n) (hk n) hrep).const_mul _
  have hZ (n : ℕ) : Measurable (Z n) :=
    pooled_jointContinuousFunctional_measurable hq (k n) (hk n) (z n) (profileRemainder M hM) hF
  obtain ⟨B,hB,hbound⟩ := jointContinuousFunctional_bound z hz (perronMark M hM)
    (profileRemainder M hM) hF
  simp only [profileRemainder_perronMark,sub_zero] at hbound
  have hi (n : ℕ) : Integrable (fun p ↦ Real.exp |Q n p|) (μ n) := by
    have hh := integrable_exp_pooledQuadratic M hM hq (k n) (r n) (hk n)
      (g n) (hweight n) hrep (γ n) (hγ n)
    rw [← he] at hh
    simpa only [Q,abs_mul,abs_of_nonneg (hγ n)] using hh
  have ht : Tendsto (fun n ↦ ∫ p, Real.exp |Q n p| ∂μ n) atTop (𝓝 1) := by
    have hh := residual_pooledQuadratic_exponential_tendsto_one_bjr_scale
      M hM hQP R q hq L (1/2) C hL (by norm_num) hC k r g N hk hN hNt hr hg hsize hweight
    convert hh using 1
    funext n
    apply integral_congr_ae
    filter_upwards [] with p
    rw [show |Q n p| = γ n * |pooledQuadratic M hM hq (k n) (hk n) (residualKernel M) p| by
      simp only [Q,abs_mul,abs_of_nonneg (hγ n)]]
    congr 2
    dsimp only [γ]
    ring
  have hp (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n ↦ (μ n).real {p | ε ≤ |Z n p|}) atTop (𝓝 0) := by
    have hh := pooled_jointContinuousFunctional_probability_tendsto_zero
      M hM R q hq L hL k r hk g hweight hKTop hr hg z hz (profileRemainder M hM) hF ε hε
    simpa only [profileRemainder_perronMark,sub_zero,μ,Z,z,actualProfileRemainder] using hh
  have hh := integral_abs_exp_add_sub_one_tendsto_zero μ Q Z hQ hZ B hB
    (fun n p ↦ hbound n _) hi ht hp
  exact ⟨hh,integral_exp_add_tendsto_one μ Q Z hQ hZ B hB
    (fun n p ↦ hbound n _) hi ht hp⟩

end PerronWright.AnnealedProfileFunctionalResidual
