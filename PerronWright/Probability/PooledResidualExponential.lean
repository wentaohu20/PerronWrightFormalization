import PerronWright.Probability.ProfileCollectionScaleMatched
import PerronWright.Probability.BoundedConcentrationTransfer

/-! # L1 control of the actual compact-model residual quadratic factor -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.PooledResidualExponential

open ProfileFiniteCollection ProjectiveFiniteCollection ProfileCollectionScaleMatched
  ProjectiveKernelClosure BoundedConcentrationTransfer

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual centered residual quadratic exponential tends to one in
L1 under the literal connected product law, on the full BJR size scale. -/
theorem quadraticFactor_l1_tendsto_zero_bjr_scale
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L A C : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (k r : ℕ → Fin q → ℕ) (g : ℕ → Fin q → C(S, ℝ)) (N : ℕ → ℕ)
    (hk : ∀ n i, 0 < k n i) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C * (N n : ℝ) ^ (2 / 3 : ℝ))
    (hweight : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i)) :
    Tendsto (fun n ↦ ∫ p,
      |Real.exp ((A * (∑ i, (k n i : ℝ)) / (N n : ℝ)) *
        pooledQuadratic M hM hq (k n) (hk n) (residualKernel M) p) - 1|
        ∂productLaw M (k n) (r n) (g n) (hweight n)) atTop (𝓝 0) := by
  let μ n := productLaw M (k n) (r n) (g n) (hweight n)
  let γ n : ℝ := A * (∑ i, (k n i : ℝ)) / (N n : ℝ)
  let Q n (p : StateFamily (S := S) (k n)) : ℝ :=
    γ n * pooledQuadratic M hM hq (k n) (hk n) (residualKernel M) p
  have hγ (n : ℕ) : 0 ≤ γ n := by dsimp only [γ]; positivity
  obtain ⟨a,f,hs,he⟩ := residualKernel_hasRepresentation M hQP
  have hQ (n : ℕ) : Measurable (Q n) := by
    dsimp only [Q]
    rw [he]
    exact (pooledQuadratic_measurable_of_representation M hM hq (k n) (hk n) hs).const_mul _
  have hi (n : ℕ) : Integrable (fun p ↦ Real.exp |Q n p|) (μ n) := by
    have hh := integrable_exp_pooledQuadratic M hM hq (k n) (r n) (hk n)
      (g n) (hweight n) hs (γ n) (hγ n)
    rw [← he] at hh
    simpa only [Q,abs_mul,abs_of_nonneg (hγ n)] using hh
  have ht : Tendsto (fun n ↦ ∫ p, Real.exp |Q n p| ∂μ n) atTop (𝓝 1) := by
    have hh := residual_pooledQuadratic_exponential_tendsto_one_bjr_scale
      M hM hQP R q hq L A C hL hA hC k r g N hk hN hNt hr hg hsize hweight
    simpa only [μ,Q,γ,abs_mul,abs_of_nonneg (hγ _)] using hh
  have hp (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n ↦ (μ n).real {p : StateFamily (S := S) (k n) | ε ≤ |(0 : ℝ)|})
        atTop (𝓝 0) := by
    simpa only [abs_zero,not_le_of_gt hε,Set.ofPred_false,measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have : ∀ n, IsProbabilityMeasure (μ n) := fun _ ↦ inferInstance
  have hh := integral_abs_exp_add_sub_one_tendsto_zero μ Q (fun _ _ ↦ 0) hQ
    (fun _ ↦ measurable_const) 0 (by norm_num) (by intro n p; simp) hi ht hp
  simpa only [Q,μ,γ,add_zero] using hh

end PerronWright.PooledResidualExponential
