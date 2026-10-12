import PerronWright.Probability.ProjectiveFiniteCollection
import PerronWright.Probability.ProjectiveKernelClosure

/-! # Scale-matched exponential moments for actual pooled component laws -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProfileCollectionScaleMatched

open ConnectedTypeLaw ProjectiveKernel ProfileSquareMoment
open ProfileFiniteCollection ProjectiveFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem integral_pooledQuadratic_finite_size_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {q : ℕ} (hq : 0 < q) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (g : Fin q → C(S, ℝ))
    (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i))
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) {B : ℝ}
    (hbudget : ∑' j, |a j| * ‖f j‖ ^ 2 ≤ B) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ (∫ p, Real.exp (γ * |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|)
        ∂productLaw M k r g hC) - 1 ∧
      (∫ p, Real.exp (γ * |pooledQuadratic M hM hq k hk (∑' j, a j • square (f j)) p|)
        ∂productLaw M k r g hC) - 1 ≤ Real.exp (4 * γ * (∑ i, (k i : ℝ)) * B) - 1 := by
  have hi := integrable_exp_pooledQuadratic M hM hq k r hk g hC hs γ hγ
  have hl := integral_mono (integrable_const (1 : ℝ)) hi
    (fun p ↦ Real.one_le_exp_iff.mpr (mul_nonneg hγ (abs_nonneg _)))
  have hu := integral_mono hi (integrable_const (Real.exp (4 * γ * (∑ i, (k i : ℝ)) * B)))
    (fun p ↦ Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_left (pooledQuadratic_abs_le_budget M hM hq k hk hs hbudget p) hγ
      exact hm.trans_eq (by ring)))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl hu
  exact ⟨by linarith, by linarith⟩

/-- The true pooled empirical statistic tends to one exponentially under
scale matching. No diverging-size assumption is imposed on the individual
components or their total; bounded and mixed cases are included. -/
theorem pooledQuadratic_exponential_tendsto_one_scale_matched
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (k r : ℕ → Fin q → ℕ) (g : ℕ → Fin q → C(S, ℝ))
    (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → C(S, ℝ)) (γ : ℕ → ℝ)
    (hk : ∀ n i, 0 < k n i) (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (hs : ∀ n, Summable (fun j ↦ |a n j| * ‖f n j‖ ^ 2))
    (hbudget : ∀ n, ∑' j, |a n j| * ‖f n j‖ ^ 2 ≤ B)
    (hγ : ∀ n, 0 ≤ γ n) (hγt : Tendsto γ atTop (𝓝 0))
    (hγscale : ∀ᶠ n in atTop, γ n ≤ A / Real.sqrt (∑ i, (k n i : ℝ)))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i)) :
    Tendsto (fun n ↦ ∫ p, Real.exp (γ n *
      |pooledQuadratic M hM hq (k n) (hk n) (∑' j, a n j • square (f n j)) p|)
        ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 1) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_pooledQuadratic_exponential_bound M hM R q hq L A B hL hA hB
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hDlim : Tendsto (fun K : ℕ ↦ D / Real.sqrt (K : ℝ)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    have he (K : ℕ) : D / Real.sqrt (K : ℝ) = D * (K : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    simp_rw [he]
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hp
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hDlim.eventually (Iio_mem_nhds hδ))
  have hsmallLim : Tendsto (fun n ↦ Real.exp (4 * γ n * (K₀ : ℝ) * B) - 1) atTop (𝓝 0) := by
    have ht : Tendsto (fun n ↦ 4 * γ n * (K₀ : ℝ) * B) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (((hγt.const_mul 4).mul_const (K₀ : ℝ)).mul_const B)
    have hm := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1
    simpa only [Function.comp_apply, mul_zero, zero_mul, Real.exp_zero, sub_self] using hm
  filter_upwards [hr, hg, hγscale, hsmallLim.eventually (Iio_mem_nhds hδ)]
    with n hnr hng hnscale hnsmall
  have hfinite := integral_pooledQuadratic_finite_size_bound M hM hq (k n) (r n) (hk n) (g n)
    (hC n) (hs n) (hbudget n) (γ n) (hγ n)
  rw [Real.dist_eq, abs_of_nonneg hfinite.1]
  by_cases hkn : K₀ ≤ ∑ i, k n i
  · have hupper := (hbound (k n) (r n) (hk n) hnr (g n) hng (a n) (f n) (hs n) (hbudget n) (hC n)).2
    have hiγ := integrable_exp_pooledQuadratic M hM hq (k n) (r n) (hk n) (g n) (hC n) (hs n) (γ n) (hγ n)
    have hiA := integrable_exp_pooledQuadratic M hM hq (k n) (r n) (hk n) (g n) (hC n) (hs n)
      (A / Real.sqrt (∑ i, (k n i : ℝ))) (by positivity)
    have hmon := integral_mono hiγ hiA (fun p ↦ Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hnscale (abs_nonneg _)))
    have hsmall := hK₀ (∑ i, k n i) hkn
    rw [Nat.cast_sum] at hsmall
    linarith only [hupper, hmon, hsmall]
  · have hknreal : (∑ i, (k n i : ℝ)) ≤ K₀ := by
      rw [← Nat.cast_sum]
      exact_mod_cast (show ∑ i, k n i ≤ K₀ by omega)
    have hmul := mul_le_mul_of_nonneg_left hknreal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hγ n))
    have hmulB := mul_le_mul_of_nonneg_right hmul hB
    have hsmall := Real.exp_le_exp.mpr hmulB
    linarith only [hfinite.2, hsmall, hnsmall]

/-- The literal BJR coefficient `A kΣ/N` for a fixed finite collection,
uniformly under `kΣ ≤ C₀ N^(2/3)`, including all bounded-size cases. -/
theorem pooledQuadratic_exponential_tendsto_one_bjr_scale
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q)
    (L A B C₀ : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (k r : ℕ → Fin q → ℕ) (g : ℕ → Fin q → C(S, ℝ))
    (N : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → C(S, ℝ))
    (hk : ∀ n i, 0 < k n i) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (hs : ∀ n, Summable (fun j ↦ |a n j| * ‖f n j‖ ^ 2))
    (hbudget : ∀ n, ∑' j, |a n j| * ‖f n j‖ ^ 2 ≤ B)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C₀ * (N n : ℝ) ^ (2 / 3 : ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A * (∑ i, (k n i : ℝ)) / (N n : ℝ)) *
      |pooledQuadratic M hM hq (k n) (hk n) (∑' j, a n j • square (f n j)) p|)
        ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 1) := by
  let γ : ℕ → ℝ := fun n ↦ A * (∑ i, (k n i : ℝ)) / (N n : ℝ)
  have hγ (n : ℕ) : 0 ≤ γ n := by dsimp only [γ]; positivity
  have hcoeff : ∀ᶠ n in atTop,
      γ n ≤ (A * C₀) * (N n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      γ n ≤ (A * C₀ ^ (3 / 2 : ℝ)) / Real.sqrt (∑ i, (k n i : ℝ)) := by
    filter_upwards [hsize] with n hn
    exact ProfileScaleMatched.coefficient_bounds (totalSize_pos hq (k n) (hk n))
      (by exact_mod_cast hN n) hC₀ hA hn
  have hup : Tendsto (fun n ↦ (A * C₀) * (N n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul hp
  have hγt : Tendsto γ atTop (𝓝 0) := squeeze_zero'
    (Eventually.of_forall hγ) (hcoeff.mono (fun _ hn ↦ hn.1)) hup
  exact pooledQuadratic_exponential_tendsto_one_scale_matched M hM R q hq L
    (A * C₀ ^ (3 / 2 : ℝ)) B hL (mul_nonneg hA (Real.rpow_nonneg hC₀ _)) hB
    k r g a f γ hk hr hg hs hbudget hγ hγt (hcoeff.mono (fun _ hn ↦ hn.2)) hC

/-- Terminal compact QP bound for the actual pooled residual statistic.
Only the paper's original QP assumption is used to obtain its projective
representation, through the proved kernel-square closure. -/
theorem exists_uniform_residual_pooledQuadratic_exponential_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
      (∀ i, r i ≤ R) → ∀ g : Fin q → C(S, ℝ), (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      0 ≤ (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
          |pooledQuadratic M hM hq k hk (ProjectiveKernelClosure.residualKernel M) p|)
            ∂productLaw M k r g hC) - 1 ∧
        (∫ p, Real.exp ((A / Real.sqrt (∑ i, (k i : ℝ))) *
          |pooledQuadratic M hM hq k hk (ProjectiveKernelClosure.residualKernel M) p|)
            ∂productLaw M k r g hC) - 1 ≤ D / Real.sqrt (∑ i, (k i : ℝ)) := by
  obtain ⟨a, f, hs, he⟩ := ProjectiveKernelClosure.residualKernel_hasRepresentation M hQP
  let B : ℝ := ∑' j, |a j| * ‖f j‖ ^ 2
  have hB : 0 ≤ B := tsum_nonneg (fun _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
  obtain ⟨D, hD, hb⟩ := exists_uniform_pooledQuadratic_exponential_bound M hM R q hq L A B hL hA hB
  refine ⟨D, hD, ?_⟩
  intro k r hk hr g hg hC
  rw [he]
  exact hb k r hk hr g hg a f hs le_rfl hC

/-- The paper's compact QP BJR-scale conclusion for the genuine pooled
empirical double integral and the actual connected product law. -/
theorem residual_pooledQuadratic_exponential_tendsto_one_bjr_scale
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (R q : ℕ) (hq : 0 < q) (L A C₀ : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hC₀ : 0 ≤ C₀)
    (k r : ℕ → Fin q → ℕ) (g : ℕ → Fin q → C(S, ℝ)) (N : ℕ → ℕ)
    (hk : ∀ n i, 0 < k n i) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (hsize : ∀ᶠ n in atTop, (∑ i, (k n i : ℝ)) ≤ C₀ * (N n : ℝ) ^ (2 / 3 : ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A * (∑ i, (k n i : ℝ)) / (N n : ℝ)) *
      |pooledQuadratic M hM hq (k n) (hk n) (ProjectiveKernelClosure.residualKernel M) p|)
        ∂productLaw M (k n) (r n) (g n) (hC n)) atTop (𝓝 1) := by
  obtain ⟨a, f, hs, he⟩ := ProjectiveKernelClosure.residualKernel_hasRepresentation M hQP
  let B : ℝ := ∑' j, |a j| * ‖f j‖ ^ 2
  have hB : 0 ≤ B := tsum_nonneg (fun _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
  rw [he]
  exact pooledQuadratic_exponential_tendsto_one_bjr_scale M hM R q hq L A B C₀ hL hA hB hC₀
    k r g N (fun _ ↦ a) (fun _ ↦ f) hk hN hNt hr hg (fun _ ↦ hs) (fun _ ↦ le_rfl) hsize hC

end PerronWright.ProfileCollectionScaleMatched
