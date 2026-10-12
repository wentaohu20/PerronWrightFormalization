import PerronWright.Probability.ProfileSquareSeries
import PerronWright.Probability.ProjectiveQuadratic

/-!
# Actual projective quadratic exponential uniform integrability

The statistic is the literal empirical-versus-Perron double integral.
Its proved feature-square identity is converted to square-root scale,
then dominated by the countable feature-square moment bound.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProjectiveExponential

open ProfileLaplace ProfileSquareMoment ProfileSquareSeries ProjectiveKernel ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual quadratic empirical statistic of a nonempty connected
sample, using its full literal vertex set. -/
def componentQuadratic (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (H : C(S × S, ℝ)) (p : State S k) : ℝ := by
  let : NeZero k := ⟨hk.ne'⟩
  exact empiricalQuadratic M hM p.1 Finset.univ Finset.univ_nonempty H

/-- The actual double integral equals the countable sum of feature
squares on the component square-root scale. -/
theorem componentQuadratic_eq_tsum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (p : State S k) :
    componentQuadratic M hM hk (∑' j, a j • square (f j)) p =
      ∑' j, a j * (scaledSum M hM (f j) p) ^ 2 := by
  let : NeZero k := ⟨hk.ne'⟩
  have he := empiricalQuadratic_eq_tsum M hM p.1 Finset.univ Finset.univ_nonempty hs
  change componentQuadratic M hM hk (∑' j, a j • square (f j)) p = _ at he
  simp only [Finset.card_univ, Fintype.card_fin] at he
  rw [← tsum_mul_left] at he
  refine he.trans (tsum_congr ?_)
  intro j
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hsqrt := Real.sq_sqrt hkreal.le
  unfold scaledSum centeredSum typeSum
  rw [div_pow, hsqrt]
  field_simp [hkreal.ne']

theorem scaled_feature_square_bound (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (a : ℝ) (f : C(S, ℝ)) (p : State S k) :
    ‖a * (scaledSum M hM f p) ^ 2‖ ≤ 4 * (k : ℝ) * (|a| * ‖f‖ ^ 2) := by
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast hk.le
  have hsqrt := Real.sq_sqrt hkreal
  have hsq := pow_le_pow_left₀ (abs_nonneg (scaledSum M hM f p))
    (scaledSum_abs_le M hM hk f p) 2
  rw [sq_abs] at hsq
  have hsq' : (scaledSum M hM f p) ^ 2 ≤ 4 * (k : ℝ) * ‖f‖ ^ 2 := by
    calc
      _ ≤ (2 * Real.sqrt (k : ℝ) * ‖f‖) ^ 2 := hsq
      _ = _ := by rw [mul_pow, mul_pow, hsqrt]; ring
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul_of_nonneg_left hsq' (abs_nonneg a)).trans_eq (by ring)

theorem summable_scaled_feature_squares (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (p : State S k) :
    Summable (fun j ↦ a j * (scaledSum M hM (f j) p) ^ 2) :=
  (hs.mul_left (4 * (k : ℝ))).of_norm_bounded
    (fun j ↦ scaled_feature_square_bound M hM hk (a j) (f j) p)

theorem componentQuadratic_abs_le_feature_sum (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {k : ℕ} (hk : 0 < k)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (p : State S k) :
    |componentQuadratic M hM hk (∑' j, a j • square (f j)) p| ≤
      ∑' j, |a j| * (scaledSum M hM (f j) p) ^ 2 := by
  rw [componentQuadratic_eq_tsum M hM hk hs]
  have hs' := (summable_scaled_feature_squares M hM hk hs p).abs
  have h := norm_tsum_le_tsum_norm (f := fun j ↦ a j * (scaledSum M hM (f j) p) ^ 2)
    (by simpa only [Real.norm_eq_abs] using hs')
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs] using h

theorem componentQuadratic_measurable_of_representation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {k : ℕ} (hk : 0 < k)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    Measurable (componentQuadratic M hM hk (∑' j, a j • square (f j))) := by
  have he : componentQuadratic M hM hk (∑' j, a j • square (f j)) =
      fun p ↦ ∑' j, a j * (scaledSum M hM (f j) p) ^ 2 := by
    funext p
    exact componentQuadratic_eq_tsum M hM hk hs p
  rw [he]
  exact Measurable.tsum (fun j ↦ ((scaledSum_measurable M hM (f j)).pow_const 2).const_mul _)

theorem integrable_exp_componentQuadratic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) (r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (A : ℝ) (hA : 0 ≤ A) :
    Integrable (fun p ↦ Real.exp ((A / Real.sqrt (k : ℝ)) *
      |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|))
        (law M g k r hC) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have habs : Measurable (fun p : State S k ↦
      |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|) := by
    simpa only [Real.norm_eq_abs] using
      (componentQuadratic_measurable_of_representation M hM hk hs).norm
  apply integrable_of_measurable_abs_le (law M g k r hC)
    (B := Real.exp ((A / Real.sqrt (k : ℝ)) *
      (4 * (k : ℝ) * ∑' j, |a j| * ‖f j‖ ^ 2))) (habs.const_mul _).exp
  intro p
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hA hq.le)
  have hmaj := componentQuadratic_abs_le_feature_sum M hM hk hs p
  have hsabs : Summable (fun j ↦ |a j| * (scaledSum M hM (f j) p) ^ 2) := by
    simpa only [abs_mul, abs_pow, sq_abs] using
      (summable_scaled_feature_squares M hM hk hs p).abs
  calc
    _ ≤ ∑' j, |a j| * (scaledSum M hM (f j) p) ^ 2 := hmaj
    _ ≤ ∑' j, 4 * (k : ℝ) * (|a j| * ‖f j‖ ^ 2) :=
      hsabs.tsum_le_tsum (fun j ↦ by
        simpa only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs] using
          scaled_feature_square_bound M hM hk (a j) (f j) p) (hs.mul_left (4 * (k : ℝ)))
    _ = _ := tsum_mul_left

theorem componentQuadratic_abs_le_budget (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {k : ℕ} (hk : 0 < k)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) {B : ℝ}
    (hbudget : ∑' j, |a j| * ‖f j‖ ^ 2 ≤ B) (p : State S k) :
    |componentQuadratic M hM hk (∑' j, a j • square (f j)) p| ≤ 4 * (k : ℝ) * B := by
  have hsabs : Summable (fun j ↦ |a j| * (scaledSum M hM (f j) p) ^ 2) := by
    simpa only [abs_mul, abs_pow, sq_abs] using
      (summable_scaled_feature_squares M hM hk hs p).abs
  calc
    _ ≤ ∑' j, |a j| * (scaledSum M hM (f j) p) ^ 2 :=
      componentQuadratic_abs_le_feature_sum M hM hk hs p
    _ ≤ ∑' j, 4 * (k : ℝ) * (|a j| * ‖f j‖ ^ 2) := hsabs.tsum_le_tsum (fun j ↦ by
      simpa only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs] using
        scaled_feature_square_bound M hM hk (a j) (f j) p) (hs.mul_left (4 * (k : ℝ)))
    _ = 4 * (k : ℝ) * ∑' j, |a j| * ‖f j‖ ^ 2 := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

theorem integrable_exp_componentQuadratic_coefficient (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) (r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (γ : ℝ) (hγ : 0 ≤ γ) :
    Integrable (fun p ↦ Real.exp (γ *
      |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|))
        (law M g k r hC) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hi := integrable_exp_componentQuadratic M hM g hk r hC hs
    (γ * Real.sqrt (k : ℝ)) (by positivity)
  simpa only [mul_div_cancel_right₀ _ hq.ne'] using hi

/-- Uniform finite-size projective square-exponential estimate. It has no
source-field restriction, and handles bounded sizes at vanishing external
coefficient without appealing to an asymptotic profile estimate. -/
theorem integral_componentQuadratic_finite_size_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) (r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (hs : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) {B : ℝ}
    (hbudget : ∑' j, |a j| * ‖f j‖ ^ 2 ≤ B) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ (∫ p, Real.exp (γ * |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|)
        ∂law M g k r hC) - 1 ∧
      (∫ p, Real.exp (γ * |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|)
        ∂law M g k r hC) - 1 ≤ Real.exp (4 * γ * (k : ℝ) * B) - 1 := by
  have hi := integrable_exp_componentQuadratic_coefficient M hM g hk r hC hs γ hγ
  have hl := integral_mono (integrable_const (1 : ℝ)) hi
    (fun p ↦ Real.one_le_exp_iff.mpr (mul_nonneg hγ (abs_nonneg _)))
  have hu := integral_mono hi (integrable_const (Real.exp (4 * γ * (k : ℝ) * B)))
    (fun p ↦ Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_left (componentQuadratic_abs_le_budget M hM hk hs hbudget p) hγ
      exact hm.trans_eq (by ring)))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl hu
  exact ⟨by linarith, by linarith⟩

/-- Uniform actual projective quadratic exponential control with a common
feature budget, including size-dependent coefficient/feature families. -/
theorem exists_uniform_componentQuadratic_exponential_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, ∃ hk : 0 < k,
      ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L →
        ∀ (a : ℕ → ℝ) (f : ℕ → C(S, ℝ)),
          Summable (fun j ↦ |a j| * ‖f j‖ ^ 2) → (∑' j, |a j| * ‖f j‖ ^ 2) ≤ B →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          0 ≤ (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) *
              |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|)
                ∂law M g k r hC) - 1 ∧
            (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) *
              |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|)
                ∂law M g k r hC) - 1 ≤ D / Real.sqrt (k : ℝ) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_feature_square_series_bound M hM R L A B hL hA hB
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  refine ⟨hk.1, ?_⟩
  intro r hr g hg a f hs hbudget hCg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have he := hk.2 r hr g hg (fun j ↦ |a j|) f (fun j ↦ abs_nonneg _) hs hbudget hCg
  have hi := integrable_exp_componentQuadratic M hM g hk.1 r hCg hs A hA
  have hseriesMeas : Measurable (fun p : State S k ↦
      ∑' j, |a j| * (scaledSum M hM (f j) p) ^ 2) :=
    Measurable.tsum (fun j ↦ ((scaledSum_measurable M hM (f j)).pow_const 2).const_mul _)
  have hiseries : Integrable (fun p : State S k ↦ Real.exp ((A / Real.sqrt (k : ℝ)) *
      ∑' j, |a j| * (scaledSum M hM (f j) p) ^ 2)) (law M g k r hCg) := by
    apply integrable_of_measurable_abs_le (law M g k r hCg)
      (B := Real.exp ((A / Real.sqrt (k : ℝ)) *
        (4 * (k : ℝ) * ∑' j, |a j| * ‖f j‖ ^ 2))) (hseriesMeas.const_mul _).exp
    intro p
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsabs : Summable (fun j ↦ |a j| * (scaledSum M hM (f j) p) ^ 2) := by
      simpa only [abs_mul, abs_pow, sq_abs] using
        (summable_scaled_feature_squares M hM hk.1 hs p).abs
    calc
      _ ≤ ∑' j, 4 * (k : ℝ) * (|a j| * ‖f j‖ ^ 2) := hsabs.tsum_le_tsum (fun j ↦ by
        simpa only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs] using
          scaled_feature_square_bound M hM hk.1 (a j) (f j) p) (hs.mul_left (4 * (k : ℝ)))
      _ = _ := tsum_mul_left
  have hu := integral_mono hi hiseries (fun p ↦ Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (componentQuadratic_abs_le_feature_sum M hM hk.1 hs p)
      (by positivity)))
  have hl := integral_mono (integrable_const (1 : ℝ)) hi
    (fun p ↦ Real.one_le_exp_iff.mpr (by positivity))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl
  exact ⟨by linarith, by linarith [he.2]⟩

/-- The paper's projective-class assertion, obtained from its defining
summable representation rather than an exponential-moment hypothesis. -/
theorem exists_componentQuadratic_exponential_bound_of_representation
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) (L A : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (H : C(S × S, ℝ)) (hH : HasRepresentation H) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, ∃ hk : 0 < k,
      ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L →
        ∀ hC : 0 < M.fieldConnectedWeight g k r,
        0 ≤ (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) * |componentQuadratic M hM hk H p|)
            ∂law M g k r hC) - 1 ∧
          (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) * |componentQuadratic M hM hk H p|)
            ∂law M g k r hC) - 1 ≤ D / Real.sqrt (k : ℝ) := by
  obtain ⟨a, f, hs, hEq⟩ := hH
  subst H
  let B : ℝ := ∑' j, |a j| * ‖f j‖ ^ 2
  have hB : 0 ≤ B := tsum_nonneg (fun j ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _))
  obtain ⟨D, hD, hbound⟩ := exists_uniform_componentQuadratic_exponential_bound M hM R L A B hL hA hB
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  obtain ⟨hkpos, hkb⟩ := hk
  exact ⟨hkpos, fun r hr g hg hCg ↦ hkb r hr g hg a f hs le_rfl hCg⟩

/-- Literal `1 + o(1)` projective quadratic exponential control along any
admissible diverging-size single-component sequence. -/
theorem componentQuadratic_exponential_tendsto_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (H : C(S × S, ℝ)) (hH : HasRepresentation H)
    (k r : ℕ → ℕ) (g : ℕ → C(S, ℝ)) (hk : ∀ n, 0 < k n)
    (hkt : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A / Real.sqrt (k n : ℝ)) *
      |componentQuadratic M hM (hk n) H p|) ∂law M (g n) (k n) (r n) (hC n))
        atTop (𝓝 1) := by
  obtain ⟨D, hD, hbound⟩ := exists_componentQuadratic_exponential_bound_of_representation
    M hM R L A hL hA H hH
  have hbounds : ∀ᶠ n in atTop,
      0 ≤ (∫ p, Real.exp ((A / Real.sqrt (k n : ℝ)) * |componentQuadratic M hM (hk n) H p|)
        ∂law M (g n) (k n) (r n) (hC n)) - 1 ∧
      (∫ p, Real.exp ((A / Real.sqrt (k n : ℝ)) * |componentQuadratic M hM (hk n) H p|)
        ∂law M (g n) (k n) (r n) (hC n)) - 1 ≤ D / Real.sqrt (k n : ℝ) := by
    filter_upwards [hkt.eventually hbound, hr, hg] with n hn hnr hng
    obtain ⟨hkpos, hkb⟩ := hn
    exact hkb (r n) hnr (g n) hng (hC n)
  have herr : Tendsto (fun n ↦ D / Real.sqrt (k n : ℝ)) atTop (𝓝 0) := by
    have hp := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).comp hkt
    have hdiv (n : ℕ) : D / Real.sqrt (k n : ℝ) = D * (k n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    simp_rw [hdiv]
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hp
  have ht := squeeze_zero' (hbounds.mono (fun n hn ↦ hn.1))
    (hbounds.mono (fun n hn ↦ hn.2)) herr
  simpa only [sub_add_cancel, zero_add] using ht.add_const (1 : ℝ)

/-- Scale-matched projective control including arbitrary bounded and
diverging component sizes in the same sequence. Only the elementary
coefficient conditions `γ → 0` and `γ ≤ A / sqrt k` are required; every
moment estimate is proved above for the actual connected law. Feature
representations may vary with the sequence subject to one common budget. -/
theorem componentQuadratic_exponential_tendsto_one_scale_matched
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (k r : ℕ → ℕ) (g : ℕ → C(S, ℝ))
    (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → C(S, ℝ)) (γ : ℕ → ℝ)
    (hk : ∀ n, 0 < k n) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (hs : ∀ n, Summable (fun j ↦ |a n j| * ‖f n j‖ ^ 2))
    (hbudget : ∀ n, ∑' j, |a n j| * ‖f n j‖ ^ 2 ≤ B)
    (hγ : ∀ n, 0 ≤ γ n) (hγt : Tendsto γ atTop (𝓝 0))
    (hγscale : ∀ᶠ n in atTop, γ n ≤ A / Real.sqrt (k n : ℝ))
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n)) :
    Tendsto (fun n ↦ ∫ p, Real.exp (γ n *
      |componentQuadratic M hM (hk n) (∑' j, a n j • square (f n j)) p|)
        ∂law M (g n) (k n) (r n) (hC n)) atTop (𝓝 1) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_componentQuadratic_exponential_bound M hM R L A B hL hA hB
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hDlim : Tendsto (fun k : ℕ ↦ D / Real.sqrt (k : ℝ)) atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
    have he (k : ℕ) : D / Real.sqrt (k : ℝ) = D * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    simp_rw [he]
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hp
  have hlarge : ∀ᶠ k : ℕ in atTop,
      (∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L →
        ∀ (a : ℕ → ℝ) (f : ℕ → C(S, ℝ)),
          Summable (fun j ↦ |a j| * ‖f j‖ ^ 2) → (∑' j, |a j| * ‖f j‖ ^ 2) ≤ B →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
          (∫ p, Real.exp ((A / Real.sqrt (k : ℝ)) *
            |componentQuadratic M hM hk (∑' j, a j • square (f j)) p|)
              ∂law M g k r hC) - 1 ≤ D / Real.sqrt (k : ℝ)) ∧
        D / Real.sqrt (k : ℝ) < δ := by
    filter_upwards [hbound, hDlim.eventually (Iio_mem_nhds hδ)] with k hk hkd
    obtain ⟨hkpos, hkb⟩ := hk
    exact ⟨⟨hkpos, fun r hr g hg a f hs hbudget hC ↦ (hkb r hr g hg a f hs hbudget hC).2⟩, hkd⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hlarge
  have hsmallLim : Tendsto (fun n ↦ Real.exp (4 * γ n * (K : ℝ) * B) - 1) atTop (𝓝 0) := by
    have ht : Tendsto (fun n ↦ 4 * γ n * (K : ℝ) * B) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (((hγt.const_mul 4).mul_const (K : ℝ)).mul_const B)
    have hm := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1
    simpa only [Function.comp_apply, mul_zero, zero_mul, Real.exp_zero, sub_self] using hm
  filter_upwards [hr, hg, hγscale, hsmallLim.eventually (Iio_mem_nhds hδ)]
    with n hnr hng hnscale hnsmall
  have hfinite := integral_componentQuadratic_finite_size_bound M hM (g n) (hk n) (r n)
    (hC n) (hs n) (hbudget n) (γ n) (hγ n)
  rw [Real.dist_eq]
  rw [abs_of_nonneg hfinite.1]
  by_cases hkn : K ≤ k n
  · have hkb := hK (k n) hkn
    obtain ⟨hkpos, hb⟩ := hkb.1
    have hupper := hb (r n) hnr (g n) hng (a n) (f n) (hs n) (hbudget n) (hC n)
    have hiγ := integrable_exp_componentQuadratic_coefficient M hM (g n) (hk n) (r n)
      (hC n) (hs n) (γ n) (hγ n)
    have hiA := integrable_exp_componentQuadratic M hM (g n) (hk n) (r n)
      (hC n) (hs n) A hA
    have hmon := integral_mono hiγ hiA (fun p ↦ Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hnscale (abs_nonneg _)))
    linarith only [hupper, hmon, hkb.2]
  · have hknreal : (k n : ℝ) ≤ K := by exact_mod_cast (show k n ≤ K by omega)
    have hmul := mul_le_mul_of_nonneg_left hknreal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hγ n))
    have hmulB := mul_le_mul_of_nonneg_right hmul hB
    have hsmall := Real.exp_le_exp.mpr hmulB
    linarith only [hfinite.2, hsmall, hnsmall]

end PerronWright.ProjectiveExponential
