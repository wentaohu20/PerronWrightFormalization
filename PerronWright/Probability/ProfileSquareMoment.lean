import PerronWright.Probability.ProfileLaplace
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual exponential square moments of connected profiles

The expanding-field Laplace estimate is used at two fixed tilts. Together
with the deterministic empirical-probability bound this controls the
entire support, not only the truncated Gaussian-tail range.
-/

open MeasureTheory Filter Topology
open scoped Topology Real

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.ProfileSquareMoment

open ConnectedTypeLaw ProfileLaplace

/-- A global elementary exponential remainder bound. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith only [h]

/-- Square-exponential increments are dominated by one fixed absolute
linear exponential on the whole bounded support. -/
theorem exp_square_sub_one_le {a A q y : ℝ} (ha : 0 ≤ a) (haA : a ≤ A)
    (hq : 0 < q) (hy : |y| ≤ 2 * q) :
    Real.exp ((a / q) * y ^ 2) - 1 ≤
      (2 * a / q) * Real.exp ((2 * A + 1) * |y|) := by
  have hsq : y ^ 2 ≤ 2 * Real.exp |y| := by
    have h := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) 2
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at h
    rw [sq_abs] at h
    linarith
  have hexponent : (a / q) * y ^ 2 ≤ 2 * A * |y| := by
    have h := mul_le_mul_of_nonneg_right hy (abs_nonneg y)
    rw [← pow_two, sq_abs] at h
    have h' := mul_le_mul_of_nonneg_left h (div_nonneg ha hq.le)
    have ha' := mul_le_mul_of_nonneg_right haA (abs_nonneg y)
    calc
      _ ≤ (a / q) * (2 * q * |y|) := h'
      _ = 2 * a * |y| := by field_simp [hq.ne']
      _ ≤ _ := by nlinarith only [ha']
  calc
    _ ≤ ((a / q) * y ^ 2) * Real.exp ((a / q) * y ^ 2) :=
      exp_sub_one_le_mul_exp _
    _ ≤ ((a / q) * (2 * Real.exp |y|)) * Real.exp (2 * A * |y|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq (div_nonneg ha hq.le))
        (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le (by positivity)
    _ = (2 * a / q) * (Real.exp |y| * Real.exp (2 * A * |y|)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring

theorem exp_abs_le_exp_add_exp_neg (U y : ℝ) :
    Real.exp (U * |y|) ≤ Real.exp (U * y) + Real.exp (-U * y) := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hy)]
    have he : U * -y = -U * y := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

section BoundedRandomVariable

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Integrability of any bounded measurable real observable. -/
theorem integrable_of_measurable_abs_le {X : Ω → ℝ} (hX : Measurable X)
    {B : ℝ} (hB : ∀ x, |X x| ≤ B) : Integrable X μ :=
  (integrable_const B).mono' hX.aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hB x))

/-- A quantitative square moment bound derived from actual linear
exponential moments, rather than stored as a uniform-integrability input. -/
theorem integral_exp_square_sub_one_le {X : Ω → ℝ} (hX : Measurable X)
    {a A q B : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) (hq : 0 < q)
    (hXbound : ∀ x, |X x| ≤ 2 * q)
    (hplus : (∫ x, Real.exp ((2 * A + 1) * X x) ∂μ) ≤ B)
    (hminus : (∫ x, Real.exp (-(2 * A + 1) * X x) ∂μ) ≤ B) :
    0 ≤ (∫ x, Real.exp ((a / q) * (X x) ^ 2) ∂μ) - 1 ∧
      (∫ x, Real.exp ((a / q) * (X x) ^ 2) ∂μ) - 1 ≤ (4 * a / q) * B := by
  have hA : 0 ≤ A := ha.trans haA
  have hU : 0 ≤ 2 * A + 1 := by linarith
  have hint (s : ℝ) : Integrable (fun x ↦ Real.exp (s * X x)) μ := by
    apply integrable_of_measurable_abs_le μ (hX.const_mul s).exp
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      s * X x ≤ |s * X x| := le_abs_self _
      _ = |s| * |X x| := abs_mul _ _
      _ ≤ |s| * (2 * q) := mul_le_mul_of_nonneg_left (hXbound x) (abs_nonneg _)
  have hiSq : Integrable (fun x ↦ Real.exp ((a / q) * (X x) ^ 2)) μ := by
    apply integrable_of_measurable_abs_le μ ((hX.pow_const 2).const_mul _).exp
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (X x)) (hXbound x) 2)
      (div_nonneg ha hq.le)
  have hiSub := hiSq.sub (integrable_const (1 : ℝ))
  have hlinear := (hint (2 * A + 1)).add (hint (-(2 * A + 1)))
  have hmajor := hlinear.const_mul (2 * a / q)
  have hmon : (∫ x, Real.exp ((a / q) * (X x) ^ 2) - 1 ∂μ) ≤
      ∫ x, (2 * a / q) *
        (Real.exp ((2 * A + 1) * X x) + Real.exp (-(2 * A + 1) * X x)) ∂μ := by
    apply integral_mono hiSub hmajor
    intro x
    exact (exp_square_sub_one_le ha haA hq (hXbound x)).trans
      (mul_le_mul_of_nonneg_left (exp_abs_le_exp_add_exp_neg _ _) (by positivity))
  rw [integral_sub hiSq (integrable_const _), integral_const, probReal_univ,
    smul_eq_mul, mul_one, integral_const_mul, integral_add (hint _) (hint _)] at hmon
  have hlower : 1 ≤ ∫ x, Real.exp ((a / q) * (X x) ^ 2) ∂μ := by
    have h := integral_mono (integrable_const (1 : ℝ)) hiSq
      (fun x ↦ Real.one_le_exp_iff.mpr (by positivity))
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h
  refine ⟨by linarith, hmon.trans ?_⟩
  have hsum := add_le_add hplus hminus
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * a / q)
  exact hm.trans_eq (by ring)

end BoundedRandomVariable

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The unnormalized field statistic on the component's square-root scale. -/
def scaledSum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) : ℝ :=
  centeredSum M hM f p / Real.sqrt (k : ℝ)

theorem centeredSum_abs_le (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) :
    |centeredSum M hM f p| ≤ 2 * (k : ℝ) * ‖f‖ := by
  have hp : |∫ x, f x ∂M.perronLaw hM| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := M.perronLaw hM)
        (Eventually.of_forall (fun x ↦ f.norm_coe_le_norm x))
  have hs := typeSum_norm_le f p.1
  rw [centeredSum]
  calc
    _ ≤ |typeSum f p.1| + |(k : ℝ) * ∫ x, f x ∂M.perronLaw hM| := abs_sub _ _
    _ ≤ (k : ℝ) * ‖f‖ + (k : ℝ) * ‖f‖ := by
      exact add_le_add (by simpa only [Real.norm_eq_abs] using hs)
        (by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)];
            exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg k))
    _ = _ := by ring

theorem scaledSum_measurable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) : Measurable (scaledSum M hM (k := k) f) := by
  exact (((typeSum_continuous f).measurable.comp measurable_fst).sub_const _).div_const _

theorem scaledSum_abs_le (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (p : State S k) :
    |scaledSum M hM f p| ≤ 2 * Real.sqrt (k : ℝ) * ‖f‖ := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hsq := Real.sq_sqrt hkreal.le
  unfold scaledSum
  rw [abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  have hb := centeredSum_abs_le M hM f p
  have hsqmul := congrArg (fun z : ℝ ↦ 2 * z * ‖f‖) hsq
  nlinarith only [hb, hsqmul]

theorem scaledSum_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (s : ℝ) (p : State S k) :
    scaledSum M hM (s • f) p = s * scaledSum M hM f p := by
  simp only [scaledSum, centeredSum_smul]
  ring

theorem scaledSum_neg (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) :
    scaledSum M hM (-f) p = -scaledSum M hM f p := by
  simp only [scaledSum, centeredSum_neg, neg_div]

theorem integrable_exp_scaled_square (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g f : C(S, ℝ)) {k : ℕ} (hk : 0 < k) (r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun p : State S k ↦ Real.exp ((a / Real.sqrt (k : ℝ)) *
      (scaledSum M hM f p) ^ 2)) (law M g k r hC) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  apply integrable_of_measurable_abs_le (law M g k r hC)
    (((scaledSum_measurable M hM f).pow_const 2).const_mul _).exp
  intro p
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hsq := pow_le_pow_left₀ (abs_nonneg (scaledSum M hM f p))
    (scaledSum_abs_le M hM hk f p) 2
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (div_nonneg ha hq.le)

/-- Finite-size deterministic square-moment estimate, uniform over every
source field and surplus for which the literal law is defined. -/
theorem integral_scaled_square_finite_size_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (g f : C(S, ℝ)) {k : ℕ} (hk : 0 < k) (r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ (∫ p, Real.exp ((a / Real.sqrt (k : ℝ)) * (scaledSum M hM f p) ^ 2)
        ∂law M g k r hC) - 1 ∧
      (∫ p, Real.exp ((a / Real.sqrt (k : ℝ)) * (scaledSum M hM f p) ^ 2)
        ∂law M g k r hC) - 1 ≤ Real.exp (4 * a * Real.sqrt (k : ℝ) * ‖f‖ ^ 2) - 1 := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hi := integrable_exp_scaled_square M hM g f hk r hC a ha
  have hl := integral_mono (integrable_const (1 : ℝ)) hi
    (fun p ↦ Real.one_le_exp_iff.mpr (by positivity))
  have hu := integral_mono hi (integrable_const (Real.exp (4 * a * Real.sqrt (k : ℝ) * ‖f‖ ^ 2)))
    (fun p ↦ by
      apply Real.exp_le_exp.mpr
      have hsq := pow_le_pow_left₀ (abs_nonneg (scaledSum M hM f p))
        (scaledSum_abs_le M hM hk f p) 2
      rw [sq_abs] at hsq
      have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg ha hq.le)
      exact hm.trans_eq (by field_simp [hq.ne']; ring))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hl hu
  constructor <;> linarith

/-- Unit-normalization of a continuous field, including the zero field. -/
def unitField (f : C(S, ℝ)) : C(S, ℝ) := ‖f‖⁻¹ • f

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_unitField_le (f : C(S, ℝ)) : ‖unitField f‖ ≤ 1 := by
  by_cases hf : f = 0
  · simp [unitField, hf]
  · have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    rw [unitField, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg f),
      inv_mul_cancel₀ hn]

omit [MeasurableSpace S] [BorelSpace S] in
theorem field_eq_norm_smul_unitField (f : C(S, ℝ)) : f = ‖f‖ • unitField f := by
  by_cases hf : f = 0
  · simp [unitField, hf]
  · have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    simp only [unitField, smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem scaledSum_eq_norm_mul_unit (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (f : C(S, ℝ)) (p : State S k) :
    scaledSum M hM f p = ‖f‖ * scaledSum M hM (unitField f) p := by
  conv_lhs => rw [field_eq_norm_smul_unitField f]
  exact scaledSum_smul M hM (unitField f) ‖f‖ p

/-- Fixed linear tilts on the square-root scale are uniformly bounded for
the actual connected law. This bound covers the whole support. -/
theorem exists_uniform_scaled_laplace_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k : ℕ in atTop, 0 < k ∧
      ∀ r : ℕ, r ≤ R → ∀ g f : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
        ∀ hC : 0 < M.fieldConnectedWeight g k r,
        (∫ p, Real.exp (U * scaledSum M hM f p) ∂law M g k r hC) ≤ B := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := exists_centered_Laplace_bound M hM R
  let B : ℝ := Real.exp (C * (U ^ 2 + L * U) + Real.log 3)
  refine ⟨B, Real.exp_pos _, ?_⟩
  have hsmall : Tendsto (fun k : ℕ ↦ (L + U) * (k : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ), hsmall.eventually (Iio_mem_nhds hε)]
    with k hk hk1 hksmall
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hk1
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hsqrtSq := Real.sq_sqrt hkreal.le
  have hhalf : (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
    rw [Real.rpow_neg hkreal.le, ← Real.sqrt_eq_rpow]
  refine ⟨hkpos, ?_⟩
  intro r hr g f hg hf hCg
  let F : C(S, ℝ) := (U / Real.sqrt (k : ℝ)) • f
  have hF : ‖F‖ ≤ U / Real.sqrt (k : ℝ) := by
    dsimp only [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hU hsqrt.le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (div_nonneg hU hsqrt.le)
  have hG : ‖g‖ ≤ L / Real.sqrt (k : ℝ) := by
    apply (le_div_iff₀ hsqrt).mpr
    nlinarith only [hg]
  have hfield : ‖g‖ + ‖F‖ < ε := by
    have h := add_le_add hG hF
    rw [← add_div, div_eq_mul_inv, ← hhalf] at h
    exact h.trans_lt hksmall
  have he := (hk r hr).2 g F hfield hCg
  have hmul : ‖g‖ * ‖F‖ ≤ (L / Real.sqrt (k : ℝ)) * (U / Real.sqrt (k : ℝ)) :=
    mul_le_mul hG hF (norm_nonneg _) (div_nonneg hL hsqrt.le)
  have hsq : ‖F‖ ^ 2 ≤ (U / Real.sqrt (k : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hnumeric : (k : ℝ) * ((U / Real.sqrt (k : ℝ)) ^ 2 +
      (L / Real.sqrt (k : ℝ)) * (U / Real.sqrt (k : ℝ))) = U ^ 2 + L * U := by
    field_simp [hsqrt.ne']
    rw [hsqrtSq]
    ring
  have hcoeff : C * (k : ℝ) * (‖F‖ ^ 2 + ‖g‖ * ‖F‖) ≤ C * (U ^ 2 + L * U) := by
    calc
      _ ≤ C * (k : ℝ) * ((U / Real.sqrt (k : ℝ)) ^ 2 +
          (L / Real.sqrt (k : ℝ)) * (U / Real.sqrt (k : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hsq hmul) (by positivity)
      _ = _ := by rw [mul_assoc, hnumeric]
  have hfun (p : State S k) : centeredSum M hM F p = U * scaledSum M hM f p := by
    simp only [F, centeredSum_smul, scaledSum]
    ring
  change (∫ p, Real.exp (centeredSum M hM F p) ∂law M g k r hCg) ≤ _ at he
  simp_rw [hfun] at he
  exact he.trans (Real.exp_le_exp.mpr (add_le_add hcoeff (le_refl (Real.log 3))))

/-- Uniform actual one-feature exponential-square moments at scale
`k^(-1/2)`, with a quantitative error common to all unit-norm fields. -/
theorem exists_uniform_scaled_square_moment_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop, 0 < k ∧
      ∀ r : ℕ, r ≤ R → ∀ g f : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
        ∀ a : ℝ, 0 ≤ a → a ≤ A → ∀ hC : 0 < M.fieldConnectedWeight g k r,
        0 ≤ (∫ p, Real.exp ((a / Real.sqrt (k : ℝ)) * (scaledSum M hM f p) ^ 2)
              ∂law M g k r hC) - 1 ∧
          (∫ p, Real.exp ((a / Real.sqrt (k : ℝ)) * (scaledSum M hM f p) ^ 2)
              ∂law M g k r hC) - 1 ≤ D / Real.sqrt (k : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_scaled_laplace_bound M hM R L (2 * A + 1)
    hL (by linarith)
  let D : ℝ := 4 * A * B + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  refine ⟨hk.1, ?_⟩
  intro r hr g f hg hf a ha haA hCg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hfull (p : State S k) : |scaledSum M hM f p| ≤ 2 * Real.sqrt (k : ℝ) := by
    exact (scaledSum_abs_le M hM hk.1 f p).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * Real.sqrt (k : ℝ))])
  have hp := hk.2 r hr g f hg hf hCg
  have hn := hk.2 r hr g (-f) hg (by simpa only [norm_neg] using hf) hCg
  simp_rw [scaledSum_neg, mul_neg, ← neg_mul] at hn
  have he := integral_exp_square_sub_one_le (law M g k r hCg) (scaledSum_measurable M hM f)
    ha haA hsqrt hfull hp hn
  refine ⟨he.1, he.2.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_right haA hB.le
  have hcoef : 4 * a * B ≤ D := by dsimp only [D]; nlinarith only [hm]
  have hd := div_le_div_of_nonneg_right hcoef hsqrt.le
  convert hd using 1
  ring

end PerronWright.ProfileSquareMoment
