import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds

/-! # Finite Gaussian envelope moments on the whole state space

The envelope was derived from the actual killed kernel. Its mass and
every polynomial absolute moment are finite, with no supplied moment or
uniform-integrability assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeGaussianEnvelopeIntegrability

open BrownianPositiveBridgeGaussianBounds

def envelopeMass (δ T : ℝ≥0) : ℝ≥0∞ := ∫⁻ y, envelope δ T y

theorem integrable_pow_envelopeReal (δ T : ℝ≥0) (hT : 0 < T) (m : ℕ) :
    Integrable (fun y : ℝ ↦ y^m*envelopeReal δ T y) := by
  have hTR : (0 : ℝ) < T := hT
  have hp : Integrable (fun y : ℝ ↦ y^(m+1)*Real.exp (-y^2/(4*(T : ℝ)))) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq
      (show 0 < 1/(4*(T : ℝ)) by positivity) (s := ((m+1 : ℕ) : ℝ))
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
    simpa only [Real.rpow_natCast,div_eq_mul_inv,one_mul,neg_mul,mul_comm (4*(T : ℝ))⁻¹] using h
  have hd := hp.norm.const_mul (envelopeCoefficient δ)
  apply Integrable.mono' hd
  · exact ((measurable_id.pow_const m).mul (measurable_envelopeReal δ T)).aestronglyMeasurable
  · apply ae_of_all
    intro y
    by_cases hy : 0 < y
    · have he : y^m*envelopeReal δ T y =
          envelopeCoefficient δ*(y^(m+1)*Real.exp (-y^2/(4*(T : ℝ)))) := by
        unfold envelopeReal
        rw [max_eq_left hy.le]
        ring
      rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg (envelopeCoefficient_nonneg δ)]
    · simp only [envelopeReal,max_eq_right (le_of_not_gt hy),mul_zero,zero_mul,norm_zero]
      exact mul_nonneg (envelopeCoefficient_nonneg δ) (norm_nonneg _)

theorem integrable_envelopeReal (δ T : ℝ≥0) (hT : 0 < T) : Integrable (envelopeReal δ T) := by
  simpa only [pow_zero,one_mul] using integrable_pow_envelopeReal δ T hT 0

theorem envelopeMass_lt_top (δ T : ℝ≥0) (hT : 0 < T) : envelopeMass δ T < ∞ :=
  (hasFiniteIntegral_iff_ofReal (ae_of_all _ (envelopeReal_nonneg δ T))).mp
    (integrable_envelopeReal δ T hT).hasFiniteIntegral

theorem polynomial_envelope_integral_lt_top (δ T : ℝ≥0) (hT : 0 < T) (m : ℕ) :
    (∫⁻ y, ENNReal.ofReal (|y|^m)*envelope δ T y) < ∞ := by
  have hi : Integrable (fun y : ℝ ↦ |y|^m*envelopeReal δ T y) := by
    have h := (integrable_pow_envelopeReal δ T hT m).norm
    simpa only [norm_mul,Real.norm_eq_abs,abs_pow,abs_of_nonneg (envelopeReal_nonneg δ T _)] using h
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _
    (fun y : ℝ ↦ mul_nonneg (pow_nonneg (abs_nonneg y) m) (envelopeReal_nonneg δ T y)))).mp hi.hasFiniteIntegral
  simpa only [ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) m),envelope] using hfin

end PerronWright.BrownianPositiveBridgeGaussianEnvelopeIntegrability
