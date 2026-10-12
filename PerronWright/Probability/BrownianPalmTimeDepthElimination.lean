import PerronWright.Probability.ExponentialMonomialTail
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Actual scalar time and depth elimination in the Palm integral

The marking time ranges over the literal open interval of a source's start
and length. Tonelli gives its length even at zero length and for infinite
nonnegative tests. The negative-level depth integral is the already proved
zeroth exponential-monomial tail. These are Lebesgue identities, not assumed
stochastic Palm or excursion identities.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPalmTimeDepthElimination

variable {Z : Type*} [MeasurableSpace Z]

def timeWindow (s l : Z → ℝ≥0) (F : Z → ℝ≥0∞) (t : ℝ) (z : Z) : ℝ≥0∞ :=
  if (s z : ℝ) < t ∧ t < (s z + l z : ℝ≥0) then F z else 0

theorem measurable_joint_timeWindow (s l : Z → ℝ≥0) (F : Z → ℝ≥0∞)
    (hs : Measurable s) (hl : Measurable l) (hF : Measurable F) :
    Measurable (fun q : ℝ × Z ↦ timeWindow s l F q.1 q.2) := by
  have hmem : MeasurableSet {q : ℝ × Z |
      (s q.2 : ℝ) < q.1 ∧ q.1 < (s q.2 + l q.2 : ℝ≥0)} :=
    (measurableSet_lt (hs.comp measurable_snd).coe_nnreal_real measurable_fst).inter
      (measurableSet_lt measurable_fst
        ((hs.add hl).comp measurable_snd).coe_nnreal_real)
  exact Measurable.ite hmem (hF.comp measurable_snd) measurable_const

omit [MeasurableSpace Z] in
theorem lintegral_timeWindow (s l : Z → ℝ≥0) (F : Z → ℝ≥0∞) (z : Z) :
    (∫⁻ t : ℝ, timeWindow s l F t z) = (l z : ℝ≥0∞) * F z := by
  have he : (fun t : ℝ ↦ timeWindow s l F t z) =
      (Ioo (s z : ℝ) (s z + l z : ℝ≥0)).indicator (fun _ ↦ F z) := by
    funext t
    simp only [timeWindow, Set.indicator_apply, mem_Ioo]
  rw [he, lintegral_indicator measurableSet_Ioo, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
  simp only [NNReal.coe_add, add_sub_cancel_left, ENNReal.ofReal_coe_nnreal]
  exact mul_comm _ _

theorem timeWindow_source_lintegral (μ : Measure Z) [SFinite μ]
    (s l : Z → ℝ≥0) (F : Z → ℝ≥0∞)
    (hs : Measurable s) (hl : Measurable l) (hF : Measurable F) :
    (∫⁻ t : ℝ, ∫⁻ z, timeWindow s l F t z ∂μ) =
      ∫⁻ z, (l z : ℝ≥0∞) * F z ∂μ := by
  rw [lintegral_lintegral_swap (measurable_joint_timeWindow s l F hs hl hF).aemeasurable]
  exact lintegral_congr (fun z ↦ lintegral_timeWindow s l F z)

theorem negative_depth_lintegral (l : ℝ≥0) (hl : 0 < l) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(l : ℝ) * a))) =
      (l : ℝ≥0∞)⁻¹ := by
  have hlR : 0 < (l : ℝ) := hl
  have hi : IntegrableOn (fun a : ℝ ↦ Real.exp (-(l : ℝ) * a)) (Ioi 0) := by
    simpa only [pow_zero, mul_one] using
      ExponentialMonomialTail.integrableOn_exponential_monomial 0 l hlR 0 le_rfl
  have hv : (∫ a : ℝ in Ioi 0, Real.exp (-(l : ℝ) * a)) = (l : ℝ)⁻¹ := by
    simpa only [pow_zero, mul_one, mul_zero, Real.exp_zero,
      ExponentialMonomialTail.tailPolynomial, one_mul, one_div] using
      ExponentialMonomialTail.integral_exponential_monomial_tail 0 l hlR 0 le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le)), hv,
    ENNReal.ofReal_inv_of_pos hlR, ENNReal.ofReal_coe_nnreal]

theorem negative_depth_source_lintegral (μ : Measure Z) [SFinite μ]
    (l : Z → ℝ≥0) (F : Z → ℝ≥0∞)
    (hl : Measurable l) (hF : Measurable F)
    (hpos : ∀ᵐ z ∂μ, 0 < l z) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ z,
      ENNReal.ofReal (Real.exp (-(l z : ℝ) * a)) * F z ∂μ) =
      ∫⁻ z, (l z : ℝ≥0∞)⁻¹ * F z ∂μ := by
  have hm : Measurable (fun q : ℝ × Z ↦
      ENNReal.ofReal (Real.exp (-(l q.2 : ℝ) * q.1)) * F q.2) :=
    (((hl.comp measurable_snd).coe_nnreal_real.neg.mul measurable_fst).exp.ennreal_ofReal).mul
      (hF.comp measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hpos] with z hz
  rw [lintegral_mul_const (F z) (by fun_prop), negative_depth_lintegral (l z) hz]

theorem time_depth_source_cancellation (μ : Measure Z) [SFinite μ]
    (s l : Z → ℝ≥0) (F : Z → ℝ≥0∞)
    (hs : Measurable s) (hl : Measurable l) (hF : Measurable F)
    (hpos : ∀ᵐ z ∂μ, 0 < l z) :
    (∫⁻ t : ℝ, ∫⁻ a : ℝ in Ioi 0, ∫⁻ z,
      ENNReal.ofReal (Real.exp (-(l z : ℝ) * a)) * timeWindow s l F t z ∂μ) =
      ∫⁻ z, F z ∂μ := by
  have hw (t : ℝ) : Measurable (timeWindow s l F t) :=
    (measurable_joint_timeWindow s l F hs hl hF).comp
      (measurable_const.prodMk measurable_id)
  have he (t : ℝ) := negative_depth_source_lintegral μ l (timeWindow s l F t) hl (hw t) hpos
  simp_rw [he]
  have hwInv (t : ℝ) (z : Z) :
      (l z : ℝ≥0∞)⁻¹ * timeWindow s l F t z =
        timeWindow s l (fun z ↦ (l z : ℝ≥0∞)⁻¹ * F z) t z := by
    unfold timeWindow
    split_ifs <;> simp only [mul_zero]
  simp_rw [hwInv]
  have hInv : Measurable (fun z ↦ (l z : ℝ≥0∞)⁻¹ * F z) :=
    ((hl.coe_nnreal_ennreal.inv).mul hF)
  rw [timeWindow_source_lintegral μ s l (fun z ↦ (l z : ℝ≥0∞)⁻¹ * F z) hs hl hInv]
  apply lintegral_congr_ae
  filter_upwards [hpos] with z hz
  rw [← mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.coe_pos.mpr hz))
    ENNReal.coe_ne_top, one_mul]

end PerronWright.BrownianPalmTimeDepthElimination
