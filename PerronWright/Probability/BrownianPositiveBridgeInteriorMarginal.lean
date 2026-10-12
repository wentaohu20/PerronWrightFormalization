import PerronWright.Probability.BrownianPositiveBridgeTwoPointKernelBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Actual uniformly bounded interior marginal moments and tails

Every interior time shares the same whole-space Gaussian envelope under
the actual positive conditioned pinned bridge law. Consequently every
polynomial absolute marginal moment and its Markov tail are uniformly
controlled for sufficiently small positive endpoints.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeInteriorMarginal

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianPositiveBridgeGaussianBounds BrownianPositiveBridgeGaussianEnvelopeIntegrability
open BrownianPositiveBridgeTwoPointKernelBounds

def marginalMomentBound (δ T : ℝ≥0) (m : ℕ) : ℝ≥0∞ :=
  interiorCoefficient δ T*(∫⁻ x : ℝ, ENNReal.ofReal (|x|^m)*envelope δ T x)

theorem marginalMomentBound_ne_top (δ T : ℝ≥0) (hT : 0 < T) (m : ℕ) :
    marginalMomentBound δ T m ≠ ∞ := by
  have hp : gaussianPDF 0 T 0 ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (gaussianPDFReal_pos 0 T 0 (ne_of_gt hT))
  unfold marginalMomentBound interiorCoefficient
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hp) ENNReal.ofReal_ne_top)
    (polynomial_envelope_integral_lt_top δ T hT m).ne

theorem eventually_uniform_onePointDensity_bound (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s t : ℝ≥0), δ ≤ s → δ ≤ t → s+t = T →
      ∀ x : ℝ, onePointDensity a s t x ≤ interiorCoefficient δ T*envelope δ T x := by
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hsmall,eventually_normalization_sq_ratio_bound T hT]
    with a ha ha1 hratio
  intro s t hs ht hsum x
  have hsT : s ≤ T := by rw [← hsum]; exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)
  have htT : t ≤ T := by rw [← hsum]; exact le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s)
  have hb1 := density_le_start_mul_envelope a ha ha1.le δ s T hδ hs hsT x
  have hb2 : density x t a ≤ ENNReal.ofReal a*ENNReal.ofReal (envelopeSup δ T) := by
    rw [density_symm x a t (hδ.trans_le ht)]
    exact (density_le_start_mul_envelope a ha ha1.le δ t T hδ ht htT x).trans
      (mul_le_mul' le_rfl (envelope_le_sup δ T hT x))
  unfold onePointDensity
  rw [hsum]
  calc
    _ ≤ (normalization a T)⁻¹*((ENNReal.ofReal a*envelope δ T x)*
        (ENNReal.ofReal a*ENNReal.ofReal (envelopeSup δ T)))/gaussianPDF 0 T 0 :=
      ENNReal.div_le_div_right (mul_le_mul' le_rfl (mul_le_mul' hb1 hb2)) _
    _ = ((normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a))/gaussianPDF 0 T 0*
        ENNReal.ofReal (envelopeSup δ T)*envelope δ T x := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' (ENNReal.div_le_div_right hratio _) le_rfl) le_rfl

theorem eventually_uniform_actual_marginal_moment (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T)
    (m : ℕ) : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s t : ℝ≥0), δ ≤ s → δ ≤ t → s+t = T →
      (∫⁻ g, ENNReal.ofReal (|g s|^m) ∂positiveBridgeLaw a T) ≤ marginalMomentBound δ T m := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_onePointDensity_bound δ T hδ hT] with a ha hb
  intro s t hs ht hsum
  have hΦ : Measurable (fun x : ℝ ↦ ENNReal.ofReal (|x|^m)) := by fun_prop
  have he := onePoint_lintegral a ha s t (hδ.trans_le hs) (hδ.trans_le ht) _ hΦ
  rw [hsum] at he
  rw [he]
  calc
    _ ≤ ∫⁻ x : ℝ, (interiorCoefficient δ T*envelope δ T x)*ENNReal.ofReal (|x|^m) :=
      lintegral_mono (fun x ↦ mul_le_mul' (hb s t hs ht hsum x) le_rfl)
    _ = _ := by
      have hm : Measurable (fun x : ℝ ↦ envelope δ T x*ENNReal.ofReal (|x|^m)) :=
        (measurable_envelope δ T).mul hΦ
      unfold marginalMomentBound
      have he := lintegral_const_mul (μ := volume) (interiorCoefficient δ T) hm
      simpa only [mul_assoc,mul_comm (envelope δ T _)] using he

theorem eventually_uniform_actual_marginal_fourth_tail (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s t : ℝ≥0), δ ≤ s → δ ≤ t → s+t = T →
      ∀ b : ℝ, 0 < b → positiveBridgeLaw a T {g | b ≤ |g s|} ≤
        marginalMomentBound δ T 4/ENNReal.ofReal (b^4) := by
  filter_upwards [eventually_uniform_actual_marginal_moment δ T hδ hT 4] with a hb
  intro s t hs ht hsum b hbpos
  have hm : Measurable (fun g : Path ↦ ENNReal.ofReal (|g s|^4)) :=
    ((continuous_eval s).measurable.abs.pow_const 4).ennreal_ofReal
  have hzero : ENNReal.ofReal (b^4) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hbpos 4)
  calc
    _ ≤ positiveBridgeLaw a T {g | ENNReal.ofReal (b^4) ≤ ENNReal.ofReal (|g s|^4)} :=
      measure_mono (fun g hg ↦ ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hbpos.le hg 4))
    _ ≤ (∫⁻ g, ENNReal.ofReal (|g s|^4) ∂positiveBridgeLaw a T)/ENNReal.ofReal (b^4) :=
      meas_ge_le_lintegral_div hm.aemeasurable hzero ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right (hb s t hs ht hsum) _

end PerronWright.BrownianPositiveBridgeInteriorMarginal
