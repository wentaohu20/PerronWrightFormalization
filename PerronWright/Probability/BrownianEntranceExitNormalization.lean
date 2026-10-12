import PerronWright.Probability.BrownianEntranceConvolution
import PerronWright.Probability.BrownianPositiveBridgeGaussianEnvelopeIntegrability

/-! # True normalization of the boundary entrance--exit product

The whole-line Gaussian envelope is integrable and bounded. It dominates
the already proved actual one-point bridge densities for every sufficiently
small positive endpoint. Their mass is genuinely one, so direct dominated
convergence computes the entrance--exit normalization without an assumed
uniform-integrability or entrance-law identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceExitNormalization

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianPositiveBridgeGaussianBounds BrownianPositiveBridgeGaussianEnvelopeIntegrability

def lowerDenominator (T : ℝ≥0) : ℝ := (T : ℝ)⁻¹*gaussianPDFReal 0 T 0

theorem lowerDenominator_pos (T : ℝ≥0) (hT : 0 < T) : 0 < lowerDenominator T :=
  mul_pos (inv_pos.mpr hT) (gaussianPDFReal_pos 0 T 0 (ne_of_gt hT))

def wholeLineBound (s t : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (envelopeSup t t)/ENNReal.ofReal (lowerDenominator (s+t)))*envelope s s x

theorem wholeLineBound_integral_ne_top (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ x, wholeLineBound s t x) ≠ ∞ := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hd0 : ENNReal.ofReal (lowerDenominator (s+t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lowerDenominator_pos (s+t) hT)
  have hc : ENNReal.ofReal (envelopeSup t t)/ENNReal.ofReal (lowerDenominator (s+t)) ≠ ∞ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top hd0
  unfold wholeLineBound
  rw [lintegral_const_mul _ (measurable_envelope s s)]
  exact ENNReal.mul_ne_top hc (envelopeMass_lt_top s s hs).ne

theorem eventually_onePointDensity_wholeLine_bound (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x : ℝ, onePointDensity a s t x ≤ wholeLineBound s t x := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hp := gaussianPDFReal_pos 0 (s+t) 0 (ne_of_gt hT)
  have hd : 0 < lowerDenominator (s+t) := lowerDenominator_pos _ hT
  have hlow : ((s+t : ℝ≥0) : ℝ)⁻¹ < 2/((s+t : ℝ≥0) : ℝ) := by
    have hi : (0 : ℝ) < ((s+t : ℝ≥0) : ℝ)⁻¹ := inv_pos.mpr (show (0 : ℝ) < (s+t : ℝ≥0) from hT)
    rw [div_eq_mul_inv]
    linarith
  have hid : Tendsto (fun a : ℝ ↦ a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    (normalization_div_sq_tendsto (s+t) hT).eventually_const_lt hlow] with a ha ha1 hn
  intro x
  have hsa := div_nonneg (densityReal_nonneg a ha s hs x) ha.le
  have hta := div_nonneg (densityReal_nonneg a ha t ht x) ha.le
  have hprod := mul_le_mul (densityReal_div_start_le_envelope a ha ha1.le s s s hs le_rfl le_rfl x)
    (densityReal_div_start_le_envelope a ha ha1.le t t t ht le_rfl le_rfl x)
    hta (envelopeReal_nonneg s s x)
  have hden : lowerDenominator (s+t) ≤
      ((1-Real.exp (-2*a^2/(s+t : ℝ≥0)))/a^2)*gaussianPDFReal 0 (s+t) 0 :=
    mul_le_mul_of_nonneg_right hn.le hp.le
  rw [onePointDensity_eq_scaled a ha s t hs ht x]
  have he : scaledDensityReal a s t x ≤
      (envelopeReal s s x*envelopeReal t t x)/lowerDenominator (s+t) := by
    unfold scaledDensityReal
    exact (div_le_div_of_nonneg_left (mul_nonneg hsa hta) hd hden).trans
      (div_le_div_of_nonneg_right hprod hd.le)
  calc
    _ ≤ ENNReal.ofReal ((envelopeReal s s x*envelopeReal t t x)/lowerDenominator (s+t)) :=
      ENNReal.ofReal_le_ofReal he
    _ = envelope s s x*envelope t t x/ENNReal.ofReal (lowerDenominator (s+t)) := by
      rw [ENNReal.ofReal_div_of_pos hd,ENNReal.ofReal_mul (envelopeReal_nonneg s s x)]
      rfl
    _ ≤ envelope s s x*ENNReal.ofReal (envelopeSup t t)/ENNReal.ofReal (lowerDenominator (s+t)) :=
      mul_le_mul' (mul_le_mul' le_rfl (envelope_le_sup t t ht x)) le_rfl
    _ = wholeLineBound s t x := by simp only [wholeLineBound,div_eq_mul_inv]; ac_rfl

theorem entranceExit_integral_eq_one (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ x, entranceExit s t x) = 1 := by
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (onePointDensity a s t) :=
    Eventually.of_forall (fun a ↦ measurable_onePointDensity a s t)
  have hbd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume, onePointDensity a s t x ≤ wholeLineBound s t x :=
    (eventually_onePointDensity_wholeLine_bound s t hs ht).mono (fun a ha ↦ Eventually.of_forall ha)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun a : ℝ ↦ onePointDensity a s t x)
      (𝓝[>] 0) (𝓝 (entranceExit s t x)) := Eventually.of_forall (onePointDensity_tendsto s t hs ht)
  have hdct := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (wholeLineBound s t)
    hm hbd (wholeLineBound_integral_ne_top s t hs ht) hlim
  have hmass : Tendsto (fun a : ℝ ↦ ∫⁻ x, onePointDensity a s t x) (𝓝[>] 0) (𝓝 (1 : ℝ≥0∞)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (onePoint_density_integral_eq_one a ha s t hs ht).symm
  exact tendsto_nhds_unique hdct hmass

theorem entrance_exit_convolution (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ x, entrance s x*entrance t x) =
      ENNReal.ofReal ((2/(s+t : ℝ≥0))*gaussianPDFReal 0 (s+t) 0) := by
  let d := ENNReal.ofReal ((2/(s+t : ℝ≥0))*gaussianPDFReal 0 (s+t) 0)
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hp := gaussianPDFReal_pos 0 (s+t) 0 (ne_of_gt hT)
  have hdR : 0 < (2/(s+t : ℝ≥0))*gaussianPDFReal 0 (s+t) 0 := by positivity
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdR
  have hfun : entranceExit s t = fun x ↦ d⁻¹*(entrance s x*entrance t x) := by
    funext x
    rw [entranceExit,entranceExitReal,ENNReal.ofReal_div_of_pos hdR,
      ENNReal.ofReal_mul (entranceReal_nonneg s x)]
    simp only [entrance,div_eq_mul_inv]
    exact mul_comm _ _
  have hm := entranceExit_integral_eq_one s t hs ht
  rw [hfun] at hm
  change (∫⁻ x, d⁻¹*(entrance s x*entrance t x)) = 1 at hm
  have hmP : Measurable (fun x : ℝ ↦ entrance s x*entrance t x) :=
    (measurable_entrance s).mul (measurable_entrance t)
  rw [lintegral_const_mul _ hmP] at hm
  calc
    _ = d*(d⁻¹*(∫⁻ x, entrance s x*entrance t x)) :=
      (ENNReal.mul_inv_cancel_left hd0 ENNReal.ofReal_ne_top).symm
    _ = d := by rw [hm,mul_one]

end PerronWright.BrownianEntranceExitNormalization
