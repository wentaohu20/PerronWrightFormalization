import PerronWright.Probability.BrownianPositiveBridgeGaussianEnvelopeIntegrability
import PerronWright.Probability.BrownianPositiveBridgeMultiPointLaw

/-! # Interior Gaussian domination of the actual two-point bridge density

Uniformity is over all interior pairs and every sufficiently small
positive endpoint, at one fixed total duration. The middle transition
is bounded by its genuine un-killed Gaussian; entrance and exit retain
their proved linear small-endpoint factors. No profile, tightness or
excursion distribution premise is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeTwoPointKernelBounds

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianPositiveBridgeGaussianBounds BrownianPositiveBridgeGaussianEnvelopeIntegrability

def twoPointGaps (s h t : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  if j = 0 then s else if j = 1 then h else if j = 2 then t else 0

def twoPointDensity (a : ℝ) (s h t : ℝ≥0) (x y : ℝ) : ℝ≥0∞ :=
  (normalization a (s+h+t))⁻¹*(density a s x*density x h y*density y t a)/gaussianPDF 0 (s+h+t) 0

def interiorCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0*ENNReal.ofReal (envelopeSup δ T)

theorem sampleTime_twoPointGaps (s h t : ℝ≥0) :
    sampleTime (twoPointGaps s h t) 3 = s+h+t := by
  simp [sampleTime_succ,sampleTime_zero,twoPointGaps]

theorem internalEval_twoPointGaps (s h t : ℝ≥0) (g : Path) :
    internalEval 2 (twoPointGaps s h t) g = ![g s,g (s+h)] := by
  funext i
  fin_cases i <;> simp [internalEval,internalTimes,sampleTime_succ,sampleTime_zero,twoPointGaps]

theorem multiDensity_twoPointGaps (a : ℝ) (s h t : ℝ≥0) (v : FreeVector 2) :
    multiDensity 2 a (twoPointGaps s h t) v = twoPointDensity a s h t (v 0) (v 1) := by
  have hl : (Fin.cons a v : Fin 3 → ℝ) (2 : Fin 3) = v 1 := rfl
  simp [multiDensity,twoPointDensity,sampleTime_twoPointGaps,jointDensity,Fin.prod_univ_two,
    prependInitial,lastState,twoPointGaps,hl]

theorem measurable_twoPointDensity (a : ℝ) (s h t : ℝ≥0) :
    Measurable (fun p : ℝ×ℝ ↦ twoPointDensity a s h t p.1 p.2) := by
  have hm : Measurable (fun p : ℝ×ℝ ↦ (![p.1,p.2] : FreeVector 2)) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  have he : (fun p : ℝ×ℝ ↦ twoPointDensity a s h t p.1 p.2) =
      multiDensity 2 a (twoPointGaps s h t) ∘ (fun p : ℝ×ℝ ↦ (![p.1,p.2] : FreeVector 2)) := by
    funext p
    exact (multiDensity_twoPointGaps a s h t ![p.1,p.2]).symm
  rw [he]
  exact (measurable_multiDensity 2 a _).comp hm

theorem density_le_gaussian (x y : ℝ) (h : ℝ≥0) : density x h y ≤ gaussianPDF x h y := by
  by_cases hy : 0 < y
  · apply ENNReal.ofReal_le_ofReal
    simp only [densityReal,Set.indicator,mem_Ioi,if_pos hy]
    exact sub_le_self _ (gaussianPDFReal_nonneg (-x) h y)
  · simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hy,ENNReal.ofReal_zero]
    exact zero_le

theorem density_le_start_mul_envelope (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (δ t T : ℝ≥0) (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    density a t y ≤ ENNReal.ofReal a*envelope δ T y := by
  have hb := normalized_density_le_envelope a ha ha1 δ t T hδ hδt htT y
  have he := (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top).mp hb
  simpa only [mul_comm] using he

theorem eventually_normalization_sq_ratio_bound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a) ≤ ENNReal.ofReal (T : ℝ) := by
  have hTR : (0 : ℝ) < T := hT
  have hi : (T : ℝ)⁻¹ < 2/(T : ℝ) := by
    rw [div_eq_mul_inv]
    have hp := inv_pos.mpr hTR
    linarith
  filter_upwards [self_mem_nhdsWithin,(normalization_div_sq_tendsto T hT).eventually_const_lt hi]
    with a ha hn
  have haR : 0 < a := ha
  have hnpos := normalizationReal_pos a haR T hT
  have hq : a^2/(1-Real.exp (-2*a^2/(T : ℝ))) ≤ (T : ℝ) := by
    have hx := (lt_div_iff₀ (sq_pos_of_pos haR)).mp hn
    have hx' : a^2/(T : ℝ) < 1-Real.exp (-2*a^2/(T : ℝ)) := by
      simpa only [div_eq_mul_inv,mul_comm] using hx
    exact (div_le_iff₀ hnpos).mpr (by
      have he := (div_lt_iff₀ hTR).mp hx'
      nlinarith)
  have he : (normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a) =
      ENNReal.ofReal (a^2/(1-Real.exp (-2*a^2/(T : ℝ)))) := by
    rw [ENNReal.ofReal_div_of_pos hnpos]
    unfold normalization
    rw [← ENNReal.ofReal_mul haR.le,← pow_two]
    simp only [div_eq_mul_inv]
    exact mul_comm _ _
  rw [he]
  exact ENNReal.ofReal_le_ofReal hq

theorem eventually_uniform_twoPointDensity_bound (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), δ ≤ s → δ ≤ t → s+h+t = T →
      ∀ x y : ℝ, twoPointDensity a s h t x y ≤
        interiorCoefficient δ T*envelope δ T x*gaussianPDF x h y := by
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hsmall,eventually_normalization_sq_ratio_bound T hT]
    with a ha ha1 hratio
  intro s h t hs ht hsum x y
  have hsT : s ≤ T := by rw [← hsum]; exact (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ h)).trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t))
  have htT : t ≤ T := by rw [← hsum]; exact le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s+h)
  have hb1 := density_le_start_mul_envelope a ha ha1.le δ s T hδ hs hsT x
  have hb3 : density y t a ≤ ENNReal.ofReal a*ENNReal.ofReal (envelopeSup δ T) := by
    rw [density_symm y a t (hδ.trans_le ht)]
    exact (density_le_start_mul_envelope a ha ha1.le δ t T hδ ht htT y).trans
      (mul_le_mul' le_rfl (envelope_le_sup δ T hT y))
  unfold twoPointDensity
  rw [hsum]
  calc
    _ ≤ (normalization a T)⁻¹*((ENNReal.ofReal a*envelope δ T x)*gaussianPDF x h y*
        (ENNReal.ofReal a*ENNReal.ofReal (envelopeSup δ T)))/gaussianPDF 0 T 0 :=
      ENNReal.div_le_div_right (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hb1 (density_le_gaussian x y h)) hb3)) _
    _ = ((normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a))/gaussianPDF 0 T 0*
        ENNReal.ofReal (envelopeSup δ T)*envelope δ T x*gaussianPDF x h y := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (ENNReal.div_le_div_right hratio _) le_rfl) le_rfl) le_rfl

end PerronWright.BrownianPositiveBridgeTwoPointKernelBounds
