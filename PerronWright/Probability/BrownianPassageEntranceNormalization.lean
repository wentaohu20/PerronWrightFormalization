import PerronWright.Probability.BrownianEntranceKernelLaplace
import PerronWright.Probability.BrownianEntranceExitNormalization

/-! # Actual passage--entrance convolution normalization

The genuine first-passage density is half of the proved killed boundary
entrance density. The true entrance--exit convolution therefore computes
the level integral and the subsequent time integral, with no pinning-law
or candidate-mass assumption. Real integrability follows from this finite
nonnegative integral rather than being imposed as an interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPassageEntranceNormalization

open BrownianFirstPassageDensityGeometry BrownianKilledBoundaryEntrance
open BrownianEntranceKernelLaplace BrownianEntranceExitNormalization

theorem passage_entrance_convolution (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ a in Ioi (0 : ℝ), density a (s : ℝ)*entrance t a) =
      ENNReal.ofReal (gaussianPDFReal 0 (s+t) 0/(s+t : ℝ≥0)) := by
  have hh (a : ℝ) (ha : 0 < a) : density a (s : ℝ) =
      ENNReal.ofReal (1/2 : ℝ)*entrance s a := by
    have he := entrance_eq_twice_passage_density (s : ℝ) a ha
    rw [Real.toNNReal_coe] at he
    rw [he]
    rw [← mul_assoc,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    norm_num
  have he : (∫⁻ a in Ioi (0 : ℝ), entrance s a*entrance t a) =
      ∫⁻ a : ℝ, entrance s a*entrance t a := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro a
    by_cases ha : 0 < a
    · rw [indicator_of_mem (show a ∈ Ioi (0 : ℝ) from ha)]
    · simp only [entrance,entranceReal,
        indicator_of_notMem (show a ∉ Ioi (0 : ℝ) from ha),ENNReal.ofReal_zero,mul_zero]
  calc
    _ = ENNReal.ofReal (1/2 : ℝ)*(∫⁻ a in Ioi (0 : ℝ), entrance s a*entrance t a) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      rw [hh a ha,mul_assoc]
    _ = _ := by
      rw [he,entrance_exit_convolution s t hs ht,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      congr 1
      ring

theorem passage_entrance_normalization (T : ℝ≥0) (_hT : 0 < T) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
    (∫⁻ a in Ioi (0 : ℝ), density a s*entrance (Real.toNNReal ((T : ℝ)-s)) a) =
      ENNReal.ofReal (gaussianPDFReal 0 T 0/(T : ℝ)) := by
  have ht : 0 < (T : ℝ)-s := sub_pos.mpr hs.2
  have hsum : Real.toNNReal s+Real.toNNReal ((T : ℝ)-s) = T := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ hs.1.le,Real.coe_toNNReal _ ht.le]
    ring
  have he := passage_entrance_convolution (Real.toNNReal s) (Real.toNNReal ((T : ℝ)-s))
    (Real.toNNReal_pos.mpr hs.1) (Real.toNNReal_pos.mpr ht)
  simpa only [Real.coe_toNNReal _ hs.1.le,hsum] using he

private theorem normalizationReal_measurable (T : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    Measurable (fun a : ℝ ↦ densityReal a s*entranceReal (Real.toNNReal ((T : ℝ)-s)) a) := by
  have hd : Measurable (fun a : ℝ ↦ densityReal a s) := by
    simp only [densityReal,indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),argument]
    fun_prop
  exact hd.mul (measurable_entranceReal _)

private theorem normalizationReal_nonneg (T : ℝ≥0) (s : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun a : ℝ ↦ densityReal a s*entranceReal (Real.toNNReal ((T : ℝ)-s)) a) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact mul_nonneg (densityReal_nonneg a ha.le s) (entranceReal_nonneg _ a)

private theorem lintegral_normalizationReal (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal
      (densityReal a s*entranceReal (Real.toNNReal ((T : ℝ)-s)) a)) =
        ENNReal.ofReal (gaussianPDFReal 0 T 0/(T : ℝ)) := by
  rw [← passage_entrance_normalization T hT s hs]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact ENNReal.ofReal_mul (densityReal_nonneg a ha.le s)

theorem integrableOn_passage_entranceReal (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
    IntegrableOn (fun a : ℝ ↦ densityReal a s*entranceReal (Real.toNNReal ((T : ℝ)-s)) a)
      (Ioi 0) := by
  refine ⟨(normalizationReal_measurable T s hs.1).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (normalizationReal_nonneg T s),
    lintegral_normalizationReal T hT s hs]
  exact ENNReal.ofReal_lt_top

theorem integral_passage_entranceReal (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
    (∫ a in Ioi (0 : ℝ), densityReal a s*entranceReal (Real.toNNReal ((T : ℝ)-s)) a) =
      gaussianPDFReal 0 T 0/(T : ℝ) := by
  have hc : 0 ≤ gaussianPDFReal 0 T 0/(T : ℝ) :=
    div_nonneg (gaussianPDFReal_nonneg 0 T 0) T.coe_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae (normalizationReal_nonneg T s)
      (integrableOn_passage_entranceReal T hT s hs).aestronglyMeasurable,
    lintegral_normalizationReal T hT s hs,ENNReal.toReal_ofReal hc]

theorem time_level_normalization (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      density a s*entrance (Real.toNNReal ((T : ℝ)-s)) a) =
        ENNReal.ofReal (gaussianPDFReal 0 T 0) := by
  have hc : 0 ≤ gaussianPDFReal 0 T 0/(T : ℝ) :=
    div_nonneg (gaussianPDFReal_nonneg 0 T 0) T.coe_nonneg
  calc
    _ = ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (gaussianPDFReal 0 T 0/(T : ℝ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact passage_entrance_normalization T hT s hs
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero,
        ← ENNReal.ofReal_mul hc]
      congr 1
      exact div_mul_cancel₀ _ (ne_of_gt (show (0 : ℝ) < T from hT))

end PerronWright.BrownianPassageEntranceNormalization
