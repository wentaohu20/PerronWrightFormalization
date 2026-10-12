import PerronWright.Probability.BrownianKilledSurvivalMoment
import PerronWright.Probability.BrownianHeatPassageTail
import PerronWright.Probability.BrownianFirstPassageEndpointGeometry
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Actual minimum-window survival domination

The surviving future is a literal restriction of the constructed Brownian
path law. Its mass, normalized by the window width, is bounded by the
proved killed-law estimate. Integrating the genuine first-passage density
over positive levels gives the exact Gaussian prefactor. Together these
give an inverse-square-root endpoint majorant, whose integrability on the
full open time interval is proved here, without a density-exchange premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumWindowSurvivalBounds

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageEndpointGeometry
open BrownianKilledSurvivalMoment

theorem normalized_killed_density_mass_bound (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ y in Ioi (0 : ℝ), BrownianPositiveKilledEndpoint.density δ t y)/ENNReal.ofReal δ ≤
      ENNReal.ofReal (survivalCoefficient/Real.sqrt (t : ℝ)) := by
  have he : (∫⁻ y : ℝ, BrownianPositiveKilledEndpoint.density δ t y) =
      BrownianPositiveKilledEndpoint.law δ t univ := by
    rw [BrownianPositiveKilledEndpoint.law_eq_withDensity δ hδ t ht,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  calc
    _ ≤ (∫⁻ y : ℝ, BrownianPositiveKilledEndpoint.density δ t y)/ENNReal.ofReal δ :=
      ENNReal.div_le_div_right (lintegral_mono' Measure.restrict_le_self (fun _ ↦ le_rfl)) _
    _ = _ := by rw [he]
    _ ≤ _ := normalized_survival_mass_bound δ hδ t ht

theorem normalized_survival_path_mass_bound (δ : ℝ) (hδ : 0 < δ)
    (t : ℝ≥0) (ht : 0 < t) :
    pathLaw (survival (-δ) t)/ENNReal.ofReal δ ≤
      ENNReal.ofReal (survivalCoefficient/Real.sqrt (t : ℝ)) := by
  have he : BrownianPositiveKilledEndpoint.law δ t univ = pathLaw (survival (-δ) t) := by
    rw [BrownianPositiveKilledEndpoint.law,
      Measure.map_apply ((continuous_eval t).measurable.add_const δ) MeasurableSet.univ,
      preimage_univ,Measure.restrict_apply_univ]
  rw [← he]
  exact normalized_survival_mass_bound δ hδ t ht

theorem passage_level_mass (s : ℝ) (hs : 0 < s) :
    (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s) =
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s)) := by
  rw [BrownianHeatPassageTail.lintegral_level_density s 0 le_rfl]
  simp [BrownianHeatPassageTail.heat,BrownianHeatPassageTail.heatReal,gaussianPDFReal,
    Real.coe_toNNReal _ hs.le,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]

def timeMajorant (T : ℝ≥0) (s : ℝ) : ℝ :=
  1/(Real.sqrt s*Real.sqrt ((T : ℝ)-s))

def majorantCoefficient : ℝ := survivalCoefficient/Real.sqrt (2*Real.pi)

theorem majorantCoefficient_nonneg : 0 ≤ majorantCoefficient :=
  div_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans survivalCoefficient_ge_one) (Real.sqrt_nonneg _)

theorem measurable_timeMajorant (T : ℝ≥0) : Measurable (timeMajorant T) := by
  unfold timeMajorant
  fun_prop

theorem timeMajorant_nonneg (T : ℝ≥0) (s : ℝ) : 0 ≤ timeMajorant T s := by
  unfold timeMajorant
  positivity

theorem inverse_sqrt_product_le_split (T : ℝ≥0) (hT : 0 < T) (s : ℝ)
    (hs : s ∈ Ioo 0 (T : ℝ)) :
    timeMajorant T s ≤ (1/Real.sqrt ((T : ℝ)/2))*
      (1/Real.sqrt s+1/Real.sqrt ((T : ℝ)-s)) := by
  have hm : 0 < (T : ℝ)/2 := by positivity
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs.1
  have hrem : 0 < Real.sqrt ((T : ℝ)-s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hmid : 0 < Real.sqrt ((T : ℝ)/2) := Real.sqrt_pos.mpr hm
  by_cases hsm : s ≤ (T : ℝ)/2
  · have hr : Real.sqrt ((T : ℝ)/2) ≤ Real.sqrt ((T : ℝ)-s) :=
      Real.sqrt_le_sqrt (by linarith)
    calc
      _ ≤ 1/(Real.sqrt s*Real.sqrt ((T : ℝ)/2)) :=
        one_div_le_one_div_of_le (mul_pos hsqrt hmid) (mul_le_mul_of_nonneg_left hr hsqrt.le)
      _ = (1/Real.sqrt ((T : ℝ)/2))*(1/Real.sqrt s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hr : Real.sqrt ((T : ℝ)/2) ≤ Real.sqrt s :=
      Real.sqrt_le_sqrt (le_of_not_ge hsm)
    calc
      _ ≤ 1/(Real.sqrt ((T : ℝ)/2)*Real.sqrt ((T : ℝ)-s)) :=
        one_div_le_one_div_of_le (mul_pos hmid hrem) (mul_le_mul_of_nonneg_right hr hrem.le)
      _ = (1/Real.sqrt ((T : ℝ)/2))*(1/Real.sqrt ((T : ℝ)-s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) (by positivity)

theorem integrableOn_timeMajorant (T : ℝ≥0) (hT : 0 < T) :
    IntegrableOn (timeMajorant T) (Ioo 0 (T : ℝ)) := by
  have hpow : IntervalIntegrable (fun s : ℝ ↦ s ^ (-1/2 : ℝ)) volume 0 (T : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hleft : IntegrableOn (fun s : ℝ ↦ 1/Real.sqrt s) (Ioo 0 (T : ℝ)) := by
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ T from T.coe_nonneg)).mp hpow
    apply hi.congr_fun _ measurableSet_Ioo
    intro s hs
    change s ^ (-1/2 : ℝ) = 1/Real.sqrt s
    rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hs.1.le,← Real.sqrt_eq_rpow,one_div]
  have hright : IntegrableOn (fun s : ℝ ↦ 1/Real.sqrt ((T : ℝ)-s)) (Ioo 0 (T : ℝ)) := by
    have hv := (hpow.comp_sub_left (T : ℝ)).symm
    simp only [sub_zero,sub_self] at hv
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le T.coe_nonneg).mp hv
    apply hi.congr_fun _ measurableSet_Ioo
    intro s hs
    change ((T : ℝ)-s) ^ (-1/2 : ℝ) = 1/Real.sqrt ((T : ℝ)-s)
    rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg (sub_pos.mpr hs.2).le,
      ← Real.sqrt_eq_rpow,one_div]
  apply ((hleft.add hright).const_mul (1/Real.sqrt ((T : ℝ)/2))).mono'
    (measurable_timeMajorant T).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [Real.norm_eq_abs,abs_of_nonneg (timeMajorant_nonneg T s)]
  exact inverse_sqrt_product_le_split T hT s hs

theorem lintegral_timeMajorant_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s in Ioo 0 (T : ℝ), ENNReal.ofReal (timeMajorant T s)) ≠ ⊤ :=
  (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (timeMajorant_nonneg T))).mp
    (integrableOn_timeMajorant T hT).hasFiniteIntegral |>.ne

theorem normalized_level_survival_mass_bound (T : ℝ≥0) (s : ℝ)
    (hs : s ∈ Ioo 0 (T : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s)*
      (pathLaw (survival (-δ) (remainingTime T s))/ENNReal.ofReal δ) ≤
      ENNReal.ofReal (majorantCoefficient*timeMajorant T s) := by
  have ht : 0 < remainingTime T s := Real.toNNReal_pos.mpr (sub_pos.mpr hs.2)
  have hc : (remainingTime T s : ℝ) = (T : ℝ)-s :=
    Real.coe_toNNReal _ (sub_pos.mpr hs.2).le
  rw [passage_level_mass s hs.1]
  calc
    _ ≤ ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        ENNReal.ofReal (survivalCoefficient/Real.sqrt (remainingTime T s : ℝ)) :=
      mul_le_mul' le_rfl (normalized_survival_path_mass_bound δ hδ _ ht)
    _ = ENNReal.ofReal (majorantCoefficient*timeMajorant T s) := by
      rw [← ENNReal.ofReal_mul (by positivity),hc,majorantCoefficient,timeMajorant]
      congr 1
      ring

theorem normalized_survival_test_bound (δ : ℝ) (t : ℝ≥0) (C : ℝ)
    (Φ : Path → ℝ≥0∞) (hΦ : ∀ g, Φ g ≤ ENNReal.ofReal C) :
    (∫⁻ g in survival (-δ) t, Φ g ∂pathLaw)/ENNReal.ofReal δ ≤
      ENNReal.ofReal C*(pathLaw (survival (-δ) t)/ENNReal.ofReal δ) := by
  calc
    _ ≤ (∫⁻ _g in survival (-δ) t, ENNReal.ofReal C ∂pathLaw)/ENNReal.ofReal δ :=
      ENNReal.div_le_div_right (lintegral_mono hΦ) _
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ]
      simp only [div_eq_mul_inv]
      ring

theorem normalized_level_survival_test_bound (T : ℝ≥0) (s : ℝ)
    (hs : s ∈ Ioo 0 (T : ℝ)) (δ : ℝ) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C)
    (Φ : ℝ → Path → ℝ≥0∞) (hΦ : ∀ a ∈ Ioi (0 : ℝ), ∀ g, Φ a g ≤ ENNReal.ofReal C) :
    (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
      ((∫⁻ g in survival (-δ) (remainingTime T s), Φ a g ∂pathLaw)/ENNReal.ofReal δ)) ≤
      ENNReal.ofReal (C*majorantCoefficient*timeMajorant T s) := by
  have hd : AEMeasurable (fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (BrownianHeatPassageTail.integrableOn_level_densityReal s hs.1 0 le_rfl).aestronglyMeasurable
      |>.aemeasurable.ennreal_ofReal
  calc
    _ ≤ ∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        (ENNReal.ofReal C*(pathLaw (survival (-δ) (remainingTime T s))/ENNReal.ofReal δ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact mul_le_mul' le_rfl (normalized_survival_test_bound δ _ C (Φ a) (hΦ a ha))
    _ = ENNReal.ofReal C*((∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s)*
        (pathLaw (survival (-δ) (remainingTime T s))/ENNReal.ofReal δ)) := by
      rw [lintegral_mul_const'' _ hd]
      ring
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (majorantCoefficient*timeMajorant T s) :=
      mul_le_mul' le_rfl (normalized_level_survival_mass_bound T s hs δ hδ)
    _ = _ := by rw [← ENNReal.ofReal_mul hC,mul_assoc]

end PerronWright.BrownianMinimumWindowSurvivalBounds
