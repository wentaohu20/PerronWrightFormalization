import PerronWright.Probability.BrownianFirstPassageDensityLaw
import PerronWright.Probability.BrownianHeatPassageTail

/-! # Exact first level moment of the genuine hitting density

At each positive duration the level-weighted hitting density is the
centered Gaussian second moment on the positive half-line, divided by
the duration. Its exact integral is one half; all integrability is proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPassageLevelFirstMoment

open BrownianFirstPassageDensityGeometry BrownianHeatPassageTail

theorem integrable_sq_heatReal (s : ℝ) (hs : 0 < s) :
    Integrable (fun a : ℝ ↦ a^2*heatReal s a) := by
  have hi : Integrable (fun a : ℝ ↦ a^2) (gaussianReal 0 (Real.toNNReal s)) := by
    simpa only [id_eq,Real.norm_eq_abs,sq_abs] using
      (memLp_id_gaussianReal' (μ := 0) (v := Real.toNNReal s) 2 (by norm_num)).integrable_norm_pow' (p := 2)
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt (Real.toNNReal_pos.mpr hs))] at hi
  have h := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 _)
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mp hi
  simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 _ _),smul_eq_mul,
    heatReal,mul_comm] using h

theorem integral_sq_heatReal (s : ℝ) (hs : 0 < s) :
    (∫ a : ℝ, a^2*heatReal s a) = s := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := Real.toNNReal s)
  change Var[id; gaussianReal 0 (Real.toNNReal s)] = (Real.toNNReal s : ℝ) at he
  rw [variance_eq_integral measurable_id.aemeasurable] at he
  simp only [id_eq,integral_id_gaussianReal,sub_zero,Real.coe_toNNReal _ hs.le] at he
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt (Real.toNNReal_pos.mpr hs)),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 _)
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))] at he
  simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 _ _),smul_eq_mul,
    heatReal,mul_comm] using he

theorem integral_positive_sq_heatReal (s : ℝ) (hs : 0 < s) :
    (∫ a : ℝ in Ioi 0, a^2*heatReal s a) = s/2 := by
  let F : ℝ → ℝ := fun a ↦ a^2*heatReal s a
  have he : (∫ a in Iic (0 : ℝ), F a) = ∫ a in Ioi (0 : ℝ), F a := by
    calc
      _ = ∫ a in Ioi (0 : ℝ), F (-a) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 F).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun a _ ↦ by
        simp only [F,heatReal,gaussianPDFReal,sub_zero,neg_sq])
  have hfull := integral_sq_heatReal s hs
  change (∫ a : ℝ, F a) = s at hfull
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi (integrable_sq_heatReal s hs),
    compl_Ioi,he] at hfull
  change (∫ a in Ioi (0 : ℝ), F a) = s/2
  linarith

theorem integrableOn_weighted_level_densityReal (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun a : ℝ ↦ a*densityReal a s) (Ioi 0) := by
  have hi := (integrable_sq_heatReal s hs).div_const s
  have he : (fun a : ℝ ↦ a*densityReal a s) = fun a ↦ a^2*heatReal s a/s := by
    funext a
    rw [densityReal_eq_heat a s hs]
    ring
  rw [he]
  exact hi.integrableOn

theorem integral_weighted_level_densityReal (s : ℝ) (hs : 0 < s) :
    (∫ a in Ioi (0 : ℝ), a*densityReal a s) = 1/2 := by
  have he : (fun a : ℝ ↦ a*densityReal a s) = fun a ↦ a^2*heatReal s a/s := by
    funext a
    rw [densityReal_eq_heat a s hs]
    ring
  rw [he,integral_div,integral_positive_sq_heatReal s hs]
  field_simp

theorem lintegral_weighted_level_density (s : ℝ) (hs : 0 < s) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal a*density a s) = ENNReal.ofReal (1/2 : ℝ) := by
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a*densityReal a s) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact (ENNReal.ofReal_mul ha.le).symm
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_weighted_level_densityReal s hs),
        integral_weighted_level_densityReal s hs]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact mul_nonneg ha.le (densityReal_nonneg a ha.le s)

end PerronWright.BrownianPassageLevelFirstMoment
