import PerronWright.Probability.BrownianMinimumEndpointPinningGeometry
import PerronWright.Probability.BrownianMinimumEndpointCandidateContinuity
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Actual endpoint-zero bridge minimum density

Translation of the literal terminal height and Tonelli identify the
endpoint candidate with the genuine bridge--Gaussian disintegration.
Equality of all Borel endpoint tests gives equality of volume densities
almost everywhere. Their proved endpoint-zero continuity then identifies
the actual pinned bridge minimum law, without assuming a conditional law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointPinningLaw

open BrownianPathLaw BrownianMinimumEndpointMeasure BrownianFirstPassageBridgeLaw
open BrownianMinimumEndpointPinningGeometry BrownianMinimumEndpointCandidateContinuity
open BrownianFirstPassageEndpointGeometry BrownianKilledBoundaryEntrance

private def base (T : ℝ≥0) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) (T : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

private instance base_sFinite (T : ℝ≥0) : SFinite (base T) := by
  unfold base
  infer_instance

private def integrand (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (z : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.2 p.1*
    entrance (remainingTime T p.1) (p.2+z)*ENNReal.ofReal (Φ (Real.toNNReal p.1,-p.2,p.2+z))

private theorem measurable_integrand (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) ↦ integrand T Φ p.1 p.2) :=
  measurable_joint_integrand T Φ

private theorem candidate_eq_base (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (z : ℝ) :
    candidate T Φ z = ∫⁻ p, integrand T Φ z p ∂base T := by
  exact (lintegral_prod _ ((measurable_integrand T Φ).comp
    (measurable_const.prodMk measurable_id : Measurable (fun p : ℝ × ℝ ↦ (z,p)))).aemeasurable).symm

theorem measurable_candidate (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (candidate T Φ) := by
  have hm := (measurable_integrand T Φ).lintegral_prod_right' (ν := base T)
  simpa only [← candidate_eq_base] using hm

theorem translate_endpoint_density (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*
        ∫⁻ y, entrance (remainingTime T s) y*H (y-a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y))) =
      ∫⁻ z, H z*candidate T Φ z := by
  have hm : Measurable (fun p : ℝ × (ℝ × ℝ) ↦ H p.1*integrand T Φ p.1 p.2) :=
    (hH.comp measurable_fst).mul (measurable_integrand T Φ)
  calc
    _ = ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        ∫⁻ z, H z*integrand T Φ z (s,a) := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro a
      have he := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ ↦ entrance (remainingTime T s) y*H (y-a)*
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,y))) a
      rw [← he]
      have hmeas : Measurable (fun z : ℝ ↦ entrance (remainingTime T s) (z+a)*H z*
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,z+a))) :=
        ((measurable_entrance _).comp (measurable_id.add_const _)).mul hH |>.mul
          (Φ.continuous.measurable.comp
            (measurable_const.prodMk (measurable_const.prodMk (measurable_id.add_const _)))).ennreal_ofReal
      simp only [add_sub_cancel_right]
      rw [← lintegral_const_mul _ hmeas]
      apply lintegral_congr
      intro z
      simp only [integrand,add_comm a z]
      ac_rfl
    _ = ∫⁻ p, (∫⁻ z, H z*integrand T Φ z p) ∂base T := by
      exact (lintegral_prod _ hm.lintegral_prod_left'.aemeasurable).symm
    _ = ∫⁻ z, ∫⁻ p, H z*integrand T Φ z p ∂base T :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr
      intro z
      have hmz : Measurable (fun p : ℝ × ℝ ↦ integrand T Φ z p) := by
        simpa only [Function.comp_def] using (measurable_integrand T Φ).comp
          (measurable_const.prodMk measurable_id : Measurable (fun p : ℝ × ℝ ↦ (z,p)))
      rw [candidate_eq_base]
      exact lintegral_const_mul (H z) hmz

theorem volume_endpoint_weighted_density (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z*(gaussianPDF 0 T z*pinnedTest T Φ z)) =
      ∫⁻ z, H z*candidate T Φ z := by
  have he := actual_endpoint_weighted_minimum_density T hT Φ H hH
  have hmH : Measurable (fun z : ℝ ↦ H z*pinnedTest T Φ z) :=
    hH.mul (measurable_pinnedTest T Φ)
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt hT),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hmH] at he
  have hleft : (∫⁻ z, gaussianPDF 0 T z*(H z*pinnedTest T Φ z)) =
      ∫⁻ z, H z*(gaussianPDF 0 T z*pinnedTest T Φ z) := by
    apply lintegral_congr
    intro z
    ac_rfl
  exact hleft.symm.trans (he.trans (translate_endpoint_density T Φ H hH))

private theorem lintegral_indicator_one_mul {B : Set ℝ} (hB : MeasurableSet B)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) z*F z) = ∫⁻ z in B, F z := by
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ B <;> simp [hz]

theorem ae_gaussian_pinnedTest_eq_candidate (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    (fun z ↦ gaussianPDF 0 T z*pinnedTest T Φ z) =ᵐ[volume] candidate T Φ := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    ((measurable_gaussianPDF _ _).mul (measurable_pinnedTest T Φ)) (measurable_candidate T Φ)
  intro B hB _
  have he := volume_endpoint_weighted_density T hT Φ (B.indicator (fun _ ↦ 1))
    (measurable_const.indicator hB)
  simpa only [lintegral_indicator_one_mul hB,Pi.mul_apply] using he

theorem actual_pinned_minimum_density (T b : ℝ≥0) (hb : b < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m y, Φ (t,m,y) = 0) :
    gaussianPDF 0 T 0*(∫⁻ g, ENNReal.ofReal (Φ (minimumTriple T g)) ∂pinnedLaw T) =
      candidate T Φ 0 := by
  have hT : 0 < T := (show 0 ≤ b from zero_le).trans_lt hb
  have hfin : (∫⁻ g, ENNReal.ofReal (Φ (minimumTriple T g)) ∂pinnedLaw T) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖Φ‖))
    calc
      _ ≤ ∫⁻ _g : Path, ENNReal.ofReal ‖Φ‖ ∂pinnedLaw T := lintegral_mono (fun g ↦
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Φ.norm_coe_le_norm _)))
      _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
  have hd : Tendsto (gaussianPDF 0 T) (𝓝 0) (𝓝 (gaussianPDF 0 T 0)) := by
    exact (ENNReal.continuous_ofReal.comp (show Continuous (gaussianPDFReal 0 T) from by
      unfold gaussianPDFReal
      fun_prop)).tendsto 0
  have hl := ENNReal.Tendsto.mul hd (Or.inr hfin) (pinnedTest_tendsto T hT Φ hΦ)
    (Or.inr gaussianPDF_ne_top)
  exact eq_at_zero_of_ae_eq_of_tendsto hl (candidate_tendsto T b hb Φ hcut 0)
    (ae_gaussian_pinnedTest_eq_candidate T hT Φ)

end PerronWright.BrownianMinimumEndpointPinningLaw
