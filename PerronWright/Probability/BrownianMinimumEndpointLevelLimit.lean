import PerronWright.Probability.BrownianKilledUnshiftedEndpointEntrance
import PerronWright.Probability.BrownianMinimumWindowSurvivalBounds

/-! # Genuine depth integration of the minimum endpoint entrance limit

The actual normalized surviving future endpoint has the proved entrance
limit at every positive remaining duration. Its uniform killed-mass bound
allows that limit to pass through the actual first-passage depth density
at each interior time. No minimum-density exchange premise is imposed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointLevelLimit

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageEndpointGeometry
open BrownianKilledBoundaryEntrance BrownianKilledUnshiftedEndpointEntrance
open BrownianMinimumWindowSurvivalBounds

def endpointKernel (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (δ s a : ℝ) : ℝ≥0∞ :=
  (∫⁻ g in survival (-δ) (remainingTime T s),
    ENNReal.ofReal (Φ (Real.toNNReal s,-a,g (remainingTime T s))) ∂pathLaw)/ENNReal.ofReal δ

theorem measurable_endpointKernel (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (δ s : ℝ) :
    Measurable (endpointKernel T Φ δ s) := by
  have hm : Measurable (fun p : ℝ × Path ↦
      ENNReal.ofReal (Φ (Real.toNNReal s,-p.1,p.2 (remainingTime T s)))) :=
    (Φ.continuous.measurable.comp (measurable_const.prodMk
      (measurable_fst.neg.prodMk ((continuous_eval _).measurable.comp measurable_snd)))).ennreal_ofReal
  exact hm.lintegral_prod_right'.div_const _

theorem endpointKernel_tendsto (T : ℝ≥0) (s : ℝ) (hs : s < (T : ℝ))
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) (a : ℝ) :
    Tendsto (fun δ : ℝ ↦ endpointKernel T Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ y, entrance (remainingTime T s) y*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y)))) := by
  let L : C(ℝ × ℝ,ℝ≥0 × ℝ × ℝ) :=
    ⟨fun p ↦ (Real.toNNReal s,-a,p.2),continuous_const.prodMk
      (continuous_const.prodMk continuous_snd)⟩
  have ht : 0 < remainingTime T s := Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := actual_normalized_survived_endpoint_test_tendsto _ ht (Φ.compContinuous L)
    (fun p ↦ hΦ _)
  simpa only [endpointKernel,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk,L] using h

theorem level_endpointKernel_tendsto (T : ℝ≥0) (s : ℝ) (hs : s ∈ Ioo 0 (T : ℝ))
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        ∫⁻ y, entrance (remainingTime T s) y*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y)))) := by
  let d := fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s
  have hd : Measurable d := by
    unfold d BrownianFirstPassageDensityGeometry.density
    simp only [BrownianFirstPassageDensityGeometry.densityReal_explicit _ _ hs.1]
    fun_prop
  let μ : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity d
  have hmass : μ univ = ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s)) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact passage_level_mass s hs.1
  let : IsFiniteMeasure μ := ⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩
  let C : ℝ≥0∞ := ENNReal.ofReal
    (‖Φ‖*(BrownianKilledSurvivalMoment.survivalCoefficient/Real.sqrt (remainingTime T s : ℝ)))
  have ht : 0 < remainingTime T s := Real.toNNReal_pos.mpr (sub_pos.mpr hs.2)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ a ∂μ, endpointKernel T Φ δ s a ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (fun a ↦ by
      calc
        _ ≤ ENNReal.ofReal ‖Φ‖*(pathLaw (survival (-δ) (remainingTime T s))/ENNReal.ofReal δ) :=
          normalized_survival_test_bound δ _ ‖Φ‖ _ (fun g ↦ ENNReal.ofReal_le_ofReal
            ((le_abs_self _).trans (Φ.norm_coe_le_norm _)))
        _ ≤ ENNReal.ofReal ‖Φ‖*ENNReal.ofReal
            (BrownianKilledSurvivalMoment.survivalCoefficient/Real.sqrt (remainingTime T s : ℝ)) :=
          mul_le_mul' le_rfl (normalized_survival_path_mass_bound δ hδ _ ht)
        _ = C := (ENNReal.ofReal_mul (norm_nonneg _)).symm)
  have hfin : (∫⁻ _a, C ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _ ↦ C)
    (Eventually.of_forall (fun δ ↦ measurable_endpointKernel T Φ δ s)) hb hfin
      (Eventually.of_forall (endpointKernel_tendsto T s hs.2 Φ hΦ))
  have hc : Measurable (fun a : ℝ ↦ ∫⁻ y,
      entrance (remainingTime T s) y*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y))) := by
    have hprod : Measurable (fun p : ℝ × ℝ ↦ entrance (remainingTime T s) p.2*
        ENNReal.ofReal (Φ (Real.toNNReal s,-p.1,p.2))) :=
      ((measurable_entrance _).comp measurable_snd).mul
        ((Φ.continuous.measurable.comp (measurable_const.prodMk
          (measurable_fst.neg.prodMk measurable_snd))).ennreal_ofReal)
    exact hprod.lintegral_prod_right'
  change Tendsto _ _ (𝓝 (∫⁻ a, (∫⁻ y,
    entrance (remainingTime T s) y*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y))) ∂μ)) at h
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hc] at h
  simpa only [μ,d,Pi.mul_apply] using h.congr (fun δ ↦
    lintegral_withDensity_eq_lintegral_mul _ hd (measurable_endpointKernel T Φ δ s))

end PerronWright.BrownianMinimumEndpointLevelLimit
