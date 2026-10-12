import PerronWright.Probability.BrownianMinimumEndpointLevelLimit
import PerronWright.Probability.BrownianHeatResolvent

/-! # Genuine full interior-time minimum endpoint entrance exchange

After the actual depth exchange, the proved inverse-square-root endpoint
majorant controls the whole time interval. Joint measurability and
dominated convergence pass the actual normalized survived-endpoint
integral through time as well, without any exchange-of-limits premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointTimeLimit

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageEndpointGeometry
open BrownianKilledBoundaryEntrance BrownianMinimumWindowSurvivalBounds
open BrownianMinimumEndpointLevelLimit

theorem measurable_joint_endpointKernel (T : ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (δ : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ endpointKernel T Φ δ p.1 p.2) := by
  have hr : Measurable (fun q : (ℝ × ℝ) × Path ↦ remainingTime T q.1.1) :=
    (continuous_remainingTime T).measurable.comp measurable_fst.fst
  have hs : MeasurableSet {q : (ℝ × ℝ) × Path |
      q.2 ∈ survival (-δ) (remainingTime T q.1.1)} := by
    change MeasurableSet {q : (ℝ × ℝ) × Path | -δ <
      ContinuousPathReflection.runningMinimum q.2 (remainingTime T q.1.1)}
    exact measurableSet_lt measurable_const
      (BrownianPathReflectionLaw.continuous_joint_minimum.measurable.comp
        (measurable_snd.prodMk hr))
  have hm : Measurable (fun q : (ℝ × ℝ) × Path ↦
      if q.2 ∈ survival (-δ) (remainingTime T q.1.1) then
        ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.1.2,q.2 (remainingTime T q.1.1))) else 0) :=
    Measurable.ite hs ((Φ.continuous.measurable.comp
      (measurable_fst.fst.real_toNNReal.prodMk (measurable_fst.snd.neg.prodMk
        (continuous_joint_eval.measurable.comp (measurable_snd.prodMk hr))))).ennreal_ofReal)
      measurable_const
  have h := hm.lintegral_prod_right' (ν := pathLaw) |>.div_const (ENNReal.ofReal δ)
  convert h using 1
  funext p
  rw [endpointKernel,← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T p.1))]
  rfl

theorem measurable_levelEndpointKernel (T : ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (δ : ℝ) :
    Measurable (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a) :=
  ((BrownianHeatResolvent.measurable_joint_passageDensity.comp measurable_swap).mul
    (measurable_joint_endpointKernel T Φ δ)).lintegral_prod_right'

theorem time_endpointKernel_tendsto (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ y, entrance (remainingTime T s) y*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y)))) := by
  let C : ℝ := ‖Φ‖*majorantCoefficient
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) majorantCoefficient_nonneg
  have hm : ∀ᶠ δ : ℝ in 𝓝[>] 0, Measurable (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a) :=
    Eventually.of_forall (measurable_levelEndpointKernel T Φ)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ s ∂volume.restrict (Ioo 0 (T : ℝ)),
      (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        endpointKernel T Φ δ s a) ≤ ENNReal.ofReal (C*timeMajorant T s) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact normalized_level_survival_test_bound T s hs δ hδ ‖Φ‖ (norm_nonneg _) _
      (fun a _ g ↦ ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Φ.norm_coe_le_norm _)))
  have hfin : (∫⁻ s in Ioo 0 (T : ℝ), ENNReal.ofReal (C*timeMajorant T s)) ≠ ∞ := by
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun s ↦ ENNReal.ofReal (C*timeMajorant T s)) hm hb hfin
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact level_endpointKernel_tendsto T s hs Φ hΦ

end PerronWright.BrownianMinimumEndpointTimeLimit
