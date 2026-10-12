import PerronWright.Probability.BrownianParabolicMinimumSplitWindow
import PerronWright.Probability.BrownianParabolicMinimumWindowLevelIntegral
import PerronWright.Probability.BrownianMinimumSplitWindowNonnegativeLimit
import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull

/-! # Actual parabolic minimum split from genuine weighted hitting products

The level-window limit is expressed with the true entire stopped driver
past and the true entire future. The stopped driver factor has its proved
random-time Radon--Nikodym density with respect to Brownian first passage.
No conditional minimum or excursion-Palm law is an input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumSplitProductLimit

open BrownianPathLaw BrownianPathReflectionLaw BrownianPathIndependentIncrements
open BrownianFirstPassagePastFibers BrownianFirstPassageUncappedLaw
open BrownianParabolicFirstPassageStrongMarkovFull BrownianParabolicFirstPassageStrongMarkov
open BrownianParabolicMinimumSplitWindow BrownianMinimumSplitWindowActualLimit
open ContinuousPathMinimumSplitBandAverage ContinuousPathFirstPassage
open BrownianParabolicMinimumWindowLevelIntegral
open BrownianParabolicFirstPassageStoppedTilt BrownianParabolicFirstPassageStoppedTiltFull

def driverPast (lambda : ℝ) (p : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (p.1,pastPath p.1 (driftPath lambda p.2))

theorem continuous_driverPast (lambda : ℝ) : Continuous (driverPast lambda) :=
  continuous_fst.prodMk (continuous_joint_pastPath.comp
    (continuous_fst.prodMk (continuous_driftPath.comp (continuous_const.prodMk continuous_snd))))

theorem driverPast_parabolicPassage (lambda level : ℝ) (f : Path) :
    driverPast lambda (parabolicPassagePast lambda level f) =
      actualDriverPassagePast lambda level f := by
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change driftPath lambda (pastPath (parabolicPassageTime lambda level f) f)
      (min t (parabolicPassageTime lambda level f)) =
      driftPath lambda f (min t (parabolicPassageTime lambda level f))
    rw [driftPath_apply,driftPath_apply,pastPath_eval,min_assoc,min_self]

private def driverSourceTest (lambda : ℝ)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ)
    (p : ℝ × ((ℝ≥0 × Path) × Path)) : ℝ≥0∞ :=
  ENNReal.ofReal (Ψ (driverPast lambda p.2.1,-p.1,driftPath (lambda-(p.2.1.1 : ℝ)) p.2.2))

private theorem measurable_driverSourceTest (lambda : ℝ)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) :
    Measurable (driverSourceTest lambda Ψ) :=
  (Ψ.continuous.measurable.comp
    (((continuous_driverPast lambda).measurable.comp measurable_snd.fst).prodMk
      (measurable_fst.neg.prodMk (continuous_driftPath.measurable.comp
        ((measurable_const.sub (NNReal.continuous_coe.measurable.comp
          measurable_snd.fst.fst)).prodMk measurable_snd.snd))))).ennreal_ofReal

private theorem driverSourceWindow_eq (lambda δ : ℝ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (a : ℝ) (f : Path) :
    sourceWindow lambda δ T (driverSourceTest lambda Ψ) (a,f) =
      BrownianMinimumSplitWindowLevelIntegral.sourceSplitWindow δ T
        (BrownianMinimumSplitWindowNonnegativeLimit.sourceTest Ψ) (a,driftPath lambda f) := by
  by_cases h : firstPassage (-a) (driftPath lambda f) < (T : ℝ≥0∞) ∧
      driftPath lambda f ∈ survival (-a-δ) T
  · have hf : driftPath (lambda-(parabolicPassagePast lambda (-a) f).1)
        (parabolicPassageFuture lambda (-a) f) = passageFuture (-a) (driftPath lambda f) := by
      change driftPath (lambda-(parabolicPassageTime lambda (-a) f : ℝ))
        (futurePath (parabolicPassageTime lambda (-a) f) f) =
        futurePath (parabolicPassageTime lambda (-a) f) (driftPath lambda f)
      exact (actual_drift_futurePath_eq_shift lambda _ f).symm
    simp only [sourceWindow,BrownianMinimumSplitWindowLevelIntegral.sourceSplitWindow,
      BrownianMinimumWindowLevelAverage.windowSet,Set.indicator,mem_ofPred_eq,h.1,h.2,
      and_self,if_true,
      driverSourceTest,BrownianMinimumSplitWindowNonnegativeLimit.sourceTest,
      driverPast_parabolicPassage,actualDriverPassagePast,hf]
  · simp only [sourceWindow,BrownianMinimumSplitWindowLevelIntegral.sourceSplitWindow,
      BrownianMinimumWindowLevelAverage.windowSet,Set.indicator,mem_ofPred_eq,h,if_false]

private theorem integrable_driverLevelWindowAverage (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun f : Path ↦ levelWindowAverage T Ψ δ (driftPath lambda f)) pathLaw := by
  have hd : Measurable (driftPath lambda) :=
    (continuous_driftPath.comp (continuous_const.prodMk continuous_id)).measurable
  have hi : Integrable (fun f : Path ↦ truncatedUnitBandAverage T Ψ δ (driftPath lambda f))
      pathLaw := (integrable_const ‖Ψ‖).mono'
    (((measurable_truncatedUnitBandAverage T Ψ).comp
      (measurable_const.prodMk hd)).aestronglyMeasurable)
    (Eventually.of_forall (fun f ↦ norm_truncatedUnitBandAverage_le T Ψ δ (driftPath lambda f)))
  apply hi.congr
  filter_upwards [ae_actual_minimum_geometry lambda T hT] with f hf
  exact (levelWindowAverage_eq_truncated T Ψ δ hδ (driftPath lambda f) hf.2.2).symm

private theorem ofReal_driverLevelIntegral (lambda δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (hT : 0 < T) (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    ENNReal.ofReal (∫ f, levelWindowAverage T Ψ δ (driftPath lambda f) ∂pathLaw) =
      (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceWindow lambda δ T (driverSourceTest lambda Ψ) (a,f)
        ∂volume) ∂pathLaw)/ENNReal.ofReal δ := by
  have hn (f : Path) : 0 ≤ levelWindowAverage T Ψ δ (driftPath lambda f) :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (integral_nonneg (fun a ↦
      Set.indicator_nonneg (fun p _ ↦ hΨ _) (a,driftPath lambda f)))
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_driverLevelWindowAverage lambda T hT Ψ δ hδ) (Eventually.of_forall hn),
    div_eq_mul_inv]
  have hm : Measurable (fun f : Path ↦ ∫⁻ a in Ioi (0 : ℝ),
      sourceWindow lambda δ T (driverSourceTest lambda Ψ) (a,f)) :=
    (measurable_sourceWindow lambda δ T _ (measurable_driverSourceTest lambda Ψ)).lintegral_prod_left'
  rw [← lintegral_mul_const _ hm]
  apply lintegral_congr_ae
  filter_upwards [ae_actual_minimum_geometry lambda T hT] with f hf
  have he := BrownianMinimumSplitWindowNonnegativeLimit.ofReal_levelWindowAverage_eq_source
    δ hδ T Ψ hΨ (driftPath lambda f) hf.2.2
  rw [div_eq_mul_inv] at he
  rw [he]
  congr 1
  exact lintegral_congr (fun a ↦ (driverSourceWindow_eq lambda δ T Ψ a f).symm)

theorem actual_raw_past_future_product_limit (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
          survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal (Ψ (driverPast lambda p,-a,driftPath (lambda-(p.1 : ℝ)) g))
            ∂pathLaw ∂BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw lambda (-a))/
        ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T (driftPath lambda f))) ∂pathLaw)) := by
  have hd : Measurable (driftPath lambda) :=
    (continuous_driftPath.comp (continuous_const.prodMk continuous_id)).measurable
  have hi : Integrable (fun f : Path ↦ Ψ (minimumPoint T (driftPath lambda f))) pathLaw :=
    (integrable_const ‖Ψ‖).mono'
      (Ψ.continuous.measurable.comp ((measurable_minimumPoint T).comp hd)).aestronglyMeasurable
      (Eventually.of_forall (fun _ ↦ Ψ.norm_coe_le_norm _))
  have ht := ENNReal.tendsto_ofReal (actual_parabolic_level_window_split_limit lambda T hT Ψ)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ hΨ _))] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [ofReal_driverLevelIntegral lambda δ hδ T hT Ψ hΨ,
    actual_minimum_window_past_future_level_integral lambda δ hδ T _
      (measurable_driverSourceTest lambda Ψ)]
  rfl

theorem driverPast_lintegral_eq_stoppedDensity (lambda level : ℝ) (hlevel : level < 0)
    {Φ : ℝ≥0 × Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ p, Φ (driverPast lambda p)
      ∂BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw lambda level) =
      ∫⁻ p, stoppedDensity lambda p*Φ p ∂pathLaw.map (passagePast level) := by
  rw [BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw]
  change (∫⁻ p, (Φ ∘ driverPast lambda) p ∂pathLaw.map (parabolicPassagePast lambda level)) = _
  rw [lintegral_map (hΦ.comp (continuous_driverPast lambda).measurable)
      (measurable_parabolicPassagePast lambda level)]
  simp only [Function.comp_def,driverPast_parabolicPassage]
  exact actual_parabolic_passage_lintegral lambda level hlevel hΦ

private theorem fixed_window_product_eq (lambda δ a : ℝ) (ha : 0 < a) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) :
    (∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
      ∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
        survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
        ENNReal.ofReal (Ψ (driverPast lambda p,-a,driftPath (lambda-(p.1 : ℝ)) g))
          ∂pathLaw ∂BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw lambda (-a)) =
      ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T}, stoppedDensity lambda p*
        (∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
          survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal (Ψ (p,-a,driftPath (lambda-(p.1 : ℝ)) g)) ∂pathLaw)
            ∂pathLaw.map (passagePast (-a)) := by
  let H : ((ℝ≥0 × Path) × Path) → ℝ≥0∞ :=
    fun q ↦ ENNReal.ofReal (Ψ (q.1,-a,driftPath (lambda-(q.1.1 : ℝ)) q.2))
  have hH : Measurable H := (Ψ.continuous.measurable.comp
    (measurable_fst.prodMk (measurable_const.prodMk (continuous_driftPath.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp
        measurable_fst.fst)).prodMk measurable_snd))))).ennreal_ofReal
  let K : (ℝ≥0 × Path) → ℝ≥0∞ := fun p ↦ ∫⁻ g,
    (BrownianParabolicMinimumWindowPastFutureLaw.futureSurvival lambda δ T).indicator H (p,g)
      ∂pathLaw
  have hK : Measurable K :=
    (hH.indicator (BrownianParabolicMinimumWindowPastFutureLaw.measurableSet_futureSurvival
      lambda δ T)).lintegral_prod_right'
  have hKeq (p : ℝ≥0 × Path) : K p =
      ∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
        survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
        ENNReal.ofReal (Ψ (p,-a,driftPath (lambda-(p.1 : ℝ)) g)) ∂pathLaw := by
    have hd : Measurable (driftPath (lambda-(p.1 : ℝ))) :=
      (continuous_driftPath.comp (continuous_const.prodMk continuous_id)).measurable
    rw [← lintegral_indicator ((measurableSet_survival (-δ)
      (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ))).preimage hd)]
    rfl
  let S : Set (ℝ≥0 × Path) := {p | p.1 < T}
  have hS : MeasurableSet S := measurable_fst measurableSet_Iio
  have he := driverPast_lintegral_eq_stoppedDensity lambda (-a) (neg_neg_of_pos ha)
    (Φ := S.indicator K) (hK.indicator hS)
  have hl : (∫⁻ p, (S.indicator K) (driverPast lambda p)
      ∂BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw lambda (-a)) =
      ∫⁻ p in S, K (driverPast lambda p)
        ∂BrownianParabolicMinimumWindowPastFutureLaw.passagePastLaw lambda (-a) := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro p
    simp only [Set.indicator,S,mem_ofPred_eq,driverPast]
  have hr : (∫⁻ p, stoppedDensity lambda p*(S.indicator K) p
      ∂pathLaw.map (passagePast (-a))) =
      ∫⁻ p in S, stoppedDensity lambda p*K p ∂pathLaw.map (passagePast (-a)) := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ S <;> simp only [Set.indicator,hp,if_true,if_false,mul_zero]
  rw [hl,hr] at he
  simp only [hKeq] at he
  exact he

theorem actual_weighted_firstPassage_product_limit (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T}, stoppedDensity lambda p*
        (∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
          survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal (Ψ (p,-a,driftPath (lambda-(p.1 : ℝ)) g)) ∂pathLaw)
            ∂pathLaw.map (passagePast (-a)))/ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T (driftPath lambda f))) ∂pathLaw)) := by
  apply (actual_raw_past_future_product_limit lambda T hT Ψ hΨ).congr'
  exact Eventually.of_forall (fun δ ↦ by
    dsimp only
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
    exact fixed_window_product_eq lambda δ a ha T Ψ)

end PerronWright.BrownianParabolicMinimumSplitProductLimit
