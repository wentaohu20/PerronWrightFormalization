import PerronWright.Probability.BrownianMinimumSplitWindowActualLimit
import PerronWright.Probability.BrownianMinimumSplitWindowLevelIntegral

/-! # Actual minimum split as a limit of first-passage products

The genuine level-window limit is converted to nonnegative integrals,
then exchanged using the proved full past/future first-passage law. Both
path pieces remain literal random paths; no Palm-law identification or
conditional-distribution hypothesis is introduced.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitWindowNonnegativeLimit

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianMinimumSplitWindowLevelIntegral
open BrownianMinimumSplitWindowActualLimit ContinuousPathMinimumSplitBandAverage

def sourceTest (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ)
    (p : ℝ × ((ℝ≥0 × Path) × Path)) : ℝ≥0∞ :=
  ENNReal.ofReal (Ψ (p.2.1,-p.1,p.2.2))

theorem measurable_sourceTest (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) :
    Measurable (sourceTest Ψ) :=
  (Ψ.continuous.measurable.comp (measurable_snd.fst.prodMk
    (measurable_fst.neg.prodMk measurable_snd.snd))).ennreal_ofReal

def windowTest (δ : ℝ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (p : ℝ × Path) : ℝ :=
  (BrownianMinimumWindowLevelAverage.windowSet δ T).indicator
    (fun p ↦ Ψ (passagePast (-p.1) p.2,-p.1,passageFuture (-p.1) p.2)) p

theorem sourceSplitWindow_eq_ofReal (δ : ℝ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (p : ℝ × Path) :
    sourceSplitWindow δ T (sourceTest Ψ) p = ENNReal.ofReal (windowTest δ T Ψ p) := by
  by_cases h : p ∈ BrownianMinimumWindowLevelAverage.windowSet δ T <;>
    simp only [sourceSplitWindow,windowTest,Set.indicator,h,if_true,if_false,
      sourceTest,ENNReal.ofReal_zero]

theorem integrable_windowTest (δ : ℝ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (f : Path)
    (hinterior : leastMinimizer T f < T) :
    Integrable (fun a : ℝ ↦ windowTest δ T Ψ (a,f)) (volume.restrict (Ioi 0)) := by
  let B := Ioc (-minimumValue T f-δ) (-minimumValue T f)
  let : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (by simp [B,Real.volume_Ioc])
  have hp : Measurable (fun a : ℝ ↦ (-a,f)) := measurable_id.neg.prodMk measurable_const
  have hm : Measurable (fun a : ℝ ↦ Ψ (passagePast (-a) f,-a,passageFuture (-a) f)) :=
    Ψ.continuous.measurable.comp ((measurable_joint_passagePast.comp hp).prodMk
      (measurable_id.neg.prodMk
        (BrownianFirstPassageMinimumWindowFutureLevelIntegral.measurable_joint_passageFuture.comp hp)))
  have hi : IntegrableOn (fun a : ℝ ↦ Ψ (passagePast (-a) f,-a,passageFuture (-a) f)) B :=
    (integrable_const ‖Ψ‖).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun a ↦ Ψ.norm_coe_le_norm _))
  have he : (fun a : ℝ ↦ windowTest δ T Ψ (a,f)) =
      B.indicator (fun a ↦ Ψ (passagePast (-a) f,-a,passageFuture (-a) f)) := by
    funext a
    have hτ : firstPassage (-a) f < (T : ℝ≥0∞) ↔ a ≤ -minimumValue T f := by
      rw [BrownianFirstPassageMinimumWindowLevelIntegral.firstPassage_lt_iff_minimum_of_interior
        T f hinterior]
      constructor <;> intro h <;> linarith
    have hs : f ∈ survival (-a-δ) T ↔ -minimumValue T f-δ < a := by
      change -a-δ < minimumValue T f ↔ _
      constructor <;> intro h <;> linarith
    simp only [windowTest,BrownianMinimumWindowLevelAverage.windowSet,Set.indicator,
      mem_ofPred_eq,hτ,hs,B,mem_Ioc]
    simp only [and_comm]
  rw [he]
  exact (hi.integrable_indicator measurableSet_Ioc).integrableOn

theorem ofReal_levelWindowAverage_eq_source (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) (f : Path)
    (hinterior : leastMinimizer T f < T) :
    ENNReal.ofReal (levelWindowAverage T Ψ δ f) =
      (∫⁻ a in Ioi (0 : ℝ), sourceSplitWindow δ T (sourceTest Ψ) (a,f))/ENNReal.ofReal δ := by
  have hn (a : ℝ) : 0 ≤ windowTest δ T Ψ (a,f) :=
    Set.indicator_nonneg (fun p _ ↦ hΨ _) _
  change ENNReal.ofReal (δ⁻¹ * ∫ a in Ioi (0 : ℝ), windowTest δ T Ψ (a,f)) = _
  rw [← div_eq_inv_mul,ENNReal.ofReal_div_of_pos hδ,
    ofReal_integral_eq_lintegral_ofReal (integrable_windowTest δ T Ψ f hinterior)
      (Eventually.of_forall hn)]
  congr 1
  exact lintegral_congr (fun a ↦ (sourceSplitWindow_eq_ofReal δ T Ψ (a,f)).symm)

theorem ofReal_integral_levelWindowAverage_eq_source (δ : ℝ) (hδ : 0 < δ)
    (T : ℝ≥0) (hT : 0 < T) (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ)
    (hΨ : ∀ p, 0 ≤ Ψ p) :
    ENNReal.ofReal (∫ f, levelWindowAverage T Ψ δ f ∂pathLaw) =
      (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceSplitWindow δ T (sourceTest Ψ) (a,f) ∂volume) ∂pathLaw)/
        ENNReal.ofReal δ := by
  have hn (f : Path) : 0 ≤ levelWindowAverage T Ψ δ f :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (integral_nonneg (fun a ↦
      Set.indicator_nonneg (fun p _ ↦ hΨ _) (a,f)))
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_levelWindowAverage T hT Ψ δ hδ)
    (Eventually.of_forall hn),div_eq_mul_inv]
  have hm : Measurable (fun f : Path ↦ ∫⁻ a in Ioi (0 : ℝ),
      sourceSplitWindow δ T (sourceTest Ψ) (a,f)) :=
    (measurable_sourceSplitWindow δ T (sourceTest Ψ) (measurable_sourceTest Ψ)).lintegral_prod_left'
  rw [← lintegral_mul_const _ hm]
  apply lintegral_congr_ae
  filter_upwards [BrownianPathFiniteReversal.ae_leastMinimizer_interior T hT] with f hf
  exact (ofReal_levelWindowAverage_eq_source δ hδ T Ψ hΨ f hf.2).trans (div_eq_mul_inv _ _)

theorem actual_split_window_lintegral_limit (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceSplitWindow δ T (sourceTest Ψ) (a,f) ∂volume) ∂pathLaw)/
        ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T f)) ∂pathLaw)) := by
  have hi : Integrable (fun f : Path ↦ Ψ (minimumPoint T f)) pathLaw :=
    (integrable_const ‖Ψ‖).mono'
      (Ψ.continuous.measurable.comp (measurable_minimumPoint T)).aestronglyMeasurable
      (Eventually.of_forall (fun _ ↦ Ψ.norm_coe_le_norm _))
  have ht := ENNReal.tendsto_ofReal (actual_level_window_split_limit T hT Ψ)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ hΨ _))] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact ofReal_integral_levelWindowAverage_eq_source δ hδ T hT Ψ hΨ

theorem actual_split_past_future_product_limit (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ((ℝ≥0 × Path) × (ℝ × Path)) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          ENNReal.ofReal (Ψ (p,-a,g)) ∂pathLaw
            ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a))/ENNReal.ofReal δ)
      (𝓝[>] 0) (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T f)) ∂pathLaw)) := by
  apply (actual_split_window_lintegral_limit T hT Ψ hΨ).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [actual_minimum_window_past_future_level_integral δ hδ T (sourceTest Ψ) (measurable_sourceTest Ψ)]
  rfl

end PerronWright.BrownianMinimumSplitWindowNonnegativeLimit
