import PerronWright.Probability.BrownianMinimumWindowActualLimit

/-! # True minimum-window limit in the nonnegative density representation

The bounded continuous actual minimum test is converted to the precise
nonnegative source used in the proved first-passage density formula.
Consequently its normalized density integral has the genuine minimum-law
limit, including the entire future at the minimizer. No identification
with an entrance process or excursion law is asserted here.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumWindowNonnegativeLimit

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageUncappedLaw
open BrownianMinimumWindowLevelAverage BrownianMinimumWindowActualLimit
open BrownianFirstPassageMinimumWindowFutureLevelIntegral ContinuousPathMinimumFutureBandAverage

def sourceTest (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (p : ℝ × ℝ × Path) : ℝ≥0∞ :=
  ENNReal.ofReal (Ψ (Real.toNNReal p.2.1,-p.1,p.2.2))

theorem measurable_sourceTest (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Measurable (sourceTest Ψ) :=
  (Ψ.continuous.measurable.comp (measurable_snd.fst.real_toNNReal.prodMk
    (measurable_fst.neg.prodMk measurable_snd.snd))).ennreal_ofReal

theorem sourceFutureWindow_eq_ofReal (δ : ℝ) (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (p : ℝ × Path) :
    sourceFutureWindow δ T (sourceTest Ψ) p = ENNReal.ofReal (windowLevelTest δ T Ψ p) := by
  simp only [sourceFutureWindow,windowLevelTest,windowSet,Set.indicator,mem_ofPred_eq]
  by_cases ht : firstPassage (-p.1) p.2 < (T : ℝ≥0∞) <;>
    by_cases hs : p.2 ∈ survival (-p.1-δ) T <;>
    simp only [ht,hs,and_self,if_true,if_false,and_false,false_and,
      ENNReal.ofReal_zero,sourceTest,levelPoint,realTime,Real.toNNReal_coe]

theorem integrable_windowLevelTest (δ : ℝ) (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (f : Path)
    (hinterior : leastMinimizer T f < T) :
    Integrable (fun a : ℝ ↦ windowLevelTest δ T Ψ (a,f)) (volume.restrict (Ioi 0)) := by
  let B := Ioc (-minimumValue T f-δ) (-minimumValue T f)
  let : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (by simp [B,Real.volume_Ioc])
  have hm : Measurable (fun a : ℝ ↦ Ψ (levelPoint a f)) :=
    Ψ.continuous.measurable.comp (measurable_joint_levelPoint.comp
      (measurable_id.prodMk measurable_const))
  have hi : IntegrableOn (fun a : ℝ ↦ Ψ (levelPoint a f)) B :=
    (integrable_const ‖Ψ‖).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun a ↦ Ψ.norm_coe_le_norm _))
  have he : (fun a : ℝ ↦ windowLevelTest δ T Ψ (a,f)) =
      B.indicator (fun a ↦ Ψ (levelPoint a f)) :=
    funext (windowLevelTest_eq_band δ T Ψ f hinterior)
  rw [he]
  exact (hi.integrable_indicator measurableSet_Ioc).integrableOn

theorem ofReal_levelWindowAverage_eq_source (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) (f : Path)
    (hinterior : leastMinimizer T f < T) :
    ENNReal.ofReal (levelWindowAverage T Ψ δ f) =
      (∫⁻ a in Ioi (0 : ℝ), sourceFutureWindow δ T (sourceTest Ψ) (a,f))/ENNReal.ofReal δ := by
  have hn (a : ℝ) : 0 ≤ windowLevelTest δ T Ψ (a,f) :=
    Set.indicator_nonneg (fun p _ ↦ hΨ _) _
  rw [levelWindowAverage,← div_eq_inv_mul,ENNReal.ofReal_div_of_pos hδ,
    ofReal_integral_eq_lintegral_ofReal (integrable_windowLevelTest δ T Ψ f hinterior)
      (Eventually.of_forall hn)]
  congr 1
  exact lintegral_congr (fun a ↦ (sourceFutureWindow_eq_ofReal δ T Ψ (a,f)).symm)

theorem ofReal_integral_levelWindowAverage_eq_source (δ : ℝ) (hδ : 0 < δ)
    (T : ℝ≥0) (hT : 0 < T) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ)
    (hΨ : ∀ p, 0 ≤ Ψ p) :
    ENNReal.ofReal (∫ f, levelWindowAverage T Ψ δ f ∂pathLaw) =
      (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceFutureWindow δ T (sourceTest Ψ) (a,f) ∂volume) ∂pathLaw)/
        ENNReal.ofReal δ := by
  have hn (f : Path) : 0 ≤ levelWindowAverage T Ψ δ f :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (integral_nonneg (fun a ↦
      Set.indicator_nonneg (fun p _ ↦ hΨ _) (a,f)))
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_levelWindowAverage T hT Ψ δ hδ)
    (Eventually.of_forall hn),div_eq_mul_inv]
  have hm : Measurable (fun f : Path ↦ ∫⁻ a in Ioi (0 : ℝ),
      sourceFutureWindow δ T (sourceTest Ψ) (a,f)) :=
    (measurable_sourceFutureWindow δ T (sourceTest Ψ) (measurable_sourceTest Ψ)).lintegral_prod_left'
  rw [← lintegral_mul_const _ hm]
  apply lintegral_congr_ae
  filter_upwards [BrownianPathFiniteReversal.ae_leastMinimizer_interior T hT] with f hf
  exact (ofReal_levelWindowAverage_eq_source δ hδ T Ψ hΨ f hf.2).trans (div_eq_mul_inv _ _)

theorem actual_future_window_lintegral_limit (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceFutureWindow δ T (sourceTest Ψ) (a,f) ∂volume) ∂pathLaw)/
        ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T f)) ∂pathLaw)) := by
  have hi : Integrable (fun f : Path ↦ Ψ (minimumPoint T f)) pathLaw :=
    (integrable_const ‖Ψ‖).mono'
      (Ψ.continuous.measurable.comp (measurable_minimumPoint T)).aestronglyMeasurable
      (Eventually.of_forall (fun _ ↦ Ψ.norm_coe_le_norm _))
  have ht := ENNReal.tendsto_ofReal (actual_level_window_limit T hT Ψ)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ hΨ _))] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact ofReal_integral_levelWindowAverage_eq_source δ hδ T hT Ψ hΨ

theorem actual_future_density_limit (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (hΨ : ∀ p, 0 ≤ Ψ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s *
          ∫⁻ g in survival (-δ) (remainingTime T s), sourceTest Ψ (a,s,g) ∂pathLaw)/
        ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal (Ψ (minimumPoint T f)) ∂pathLaw)) := by
  apply (actual_future_window_lintegral_limit T hT Ψ hΨ).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [actual_minimum_window_future_level_density δ hδ T (sourceTest Ψ) (measurable_sourceTest Ψ)]

end PerronWright.BrownianMinimumWindowNonnegativeLimit
