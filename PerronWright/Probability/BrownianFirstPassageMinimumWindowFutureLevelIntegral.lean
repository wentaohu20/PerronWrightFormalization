import PerronWright.Probability.BrownianFirstPassageMinimumWindowLevelIntegral

/-! # Actual level-integrated minimum window with the whole future

The actual future path at first passage remains part of the test. Its
joint Borel measurability and the true first-passage product law prove
both the level/path Tonelli identity and its exact hitting-density
representation. The literal ENNReal passage event avoids any no-hit
conversion convention in the deterministic minimum-band identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumWindowFutureLevelIntegral

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianFirstPassageEndpointGeometry
open BrownianFirstPassageEndpointFullDensity BrownianFirstPassageMinimumWindowLevelIntegral

theorem measurable_joint_passageFuture :
    Measurable (fun p : ℝ × Path ↦ passageFuture p.1 p.2) :=
  BrownianFirstPassagePastFibers.continuous_joint_futurePath.measurable.comp
    (measurable_joint_firstPassage.ennreal_toNNReal.prodMk measurable_snd)

def sourceFutureWindow (δ : ℝ) (T : ℝ≥0) (Ψ : ℝ × ℝ × Path → ℝ≥0∞)
    (p : ℝ × Path) : ℝ≥0∞ :=
  {p : ℝ × Path | firstPassage (-p.1) p.2 < (T : ℝ≥0∞)}.indicator
    (fun p ↦ {p : ℝ × Path | p.2 ∈ survival (-p.1-δ) T}.indicator
      (fun p ↦ Ψ (p.1,realTime (-p.1) p.2,passageFuture (-p.1) p.2)) p) p

theorem measurable_sourceFutureWindow (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (sourceFutureWindow δ T Ψ) := by
  have hp : Measurable (fun p : ℝ × Path ↦ (-p.1,p.2)) :=
    measurable_fst.neg.prodMk measurable_snd
  have ht : Measurable (fun p : ℝ × Path ↦ realTime (-p.1) p.2) :=
    measurable_joint_realTime.comp hp
  have hτ : Measurable (fun p : ℝ × Path ↦ firstPassage (-p.1) p.2) :=
    measurable_joint_firstPassage.comp hp
  have hf : Measurable (fun p : ℝ × Path ↦ passageFuture (-p.1) p.2) :=
    measurable_joint_passageFuture.comp hp
  have hs : MeasurableSet {p : ℝ × Path | p.2 ∈ survival (-p.1-δ) T} := by
    change MeasurableSet {p : ℝ × Path | -p.1-δ <
      ContinuousPathReflection.runningMinimum p.2 T}
    exact measurableSet_lt (measurable_fst.neg.sub_const δ)
      ((continuous_minimum_at T).measurable.comp measurable_snd)
  exact (hΨ.comp (measurable_fst.prodMk (ht.prodMk hf))).indicator hs |>.indicator
    (hτ measurableSet_Iio)

theorem sourceFutureWindow_eq_band (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × Path → ℝ≥0∞) (f : Path)
    (hinterior : leastMinimizer T f < T) (a : ℝ) :
    sourceFutureWindow δ T Ψ (a,f) =
      (Ioc (-minimumValue T f-δ) (-minimumValue T f)).indicator
        (fun a ↦ Ψ (a,realTime (-a) f,passageFuture (-a) f)) a := by
  have hτ : firstPassage (-a) f < (T : ℝ≥0∞) ↔ a ≤ -minimumValue T f := by
    rw [firstPassage_lt_iff_minimum_of_interior T f hinterior]
    constructor <;> intro h <;> linarith
  have hs : f ∈ survival (-a-δ) T ↔ -minimumValue T f-δ < a := by
    change -a-δ < minimumValue T f ↔ _
    constructor <;> intro h <;> linarith
  by_cases hlo : -minimumValue T f-δ < a <;>
    by_cases hhi : a ≤ -minimumValue T f <;>
    simp [sourceFutureWindow,Set.indicator,hτ,hs,hlo,hhi]

theorem sourceFutureWindow_path_lintegral (a : ℝ) (ha : 0 < a) (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × Path → ℝ≥0∞) :
    (∫⁻ f, sourceFutureWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f in {f : Path | realTime (-a) f < (T : ℝ)},
        (survival (-a-δ) T).indicator
          (fun f ↦ Ψ (a,realTime (-a) f,passageFuture (-a) f)) f ∂pathLaw := by
  have hH : MeasurableSet {f : Path | realTime (-a) f < (T : ℝ)} :=
    (measurable_realTime (-a)) measurableSet_Iio
  rw [← lintegral_indicator hH]
  apply lintegral_congr_ae
  filter_upwards [BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-a)
    (neg_neg_of_pos ha)] with f hf
  have he : firstPassage (-a) f < (T : ℝ≥0∞) ↔ realTime (-a) f < (T : ℝ) := by
    rw [← ENNReal.coe_toNNReal hf,ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.symm
  simp only [sourceFutureWindow,Set.indicator,mem_ofPred_eq,he]

theorem sourceFutureWindow_fubini (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ f, sourceFutureWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceFutureWindow δ T Ψ (a,f) ∂volume) ∂pathLaw :=
  lintegral_lintegral_swap (measurable_sourceFutureWindow δ T Ψ hΨ).aemeasurable

theorem actual_minimum_window_future_level_density (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceFutureWindow δ T Ψ (a,f) ∂volume) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s *
          ∫⁻ g in survival (-δ) (remainingTime T s), Ψ (a,s,g) ∂pathLaw := by
  rw [← sourceFutureWindow_fubini δ T Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
  rw [sourceFutureWindow_path_lintegral a ha]
  have hm : Measurable (fun p : ℝ × Path ↦ Ψ (a,p.1,p.2)) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact actual_minimum_window_future_full_density a ha δ hδ T _ hm

end PerronWright.BrownianFirstPassageMinimumWindowFutureLevelIntegral
