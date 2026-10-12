import PerronWright.Probability.BrownianFirstPassageEndpointFullDensity
import PerronWright.Probability.BrownianFirstPassageMinimumApproximation

/-! # Integrating the genuine minimum-depth window over negative levels

The actual window integrand is jointly Borel in the level and Brownian
path. Tonelli therefore exchanges level and path integration. The true
first-passage and killed endpoint densities then give its exact numeric
integral for every nonnegative Borel test of level, hit time and endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumWindowLevelIntegral

open BrownianPathLaw ContinuousPathFirstPassage
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageEndpointFullDensity
open ContinuousPathLeastMinimum BrownianFirstPassageMinimumApproximation

theorem measurable_joint_realTime :
    Measurable (fun p : ℝ × Path ↦ realTime p.1 p.2) :=
  NNReal.continuous_coe.measurable.comp measurable_joint_firstPassage.ennreal_toNNReal

def sourceWindow (δ : ℝ) (T : ℝ≥0) (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞)
    (p : ℝ × Path) : ℝ≥0∞ :=
  {p : ℝ × Path | firstPassage (-p.1) p.2 < (T : ℝ≥0∞)}.indicator
    (fun p ↦ {p : ℝ × Path | p.2 ∈ survival (-p.1-δ) T}.indicator
      (fun p ↦ Ψ (p.1,realTime (-p.1) p.2,p.2 T)) p) p

theorem measurable_sourceWindow (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (sourceWindow δ T Ψ) := by
  have ht : Measurable (fun p : ℝ × Path ↦ realTime (-p.1) p.2) :=
    measurable_joint_realTime.comp (measurable_fst.neg.prodMk measurable_snd)
  have hτ : Measurable (fun p : ℝ × Path ↦ firstPassage (-p.1) p.2) :=
    measurable_joint_firstPassage.comp (measurable_fst.neg.prodMk measurable_snd)
  have hs : MeasurableSet {p : ℝ × Path | p.2 ∈ survival (-p.1-δ) T} := by
    change MeasurableSet {p : ℝ × Path | -p.1-δ <
      ContinuousPathReflection.runningMinimum p.2 T}
    exact measurableSet_lt (measurable_fst.neg.sub_const δ)
      ((continuous_minimum_at T).measurable.comp measurable_snd)
  exact (hΨ.comp (measurable_fst.prodMk
    (ht.prodMk ((continuous_eval T).measurable.comp measurable_snd)))).indicator hs |>.indicator
      (hτ measurableSet_Iio)

theorem firstPassage_lt_iff_minimum_of_interior (T : ℝ≥0) (f : Path)
    (hinterior : leastMinimizer T f < T) (level : ℝ) :
    firstPassage level f < (T : ℝ≥0∞) ↔ minimumValue T f ≤ level := by
  constructor
  · intro h
    exact (firstPassage_le_iff_minimum level f T).mp h.le
  · intro h
    exact (firstPassage_le_leastMinimizer T f level h).trans_lt
      (ENNReal.coe_lt_coe.mpr hinterior)

theorem sourceWindow_eq_band (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞) (f : Path)
    (hinterior : leastMinimizer T f < T) (a : ℝ) :
    sourceWindow δ T Ψ (a,f) =
      (Ioc (-minimumValue T f-δ) (-minimumValue T f)).indicator
        (fun a ↦ Ψ (a,realTime (-a) f,f T)) a := by
  have hτ : firstPassage (-a) f < (T : ℝ≥0∞) ↔ a ≤ -minimumValue T f := by
    rw [firstPassage_lt_iff_minimum_of_interior T f hinterior]
    constructor <;> intro h <;> linarith
  have hs : f ∈ survival (-a-δ) T ↔ -minimumValue T f-δ < a := by
    change -a-δ < minimumValue T f ↔ _
    constructor <;> intro h <;> linarith
  by_cases hlo : -minimumValue T f-δ < a <;>
    by_cases hhi : a ≤ -minimumValue T f <;>
    simp [sourceWindow,Set.indicator,hτ,hs,hlo,hhi]

theorem sourceWindow_path_lintegral (a : ℝ) (ha : 0 < a) (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ f, sourceWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f in {f : Path | realTime (-a) f < (T : ℝ)},
        (survival (-a-δ) T).indicator (fun f ↦ Ψ (a,realTime (-a) f,f T)) f ∂pathLaw := by
  have hH : MeasurableSet {f : Path | realTime (-a) f < (T : ℝ)} :=
    (measurable_realTime (-a)) measurableSet_Iio
  rw [← lintegral_indicator hH]
  apply lintegral_congr_ae
  filter_upwards [BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-a)
    (neg_neg_of_pos ha)] with f hf
  have he : firstPassage (-a) f < (T : ℝ≥0∞) ↔ realTime (-a) f < (T : ℝ) := by
    rw [← ENNReal.coe_toNNReal hf,ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.symm
  simp only [sourceWindow,Set.indicator,mem_ofPred_eq,he]

theorem sourceWindow_fubini (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ f, sourceWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceWindow δ T Ψ (a,f) ∂volume) ∂pathLaw :=
  lintegral_lintegral_swap (measurable_sourceWindow δ T Ψ hΨ).aemeasurable

theorem actual_minimum_window_level_density (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × ℝ × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceWindow δ T Ψ (a,f) ∂volume) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s *
          ∫⁻ y, BrownianPositiveKilledEndpoint.density δ (remainingTime T s) y *
            Ψ (a,s,-a-δ+y) := by
  rw [← sourceWindow_fubini δ T Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
  rw [sourceWindow_path_lintegral a ha]
  have hm : Measurable (fun p : ℝ × ℝ ↦ Ψ (a,p.1,p.2)) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact actual_minimum_window_full_density a ha δ hδ T _ hm

end PerronWright.BrownianFirstPassageMinimumWindowLevelIntegral
