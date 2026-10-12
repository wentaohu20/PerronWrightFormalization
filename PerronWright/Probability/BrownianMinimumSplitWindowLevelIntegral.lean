import PerronWright.Probability.BrownianFirstPassageMinimumWindowPastFutureLaw
import PerronWright.Probability.BrownianMinimumWindowLevelAverage

/-! # Genuine level-window exchange retaining the stopped past

The actual negative-level hit and lower-minimum window are integrated
over levels. Tonelli and the proved full first-passage product law retain
the stopped past, rather than replacing it by a hitting-time marginal.
The test is arbitrary nonnegative Borel, not an assumed Palm interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitWindowLevelIntegral

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianMinimumWindowLevelAverage
open BrownianFirstPassageMinimumWindowPastFutureLaw
open BrownianFirstPassageMinimumWindowLevelIntegral
open BrownianFirstPassageMinimumWindowFutureLevelIntegral

theorem measurable_joint_passagePast :
    Measurable (fun p : ℝ × Path ↦ passagePast p.1 p.2) := by
  have ht := measurable_joint_firstPassage.ennreal_toNNReal
  exact ht.prodMk (BrownianFirstPassagePastFibers.continuous_joint_pastPath.measurable.comp
    (ht.prodMk measurable_snd))

def sourceSplitWindow (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (p : ℝ × Path) : ℝ≥0∞ :=
  (windowSet δ T).indicator
    (fun p ↦ Ψ (p.1,passagePast (-p.1) p.2,passageFuture (-p.1) p.2)) p

theorem measurable_sourceSplitWindow (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (sourceSplitWindow δ T Ψ) := by
  have hp : Measurable (fun p : ℝ × Path ↦ (-p.1,p.2)) :=
    measurable_fst.neg.prodMk measurable_snd
  exact (hΨ.comp (measurable_fst.prodMk
    ((measurable_joint_passagePast.comp hp).prodMk
      (measurable_joint_passageFuture.comp hp)))).indicator (measurableSet_windowSet δ T)

theorem sourceSplitWindow_eq_band (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (f : Path)
    (hinterior : leastMinimizer T f < T) (a : ℝ) :
    sourceSplitWindow δ T Ψ (a,f) =
      (Ioc (-minimumValue T f-δ) (-minimumValue T f)).indicator
        (fun a ↦ Ψ (a,passagePast (-a) f,passageFuture (-a) f)) a := by
  have hτ : firstPassage (-a) f < (T : ℝ≥0∞) ↔ a ≤ -minimumValue T f := by
    rw [firstPassage_lt_iff_minimum_of_interior T f hinterior]
    constructor <;> intro h <;> linarith
  have hs : f ∈ survival (-a-δ) T ↔ -minimumValue T f-δ < a := by
    change -a-δ < minimumValue T f ↔ _
    constructor <;> intro h <;> linarith
  simp only [sourceSplitWindow,windowSet,Set.indicator,mem_ofPred_eq,hτ,hs,mem_Ioc]
  simp only [and_comm]

theorem sourceSplitWindow_path_lintegral (a : ℝ) (ha : 0 < a) (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) :
    (∫⁻ f, sourceSplitWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f in {f : Path | passageTime (-a) f < T},
        (survival (-a-δ) T).indicator
          (fun f ↦ Ψ (a,passagePast (-a) f,passageFuture (-a) f)) f ∂pathLaw := by
  have hH : MeasurableSet {f : Path | passageTime (-a) f < T} :=
    (measurable_passageTime (-a)) measurableSet_Iio
  rw [← lintegral_indicator hH]
  apply lintegral_congr_ae
  filter_upwards [BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-a)
    (neg_neg_of_pos ha)] with f hf
  have he : firstPassage (-a) f < (T : ℝ≥0∞) ↔ passageTime (-a) f < T := by
    rw [← ENNReal.coe_toNNReal hf,ENNReal.coe_lt_coe]
    rfl
  by_cases hτ : passageTime (-a) f < T <;>
    by_cases hs : f ∈ survival (-a-δ) T <;>
    simp only [sourceSplitWindow,windowSet,Set.indicator,mem_ofPred_eq,he,hτ,hs,
      and_self,if_true,if_false,and_false,false_and]

theorem sourceSplitWindow_fubini (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ f, sourceSplitWindow δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceSplitWindow δ T Ψ (a,f) ∂volume) ∂pathLaw :=
  lintegral_lintegral_swap (measurable_sourceSplitWindow δ T Ψ hΨ).aemeasurable

theorem actual_minimum_window_past_future_level_integral
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceSplitWindow δ T Ψ (a,f) ∂volume) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          Ψ (a,p,g) ∂pathLaw ∂passagePastLaw (-a) := by
  rw [← sourceSplitWindow_fubini δ T Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
  rw [sourceSplitWindow_path_lintegral a ha]
  have hm : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ Ψ (a,p)) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact actual_minimum_window_past_future_lintegral (-a) (neg_neg_of_pos ha) δ hδ T _ hm

end PerronWright.BrownianMinimumSplitWindowLevelIntegral
