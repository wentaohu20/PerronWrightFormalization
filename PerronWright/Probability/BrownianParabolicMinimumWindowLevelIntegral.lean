import PerronWright.Probability.BrownianParabolicMinimumWindowPastFutureLaw
import PerronWright.Probability.BrownianFirstPassageMinimumWindowLevelIntegral

/-! # Genuine full level exchange for parabolic minimum windows

Joint parameter measurability and Tonelli carry the actual whole raw
past/future window through the proved parabolic hitting product law.
The future survival test keeps the literal lambda-minus-elapsed-time
parameter. No conditional minimum or Palm distribution is supplied.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumWindowLevelIntegral

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianPathReflectionLaw BrownianParabolicFirstPassageStrongMarkovFull
open BrownianParabolicPassageParameterMeasurability BrownianParabolicFirstPassageFinite
open BrownianParabolicMinimumWindowPastFutureLaw
open BrownianFirstPassageMinimumWindowLevelIntegral

def sourceWindow (lambda δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (p : ℝ × Path) : ℝ≥0∞ :=
  {p : ℝ × Path | firstPassage (-p.1) (driftPath lambda p.2) < (T : ℝ≥0∞) ∧
    driftPath lambda p.2 ∈ survival (-p.1-δ) T}.indicator
    (fun p ↦ Ψ (p.1,parabolicPassagePast lambda (-p.1) p.2,
      parabolicPassageFuture lambda (-p.1) p.2)) p

theorem measurable_sourceWindow (lambda δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (sourceWindow lambda δ T Ψ) := by
  have hp : Measurable (fun p : ℝ × Path ↦ ((lambda,-p.1),p.2)) :=
    (measurable_const.prodMk measurable_fst.neg).prodMk measurable_snd
  have hτ := measurable_joint_parabolicFirstPassage.comp hp
  have hd : Measurable (fun p : ℝ × Path ↦ driftPath lambda p.2) :=
    continuous_driftPath.measurable.comp (measurable_const.prodMk measurable_snd)
  have hs : MeasurableSet {p : ℝ × Path | driftPath lambda p.2 ∈ survival (-p.1-δ) T} := by
    change MeasurableSet {p : ℝ × Path | -p.1-δ <
      ContinuousPathReflection.runningMinimum (driftPath lambda p.2) T}
    exact measurableSet_lt (measurable_fst.neg.sub_const δ)
      ((continuous_minimum_at T).measurable.comp hd)
  exact (hΨ.comp (measurable_fst.prodMk
    ((measurable_joint_parabolicPassagePast.comp hp).prodMk
      (measurable_joint_parabolicPassageFuture.comp hp)))).indicator
        ((hτ measurableSet_Iio).inter hs)

theorem sourceWindow_eq_band (lambda δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (f : Path)
    (hinterior : leastMinimizer T (driftPath lambda f) < T) (a : ℝ) :
    sourceWindow lambda δ T Ψ (a,f) =
      (Ioc (-minimumValue T (driftPath lambda f)-δ)
        (-minimumValue T (driftPath lambda f))).indicator
        (fun a ↦ Ψ (a,parabolicPassagePast lambda (-a) f,
          parabolicPassageFuture lambda (-a) f)) a := by
  have hτ : firstPassage (-a) (driftPath lambda f) < (T : ℝ≥0∞) ↔
      a ≤ -minimumValue T (driftPath lambda f) := by
    rw [firstPassage_lt_iff_minimum_of_interior T (driftPath lambda f) hinterior]
    constructor <;> intro h <;> linarith
  have hs : driftPath lambda f ∈ survival (-a-δ) T ↔
      -minimumValue T (driftPath lambda f)-δ < a := by
    change -a-δ < minimumValue T (driftPath lambda f) ↔ _
    constructor <;> intro h <;> linarith
  simp only [sourceWindow,Set.indicator,mem_ofPred_eq,hτ,hs,mem_Ioc]
  simp only [and_comm]

theorem sourceWindow_path_lintegral (lambda a : ℝ) (δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) :
    (∫⁻ f, sourceWindow lambda δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f in {f : Path | parabolicPassageTime lambda (-a) f < T},
        ((driftPath lambda) ⁻¹' survival (-a-δ) T).indicator
          (fun f ↦ Ψ (a,parabolicPassagePast lambda (-a) f,
            parabolicPassageFuture lambda (-a) f)) f ∂pathLaw := by
  have hH : MeasurableSet {f : Path | parabolicPassageTime lambda (-a) f < T} :=
    (measurable_parabolicPassageTime lambda (-a)) measurableSet_Iio
  rw [← lintegral_indicator hH]
  apply lintegral_congr_ae
  filter_upwards [ae_parabolicFirstPassage_ne_top lambda (-a)] with f hf
  have he : firstPassage (-a) (driftPath lambda f) < (T : ℝ≥0∞) ↔
      parabolicPassageTime lambda (-a) f < T := by
    rw [← ENNReal.coe_toNNReal hf,ENNReal.coe_lt_coe]
    rfl
  by_cases hτ : parabolicPassageTime lambda (-a) f < T <;>
    by_cases hs : driftPath lambda f ∈ survival (-a-δ) T <;>
    simp only [sourceWindow,Set.indicator,mem_ofPred_eq,mem_preimage,he,hτ,hs,
      and_self,if_true,if_false,and_false,false_and]

theorem sourceWindow_fubini (lambda δ : ℝ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ f, sourceWindow lambda δ T Ψ (a,f) ∂pathLaw) =
      ∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceWindow lambda δ T Ψ (a,f) ∂volume) ∂pathLaw :=
  lintegral_lintegral_swap (measurable_sourceWindow lambda δ T Ψ hΨ).aemeasurable

theorem actual_minimum_window_past_future_level_integral
    (lambda δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, (∫⁻ a in Ioi (0 : ℝ), sourceWindow lambda δ T Ψ (a,f) ∂volume) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹'
          survival (-δ) (BrownianFirstPassageEndpointGeometry.remainingTime T (p.1 : ℝ)),
          Ψ (a,p,g) ∂pathLaw ∂passagePastLaw lambda (-a) := by
  rw [← sourceWindow_fubini lambda δ T Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
  rw [sourceWindow_path_lintegral lambda a]
  have hm : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ Ψ (a,p)) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact actual_minimum_window_past_future_lintegral lambda (-a) (neg_neg_of_pos ha) δ hδ T _ hm

end PerronWright.BrownianParabolicMinimumWindowLevelIntegral
