import PerronWright.Probability.BrownianBridgeMinimumReconstruction
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalLaw

/-! # Exact actual conditioning as minimum-shift occupation bias

The actual uniform minimum-time / shifted-path product and exact inverse
rotation identify conditioning above a negative barrier with a literal
low-height occupation weight on the actual minimum-shift law. This is
an exact law identity, not an assertion that this bias vanishes or that
the minimum-shift law is the conditioned-positive entrance law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumOccupationBias

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumReconstruction
open BrownianPositiveBridgeConditioning BrownianFirstPassageBridgeLaw
open BrownianBridgeMinimumUniformTests BrownianPositiveBridgeFiniteDimensionalLaw
open BrownianBridgeCyclicPathLaw

def reverseTime (T : ℝ≥0) (s : ℝ) : ℝ≥0 := Real.toNNReal ((T : ℝ)-s)

theorem continuous_reverseTime (T : ℝ≥0) : Continuous (reverseTime T) :=
  continuous_real_toNNReal.comp (continuous_const.sub continuous_id)

theorem reverseTime_minimum (T : ℝ≥0) (f : Path) :
    reverseTime T (bridgeMinimumTime T f : ℝ) = T-bridgeMinimumTime T f := by
  rw [reverseTime,← NNReal.coe_sub (bridgeMinimumTime_le T f),Real.toNNReal_coe]

def lowHeightIndicator (T : ℝ≥0) (a : ℝ) (s : ℝ) (e : Path) : ℝ≥0∞ :=
  if e (reverseTime T s) < a then 1 else 0

theorem measurable_lowHeightIndicator (T : ℝ≥0) (a : ℝ) :
    Measurable (fun p : ℝ × Path ↦ lowHeightIndicator T a p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × Path ↦ p.2 (reverseTime T p.1)) :=
    continuous_joint_eval.measurable.comp
      (measurable_snd.prodMk ((continuous_reverseTime T).measurable.comp measurable_fst))
  exact Measurable.ite (measurableSet_lt hm measurable_const) measurable_const measurable_const

def lowHeightMass (T : ℝ≥0) (a : ℝ) (e : Path) : ℝ≥0∞ :=
  ∫⁻ s in Ioc 0 (T : ℝ), lowHeightIndicator T a s e

theorem measurable_lowHeightMass (T : ℝ≥0) (a : ℝ) : Measurable (lowHeightMass T a) :=
  (measurable_lowHeightIndicator T a).lintegral_prod_left'

def occupationDensity (T : ℝ≥0) (a : ℝ) (e : Path) : ℝ≥0∞ :=
  (normalization a T)⁻¹*(ENNReal.ofReal (T : ℝ))⁻¹*lowHeightMass T a e

theorem measurable_occupationDensity (T : ℝ≥0) (a : ℝ) : Measurable (occupationDensity T a) :=
  (measurable_lowHeightMass T a).const_mul _

theorem lowHeightMass_le_time (T : ℝ≥0) (a : ℝ) (e : Path) :
    lowHeightMass T a e ≤ ENNReal.ofReal (T : ℝ) := by
  calc
    _ ≤ ∫⁻ _s in Ioc 0 (T : ℝ), (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro s
      change (if e (reverseTime T s) < a then 1 else 0) ≤ 1
      split_ifs <;> simp only [le_refl,zero_le]
    _ = _ := by simp only [lintegral_one,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]

theorem actual_minimumShift_lintegral (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (minimumShiftPath T hT f) ∂positiveBridgeLaw a T) =
      ∫⁻ e, occupationDensity T a e*Ψ e ∂minimumShiftLaw T hT := by
  have hm := measurable_minimumShiftPath T hT
  rw [positiveBridgeLaw_lintegral a ha T hT (fun f ↦ Ψ (minimumShiftPath T hT f)) (hΨ.comp hm)]
  simp only [minimumShiftPath_translate]
  have he : (∫⁻ g in bridgeConstraint (-a) T 0, Ψ (minimumShiftPath T hT g) ∂pinnedLaw T) =
      ∫⁻ g, lowHeightIndicator T a (bridgeMinimumTime T g : ℝ) (minimumShiftPath T hT g)*
        Ψ (minimumShiftPath T hT g) ∂pinnedLaw T := by
    rw [← lintegral_indicator (measurableSet_bridgeConstraint (-a) T 0)]
    apply lintegral_congr_ae
    filter_upwards [ae_pinnedLaw_endpoints_zero T hT] with g hg
    have hmem := bridgeConstraint_iff_shifted_height a T hT g hg.1 hg.2
    rw [lowHeightIndicator,reverseTime_minimum]
    by_cases hc : g ∈ bridgeConstraint (-a) T 0
    · simp only [Set.indicator_of_mem hc,if_pos (hmem.mp hc),one_mul]
    · simp only [Set.indicator_of_notMem hc,if_neg (mt hmem.mpr hc),zero_mul]
  rw [he]
  have htest : Measurable (fun p : ℝ × Path ↦ lowHeightIndicator T a p.1 p.2*Ψ p.2) :=
    (measurable_lowHeightIndicator T a).mul (hΨ.comp measurable_snd)
  have hprod := lintegral_bridgePathLaw_minimum_joint_eq_uniform T hT _ htest
  change (∫⁻ g, lowHeightIndicator T a (bridgeMinimumTime T g : ℝ) (minimumShiftPath T hT g)*
      Ψ (minimumShiftPath T hT g) ∂pinnedLaw T) = _ at hprod
  rw [hprod,lintegral_lintegral_swap htest.aemeasurable]
  have hinner (e : Path) : (∫⁻ s in Ioc 0 (T : ℝ), lowHeightIndicator T a s e*Ψ e) =
      lowHeightMass T a e*Ψ e :=
    lintegral_mul_const (Ψ e) ((measurable_lowHeightIndicator T a).comp
      (measurable_id.prodMk measurable_const))
  simp_rw [hinner]
  rw [← lintegral_const_mul _ (f := fun e ↦ lowHeightMass T a e*Ψ e)
    ((measurable_lowHeightMass T a).mul hΨ),
    ← lintegral_const_mul _ (f := fun e ↦ (ENNReal.ofReal (T : ℝ))⁻¹*(lowHeightMass T a e*Ψ e))
      (((measurable_lowHeightMass T a).mul hΨ).const_mul _)]
  congr 1
  funext e
  simp only [occupationDensity,normalization]
  ring

theorem actual_minimumShiftLaw_eq_occupation_bias (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) :
    (positiveBridgeLaw a T).map (minimumShiftPath T hT) =
      (minimumShiftLaw T hT).withDensity (occupationDensity T a) := by
  apply Measure.ext
  intro B hB
  have he := actual_minimumShift_lintegral a ha T hT (B.indicator (fun _ ↦ 1))
    (measurable_const.indicator hB)
  rw [← lintegral_map (measurable_const.indicator hB) (measurable_minimumShiftPath T hT),
    show (fun _ : Path ↦ (1 : ℝ≥0∞)) = (1 : Path → ℝ≥0∞) from rfl,
    lintegral_indicator_one hB] at he
  rw [withDensity_apply _ hB,he]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro e
  by_cases heB : e ∈ B <;> simp [Set.indicator,heB]

theorem occupationDensity_integral_one (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ e, occupationDensity T a e ∂minimumShiftLaw T hT) = 1 := by
  let := positiveBridgeLaw_isProbability a ha T hT
  have he := actual_minimumShift_lintegral a ha T hT (fun _ ↦ 1) measurable_const
  simpa only [lintegral_one,mul_one,measure_univ] using he.symm

theorem occupation_bias_isProbability (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure ((minimumShiftLaw T hT).withDensity (occupationDensity T a)) := by
  rw [← actual_minimumShiftLaw_eq_occupation_bias a ha T hT]
  let := positiveBridgeLaw_isProbability a ha T hT
  exact Measure.isProbabilityMeasure_map (measurable_minimumShiftPath T hT).aemeasurable

theorem lowHeightMass_expectation (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ e, lowHeightMass T a e ∂minimumShiftLaw T hT) =
      ENNReal.ofReal (T : ℝ)*normalization a T := by
  have hN0 : normalization a T ≠ 0 := by
    have hp := BrownianBridgeSurvivalLaw.bridgeConstraint_probability_zero_endpoint_pos a ha T hT
    rw [BrownianBridgeSurvivalLaw.bridgeConstraint_probability_zero_endpoint a ha T hT] at hp
    exact ne_of_gt hp
  have hNtop : normalization a T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hT0 : ENNReal.ofReal (T : ℝ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hT)
  have he : (normalization a T*ENNReal.ofReal (T : ℝ))*
      ((normalization a T)⁻¹*(ENNReal.ofReal (T : ℝ))⁻¹) = 1 := by
    rw [mul_mul_mul_comm,ENNReal.mul_inv_cancel hN0 hNtop,
      ENNReal.mul_inv_cancel hT0 ENNReal.ofReal_ne_top,one_mul]
  have hm := occupationDensity_integral_one a ha T hT
  unfold occupationDensity at hm
  rw [lintegral_const_mul _ (measurable_lowHeightMass T a)] at hm
  calc
    _ = 1*(∫⁻ e, lowHeightMass T a e ∂minimumShiftLaw T hT) := (one_mul _).symm
    _ = (normalization a T*ENNReal.ofReal (T : ℝ))*
        (((normalization a T)⁻¹*(ENNReal.ofReal (T : ℝ))⁻¹)*
          (∫⁻ e, lowHeightMass T a e ∂minimumShiftLaw T hT)) := by rw [← mul_assoc,he]
    _ = _ := by rw [hm,mul_one,mul_comm]

end PerronWright.BrownianBridgeMinimumOccupationBias
