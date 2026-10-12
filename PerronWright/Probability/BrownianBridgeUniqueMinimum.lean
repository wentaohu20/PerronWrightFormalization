import PerronWright.Probability.BrownianBridgeSeparatedMinima
import PerronWright.Probability.BrownianBridgeNegativeMinimum

/-! # The actual Gaussian pinned bridge has a unique interior minimum

The proved null ties for separated compact intervals are intersected
over rational endpoints. Any two distinct global minimizing times are
contained in two such intervals. The previously proved actual negative
minimum excludes the endpoints. No minimum uniqueness is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeUniqueMinimum

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCyclicPath BrownianBridgeMinimumShift
open BrownianBridgeAreaTiltPathLaw BrownianBridgeNegativeMinimum BrownianBridgeSeparatedMinima
open ContinuousPathIntervalMinimum

theorem ae_no_two_ordered_minimizers (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ s t : ℝ≥0, s < t → t ≤ T →
      closedBridge T s f = bridgeMinimumValue T f →
      closedBridge T t f = bridgeMinimumValue T f → False := by
  have hAll : ∀ᵐ f ∂pathLaw, ∀ a b w : ℚ,
      Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) →
      Real.toNNReal (b : ℝ) ≤ Real.toNNReal (w : ℝ) → Real.toNNReal (w : ℝ) < T →
      intervalMinimum 0 (Real.toNNReal (a : ℝ)) (stoppedBridgePath T f) ≠
        intervalMinimum (Real.toNNReal (b : ℝ)) (Real.toNNReal (w : ℝ)) (stoppedBridgePath T f) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro w
    by_cases hab : Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ)
    · by_cases hbw : Real.toNNReal (b : ℝ) ≤ Real.toNNReal (w : ℝ)
      · by_cases hw : Real.toNNReal (w : ℝ) < T
        · filter_upwards [ae_separated_interval_minima_ne T 0 _ _ _ hT zero_le hab hbw hw] with f hf
          exact fun _ _ _ ↦ hf
        · exact Filter.Eventually.of_forall (fun _ _ _ h ↦ (hw h).elim)
      · exact Filter.Eventually.of_forall (fun _ _ h ↦ (hbw h).elim)
    · exact Filter.Eventually.of_forall (fun _ h ↦ (hab h).elim)
  filter_upwards [hAll,ae_bridgeMinimumValue_negative T hT,ae_closedBridge_eq_bridge T] with f hall hneg hclosed
  intro s t hst ht hsmin htmin
  have htne : t ≠ T := by
    intro he
    rw [← htmin,he,closedBridge_endpoint T hT f] at hneg
    exact lt_irrefl _ hneg
  have htlt : t < T := lt_of_le_of_ne ht htne
  obtain ⟨a,hsa,hat⟩ := exists_rat_btwn (show (s : ℝ) < t from hst)
  obtain ⟨b,hab,hbt⟩ := exists_rat_btwn hat
  obtain ⟨w,htw,hwT⟩ := exists_rat_btwn (show (t : ℝ) < T from htlt)
  have ha0 : 0 ≤ (a : ℝ) := s.coe_nonneg.trans hsa.le
  have hw0 : 0 ≤ (w : ℝ) := t.coe_nonneg.trans htw.le
  have hsa' : s ≤ Real.toNNReal (a : ℝ) := (Real.le_toNNReal_iff_coe_le ha0).mpr hsa.le
  have hab' : Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) :=
    (Real.toNNReal_lt_toNNReal_iff (ha0.trans_lt hab)).mpr hab
  have hbt' : Real.toNNReal (b : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.mpr hbt.le
  have htw' : t ≤ Real.toNNReal (w : ℝ) := (Real.le_toNNReal_iff_coe_le hw0).mpr htw.le
  have hwT' : Real.toNNReal (w : ℝ) < T := (Real.toNNReal_lt_iff_lt_coe hw0).mpr hwT
  have hbw' := hbt'.trans htw'
  have haT := (hab'.le.trans hbw').trans hwT'.le
  have heLeft : intervalMinimum 0 (Real.toNNReal (a : ℝ)) (stoppedBridgePath T f) = bridgeMinimumValue T f := by
    apply intervalMinimum_eq_of_attains 0 _ zero_le
    · intro u hu
      change bridgeMinimumValue T f ≤ bridge T (min u T) f
      rw [min_eq_left (hu.2.trans haT),← hclosed]
      exact bridgeMinimumValue_le T f u (hu.2.trans haT)
    · refine ⟨s,⟨zero_le,hsa'⟩,?_⟩
      change bridge T (min s T) f = _
      rw [min_eq_left (hst.le.trans ht),← hclosed]
      exact hsmin
  have heRight : intervalMinimum (Real.toNNReal (b : ℝ)) (Real.toNNReal (w : ℝ))
      (stoppedBridgePath T f) = bridgeMinimumValue T f := by
    apply intervalMinimum_eq_of_attains _ _ hbw'
    · intro u hu
      change bridgeMinimumValue T f ≤ bridge T (min u T) f
      rw [min_eq_left (hu.2.trans hwT'.le),← hclosed]
      exact bridgeMinimumValue_le T f u (hu.2.trans hwT'.le)
    · refine ⟨t,⟨hbt',htw'⟩,?_⟩
      change bridge T (min t T) f = _
      rw [min_eq_left ht,← hclosed]
      exact htmin
  exact hall a b w hab' hbw' hwT' (heLeft.trans heRight.symm)

theorem ae_closedBridge_unique_minimum (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ t : ℝ≥0, t ≤ T → closedBridge T t f = bridgeMinimumValue T f →
      t = bridgeMinimumTime T f := by
  filter_upwards [ae_no_two_ordered_minimizers T hT] with f hf
  intro t ht he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact hf t (bridgeMinimumTime T f) hlt (bridgeMinimumTime_le T f) he (bridgeMinimumTime_value T f)
  · exact hf (bridgeMinimumTime T f) t hgt ht (bridgeMinimumTime_value T f) he

/-- Actual literal pinned Brownian bridge coordinates have a unique
negative minimum strictly inside the compact horizon. -/
theorem ae_actual_bridge_unique_interior_minimum (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∃! t : ℝ≥0, t ≤ T ∧
      (∀ s : ℝ≥0, s ≤ T → bridge T t f ≤ bridge T s f) ∧
      0 < t ∧ t < T ∧ bridge T t f < 0 := by
  filter_upwards [ae_closedBridge_unique_minimum T hT,ae_bridgeMinimumTime_interior T hT,
    ae_bridgeMinimumValue_negative T hT,ae_closedBridge_eq_bridge T] with f huniq hint hneg hclosed
  refine ⟨bridgeMinimumTime T f,⟨bridgeMinimumTime_le T f,?_,hint.1,hint.2,?_⟩,?_⟩
  · intro s hs
    rw [← hclosed,← hclosed,bridgeMinimumTime_value]
    exact bridgeMinimumValue_le T f s hs
  · rw [← hclosed,bridgeMinimumTime_value]
    exact hneg
  · intro t ht
    apply huniq t ht.1
    apply le_antisymm
    · rw [← bridgeMinimumTime_value, hclosed]
      rw [hclosed]
      exact ht.2.1 _ (bridgeMinimumTime_le T f)
    · exact bridgeMinimumValue_le T f t ht.1

end PerronWright.BrownianBridgeUniqueMinimum
