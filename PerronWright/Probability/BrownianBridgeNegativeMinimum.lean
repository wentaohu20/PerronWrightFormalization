import PerronWright.Probability.BrownianBridgeCycleMinima
import PerronWright.Probability.BrownianBridgeDiffuseIncrements

/-! # The actual Brownian pinned bridge has a negative interior minimum

Infinitely many fixed minimum events have the same probability by the
proved actual cyclic law. Their intersections have zero probability by
the proved diffuse Gaussian increments. Countable additivity in the
actual probability measure forces that common probability to vanish.
Hence the genuine compact minimum is strictly negative, and its actual
earliest minimizer is strictly inside (0,T). No positivity-conditioning
or minimum-uniqueness interface is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeNegativeMinimum

open BrownianPathLaw BrownianBridgeCyclicPath BrownianBridgeMinimumShift
open BrownianBridgeCycleMinima BrownianBridgeDiffuseIncrements

def minimumGrid (T : ℝ≥0) (i : ℕ) : ℝ≥0 := T/((i : ℝ≥0)+2)

theorem minimumGrid_lt (T : ℝ≥0) (hT : 0 < T) (i : ℕ) : minimumGrid T i < T := by
  change (T/((i : ℝ≥0)+2) : ℝ) < (T : ℝ)
  simp only [NNReal.coe_natCast]
  apply (div_lt_iff₀ (by positivity : 0 < (i : ℝ)+2)).mpr
  have hi := Nat.cast_nonneg (α := ℝ) i
  have hp : 0 < (T : ℝ) := hT
  nlinarith

theorem minimumGrid_injective (T : ℝ≥0) (hT : 0 < T) : Function.Injective (minimumGrid T) := by
  intro i j he
  have hr := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) he
  change (T/((i : ℝ≥0)+2) : ℝ) = (T/((j : ℝ≥0)+2) : ℝ) at hr
  simp only [NNReal.coe_natCast] at hr
  have hi : (i : ℝ)+2 ≠ 0 := by positivity
  have hj : (j : ℝ)+2 ≠ 0 := by positivity
  have hx := (div_eq_div_iff hi hj).mp hr
  have hp : 0 < (T : ℝ) := hT
  have he' : (i : ℝ) = j := by nlinarith
  exact_mod_cast he'

theorem fixedMinimumEvent_zero_measure (T : ℝ≥0) (hT : 0 < T) :
    pathLaw (fixedMinimumEvent T 0) = 0 := by
  let E : ℕ → Set Path := fun i ↦ fixedMinimumEvent T (minimumGrid T i)
  have hd : Pairwise (fun i j ↦ AEDisjoint pathLaw (E i) (E j)) := by
    intro i j hij
    have hne := ae_closedBridge_values_ne T (minimumGrid T i) (minimumGrid T j) hT
      (minimumGrid_lt T hT i) (minimumGrid_lt T hT j)
      (fun he ↦ hij (minimumGrid_injective T hT he))
    have hz : pathLaw {f | closedBridge T (minimumGrid T i) f = closedBridge T (minimumGrid T j) f} = 0 := by
      simpa only [ae_iff,not_not] using hne
    apply measure_mono_null _ hz
    intro f hf
    exact hf.1.symm.trans hf.2
  have hm : ∀ i, NullMeasurableSet (E i) pathLaw :=
    fun i ↦ (measurableSet_fixedMinimumEvent T (minimumGrid T i)).nullMeasurableSet
  have he := measure_iUnion₀ hd hm
  have hp (i : ℕ) : pathLaw (E i) = pathLaw (fixedMinimumEvent T 0) :=
    fixedMinimumEvent_measure_eq T _ hT (minimumGrid_lt T hT i).le
  simp only [hp] at he
  by_contra hn
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hn] at he
  exact measure_ne_top pathLaw (⋃ i, E i) he

theorem ae_bridgeMinimumValue_negative (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, bridgeMinimumValue T f < 0 := by
  have he : {f : Path | ¬bridgeMinimumValue T f < 0} = fixedMinimumEvent T 0 := by
    ext f
    have hn : bridgeMinimumValue T f ≤ 0 := by
      simpa only [closedBridge_zero] using bridgeMinimumValue_le T f 0 zero_le
    change ¬bridgeMinimumValue T f < 0 ↔ bridgeMinimumValue T f = closedBridge T 0 f
    rw [closedBridge_zero]
    exact ⟨fun h ↦ le_antisymm hn (le_of_not_gt h),fun h ↦ by rw [h]; exact lt_irrefl _⟩
  apply ae_iff.mpr
  rw [he,fixedMinimumEvent_zero_measure T hT]

theorem ae_bridgeMinimumTime_interior (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, 0 < bridgeMinimumTime T f ∧ bridgeMinimumTime T f < T := by
  filter_upwards [ae_bridgeMinimumValue_negative T hT] with f hf
  have h0 : bridgeMinimumTime T f ≠ 0 := by
    intro he
    rw [← bridgeMinimumTime_value T f,he,closedBridge_zero] at hf
    exact lt_irrefl _ hf
  have hEnd : bridgeMinimumTime T f ≠ T := by
    intro he
    rw [← bridgeMinimumTime_value T f,he,closedBridge_endpoint T hT f] at hf
    exact lt_irrefl _ hf
  refine ⟨pos_iff_ne_zero.mpr h0,?_⟩
  by_contra hn
  exact hEnd (le_antisymm (bridgeMinimumTime_le T f) (le_of_not_gt hn))

/-- Literal coordinates of the actual pinned Brownian bridge, not only
a newly named minimum functional, attain their negative minimum inside (0,T). -/
theorem ae_actual_bridge_negative_minimum (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∃ t : ℝ≥0, 0 < t ∧ t < T ∧ BrownianPinnedBridge.bridge T t f < 0 ∧
      ∀ s : ℝ≥0, s ≤ T → BrownianPinnedBridge.bridge T t f ≤ BrownianPinnedBridge.bridge T s f := by
  filter_upwards [ae_bridgeMinimumValue_negative T hT,ae_bridgeMinimumTime_interior T hT,
    ae_closedBridge_eq_bridge T] with f hf hi he
  refine ⟨bridgeMinimumTime T f,hi.1,hi.2,?_,?_⟩
  · rw [← he,bridgeMinimumTime_value]
    exact hf
  · intro s hs
    rw [← he,← he,bridgeMinimumTime_value]
    exact bridgeMinimumValue_le T f s hs

end PerronWright.BrownianBridgeNegativeMinimum
