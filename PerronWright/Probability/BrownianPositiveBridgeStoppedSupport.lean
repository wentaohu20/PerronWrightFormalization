import PerronWright.Probability.BrownianPositiveBridgeConditioning

/-! # Actual positive bridge laws live on stopped continuous paths

The support property follows from the genuine stopped pinned source and
absolute continuity of conditioning. The common initial bound follows
from the actual endpoint value. Neither support nor tightness is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeStoppedSupport

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeAreaTiltPathLaw
open BrownianFirstPassageBridgeLaw BrownianPositiveBridgeConditioning

def stoppedPaths (T : ℝ≥0) : Set Path := {g | ∀ t : ℝ≥0, g t = g (min t T)}

theorem isClosed_stoppedPaths (T : ℝ≥0) : IsClosed (stoppedPaths T) := by
  have he : stoppedPaths T = ⋂ t : ℝ≥0, {g : Path | g t = g (min t T)} := by
    ext g
    simp only [stoppedPaths,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter (fun t ↦ isClosed_eq (continuous_eval t) (continuous_eval (min t T)))

theorem measurableSet_stoppedPaths (T : ℝ≥0) : MeasurableSet (stoppedPaths T) :=
  (isClosed_stoppedPaths T).measurableSet

theorem ae_pinnedLaw_stopped (T : ℝ≥0) : ∀ᵐ g ∂pinnedLaw T, g ∈ stoppedPaths T := by
  apply (ae_map_iff (measurable_stoppedBridgePath T).aemeasurable (measurableSet_stoppedPaths T)).mpr
  apply ae_of_all
  intro f
  change ∀ t : ℝ≥0, bridge T (min t T) f = bridge T (min (min t T) T) f
  intro t
  rw [min_assoc,min_self]

theorem ae_conditionedLaw_stopped (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ g ∂conditionedLaw a T, g ∈ stoppedPaths T := by
  have hAC : conditionedLaw a T ≪ pinnedLaw T := cond_absolutelyContinuous
  exact hAC.ae_le (ae_pinnedLaw_stopped T)

theorem ae_positiveBridgeLaw_stopped (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ g ∂positiveBridgeLaw a T, g ∈ stoppedPaths T := by
  apply (ae_map_iff (measurable_translate a).aemeasurable (measurableSet_stoppedPaths T)).mpr
  filter_upwards [ae_conditionedLaw_stopped a T] with g hg
  intro t
  change g t+a = g (min t T)+a
  rw [hg t]

theorem ae_positiveBridgeLaw_constant_after (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ g ∂positiveBridgeLaw a T, ∀ t : ℝ≥0, T ≤ t → g t = g T := by
  filter_upwards [ae_positiveBridgeLaw_stopped a T] with g hg
  intro t ht
  simpa only [min_eq_right ht] using hg t

theorem eventually_ae_initial_norm_le_one (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ g ∂positiveBridgeLaw a T, ‖g 0‖ ≤ 1 := by
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hsmall] with a ha ha1
  filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
  rw [hg.1,Real.norm_eq_abs,abs_of_pos ha]
  exact ha1.le

end PerronWright.BrownianPositiveBridgeStoppedSupport
