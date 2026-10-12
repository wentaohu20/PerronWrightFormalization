import PerronWright.Probability.BrownianBridgeCircleGeometry

/-! # Literal measurable reverse cyclic offset

The two-piece nonnegative-time formula is proved equal to signed circle
reduction on the actual interval. No uniform distribution is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeRotationOffset

open BrownianBridgeCircleGeometry

def reverseOffset (T s m : ℝ≥0) : ℝ≥0 := if s ≤ m then m-s else T-s+m

theorem measurable_joint_reverseOffset (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × ℝ≥0 ↦ reverseOffset T p.1 p.2) := by
  unfold reverseOffset
  exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    (measurable_snd.sub measurable_fst) ((measurable_const.sub measurable_fst).add measurable_snd)

theorem measurable_reverseOffset (T s : ℝ≥0) : Measurable (reverseOffset T s) :=
  (measurable_joint_reverseOffset T).comp (measurable_const.prodMk measurable_id)

theorem reverseOffset_eq_circleTime (T s m : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (hm : m < T) :
    reverseOffset T s m = circleTime T hT ((m : ℝ)-(s : ℝ)) := by
  unfold reverseOffset
  by_cases hsm : s ≤ m
  · rw [if_pos hsm,← NNReal.coe_sub hsm]
    exact (circleTime_eq_self T (m-s) hT ((tsub_le_self).trans_lt hm)).symm
  · rw [if_neg hsm]
    have hms : m < s := lt_of_not_ge hsm
    have hr : T-s+m < T := NNReal.coe_lt_coe.mp (by
      rw [NNReal.coe_add,NNReal.coe_sub hs]
      have he : (m : ℝ) < s := hms
      linarith)
    have he : (T : ℝ)+((m : ℝ)-(s : ℝ)) = (T-s+m : ℝ≥0) := by
      rw [NNReal.coe_add,NNReal.coe_sub hs]
      ring
    unfold circleTime
    rw [← toIcoMod_add_left (show 0 < (T : ℝ) from hT) 0 ((m : ℝ)-(s : ℝ)),he,
      (toIcoMod_eq_self (show 0 < (T : ℝ) from hT)).mpr
        ⟨(T-s+m).coe_nonneg,by simpa only [zero_add] using
          (show ((T-s+m : ℝ≥0) : ℝ) < (T : ℝ) from hr)⟩,
      Real.toNNReal_coe]

theorem reverseOffset_lt (T s m : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (hm : m < T) :
    reverseOffset T s m < T := by
  rw [reverseOffset_eq_circleTime T s m hT hs hm]
  exact circleTime_lt T hT _

end PerronWright.BrownianBridgeRotationOffset
