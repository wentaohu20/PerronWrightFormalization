import PerronWright.Probability.BrownianBridgeMinimumStrictPositivity

/-! # Exact circle reduction and closed-bridge cyclic group geometry

Signed real offsets are reduced to [0,T). The actual closed bridge
endpoint equivalence makes cyclic composition a genuine group action
on path values. No minimum distribution is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeCircleGeometry

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCyclicPath
open BrownianBridgeCyclicGeometry BrownianBridgeCycleKernel

def circleTime (T : ℝ≥0) (hT : 0 < T) (x : ℝ) : ℝ≥0 :=
  Real.toNNReal (toIcoMod (show 0 < (T : ℝ) from hT) 0 x)

theorem circleTime_coe (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    (circleTime T hT x : ℝ) = toIcoMod (show 0 < (T : ℝ) from hT) 0 x :=
  Real.coe_toNNReal _ (left_le_toIcoMod _ 0 x)

theorem circleTime_lt (T : ℝ≥0) (hT : 0 < T) (x : ℝ) : circleTime T hT x < T := by
  change (circleTime T hT x : ℝ) < (T : ℝ)
  rw [circleTime_coe]
  simpa only [zero_add] using toIcoMod_lt_right (show 0 < (T : ℝ) from hT) 0 x

theorem circleTime_eq_self (T t : ℝ≥0) (hT : 0 < T) (ht : t < T) :
    circleTime T hT (t : ℝ) = t := by
  unfold circleTime
  rw [(toIcoMod_eq_self (show 0 < (T : ℝ) from hT)).mpr
    ⟨t.coe_nonneg,by simpa only [zero_add] using (show (t : ℝ) < T from ht)⟩,Real.toNNReal_coe]

theorem circleTime_period (T : ℝ≥0) (hT : 0 < T) : circleTime T hT (T : ℝ) = 0 := by
  unfold circleTime
  have he : toIcoMod (show 0 < (T : ℝ) from hT) 0 (T : ℝ) = 0 := by
    simpa only [zero_add] using toIcoMod_apply_right (show 0 < (T : ℝ) from hT) 0
  rw [he,Real.toNNReal_zero]

theorem circleTime_reduce_add (T : ℝ≥0) (hT : 0 < T) (x y : ℝ) :
    circleTime T hT ((circleTime T hT x : ℝ)+y) = circleTime T hT (x+y) := by
  unfold circleTime
  rw [Real.coe_toNNReal _ (left_le_toIcoMod _ 0 x)]
  congr 1
  apply (toIcoMod_eq_toIcoMod (show 0 < (T : ℝ) from hT)).mpr
  refine ⟨toIcoDiv (show 0 < (T : ℝ) from hT) 0 x,?_⟩
  convert self_sub_toIcoMod (show 0 < (T : ℝ) from hT) 0 x using 1
  ring

theorem circleTime_add_reduce (T : ℝ≥0) (hT : 0 < T) (x y : ℝ) :
    circleTime T hT (x+(circleTime T hT y : ℝ)) = circleTime T hT (x+y) := by
  rw [add_comm x,circleTime_reduce_add,add_comm y]

theorem circleTime_sub_inverse (T m s : ℝ≥0) (hT : 0 < T) (hm : m < T) :
    circleTime T hT ((s : ℝ)+(circleTime T hT ((m : ℝ)-(s : ℝ)) : ℝ)) = m := by
  rw [circleTime_add_reduce]
  have he : (s : ℝ)+((m : ℝ)-(s : ℝ)) = m := by ring
  rw [he,circleTime_eq_self T m hT hm]

theorem circleTime_cancel_shift (T x s : ℝ≥0) (hT : 0 < T) (hx : x < T) :
    circleTime T hT (-(s : ℝ)+(circleTime T hT ((s : ℝ)+(x : ℝ)) : ℝ)) = x := by
  rw [circleTime_add_reduce]
  have he : -(s : ℝ)+((s : ℝ)+(x : ℝ)) = x := by ring
  rw [he,circleTime_eq_self T x hT hx]

theorem closedBridge_circleTime (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (f : Path) :
    closedBridge T (circleTime T hT (t : ℝ)) f = closedBridge T t f := by
  rcases lt_or_eq_of_le ht with hlt|he
  · rw [circleTime_eq_self T t hT hlt]
  · rw [he,circleTime_period,closedBridge_zero,closedBridge_endpoint T hT f]

theorem cyclicBridgePath_eq_circle (T s t : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (f : Path) :
    cyclicBridgePath T hT s f t =
      closedBridge T (circleTime T hT ((s : ℝ)+(min t T : ℝ≥0))) f-closedBridge T s f :=
  cyclicBridgePath_eq_modulo T s t hT hs f

theorem closedBridge_cyclicBridgePath (T s t : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path) :
    closedBridge T t (cyclicBridgePath T hT s f) = cyclicBridgePath T hT s f t := by
  unfold closedBridge bridge
  rw [cyclicBridgePath_zero T hT s hs f,cyclicBridgePath_endpoint T hT s f]
  ring

theorem cyclicBridgePath_compose (T s u : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (hu : u ≤ T) (f : Path) :
    cyclicBridgePath T hT u (cyclicBridgePath T hT s f) =
      cyclicBridgePath T hT (circleTime T hT ((s : ℝ)+(u : ℝ))) f := by
  apply ContinuousMap.ext
  intro t
  rw [cyclicBridgePath_eq_circle T u t hT hu,closedBridge_cyclicBridgePath T s _ hT hs,
    closedBridge_cyclicBridgePath T s u hT hs,
    cyclicBridgePath_eq_circle T s _ hT hs,cyclicBridgePath_eq_circle T s u hT hs,
    cyclicBridgePath_eq_circle T _ t hT (circleTime_lt T hT _).le]
  rw [min_eq_left (circleTime_lt T hT _).le,min_eq_left hu,
    circleTime_add_reduce,circleTime_reduce_add]
  simp only [sub_sub_sub_cancel_right,add_assoc]

end PerronWright.BrownianBridgeCircleGeometry
