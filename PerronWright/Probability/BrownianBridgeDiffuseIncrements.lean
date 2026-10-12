import PerronWright.Probability.BrownianBridgeMinimumShift

/-! # Actual pinned-bridge increments are diffuse

Finite linear Gaussian laws give the exact variance d(T-d)/T for a
cyclic increment. For distinct times below T this is strictly positive,
so equality of the true closed-bridge values has probability zero.
No non-atomicity or minimum-uniqueness interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeDiffuseIncrements

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianBridgeCycleKernel BrownianBridgeCyclicPath BrownianBridgeCyclicFiniteLaw

theorem hasLaw_rotation_eval (T s t : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (ht : t ≤ T) :
    HasLaw (rotation T s t) (gaussianReal 0
      (Real.toNNReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ)))) pathLaw := by
  have he : linearRotationTest T s (fun _ : Unit ↦ t) (fun _ ↦ (1 : ℝ)) = rotation T s t := by
    funext f
    simp only [linearRotationTest,Fintype.sum_unique,one_mul]
  have hv : quadraticVariance T (fun _ : Unit ↦ t) (fun _ ↦ (1 : ℝ)) =
      (t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ) := by
    simp only [quadraticVariance,Fintype.sum_unique,one_mul,min_self]
    field_simp
  have h := hasLaw_linearRotationTest T s hT hs (fun _ : Unit ↦ t) (fun _ ↦ ht) (fun _ ↦ 1)
  rwa [he,hv] at h

theorem ae_rotation_ne_zero (T s t : ℝ≥0) (hT : 0 < T) (hs : s ≤ T)
    (ht0 : 0 < t) (ht : t < T) : ∀ᵐ f ∂pathLaw, rotation T s t f ≠ 0 := by
  have hp : 0 < (t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ) :=
    div_pos (mul_pos (show 0 < (t : ℝ) from ht0) (sub_pos.mpr (show (t : ℝ) < T from ht))) hT
  let := nullSingletonClass_gaussianReal (μ := 0)
    (show Real.toNNReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ)) ≠ 0 from
      ne_of_gt (Real.toNNReal_pos.mpr hp))
  have hm := (hasLaw_rotation_eval T s t hT hs ht.le).measure_eq
    (p := fun x : ℝ ↦ x=0) (by exact measurableSet_singleton 0)
  have hz : pathLaw {f | rotation T s t f = 0} = 0 := by
    simpa only [ofPred_eq_eq_singleton,measure_singleton] using hm
  simpa only [ae_iff,not_not] using hz

private theorem ae_bridge_values_ne_ordered (T s u : ℝ≥0) (hT : 0 < T)
    (hsu : s < u) (hu : u < T) : ∀ᵐ f ∂pathLaw, bridge T s f ≠ bridge T u f := by
  have hd0 : 0 < u-s := tsub_pos_iff_lt.mpr hsu
  have hd : u-s < T := lt_of_le_of_lt tsub_le_self hu
  have h := ae_rotation_ne_zero T s (u-s) hT (hsu.le.trans hu.le) hd0 hd
  have he : cycleTime T s (u-s)=u := by
    simp only [cycleTime,add_tsub_cancel_of_le hsu.le,if_pos hu.le]
  filter_upwards [h] with f hf
  intro hsu'
  apply hf
  simp only [rotation,he,hsu',sub_self]

theorem ae_closedBridge_values_ne (T s u : ℝ≥0) (hT : 0 < T)
    (hs : s < T) (hu : u < T) (hne : s ≠ u) :
    ∀ᵐ f ∂pathLaw, closedBridge T s f ≠ closedBridge T u f := by
  have h : ∀ᵐ f ∂pathLaw, bridge T s f ≠ bridge T u f := by
    rcases lt_or_gt_of_ne hne with hsu|hus
    · exact ae_bridge_values_ne_ordered T s u hT hsu hu
    · filter_upwards [ae_bridge_values_ne_ordered T u s hT hus hs] with f hf
      exact Ne.symm hf
  filter_upwards [h,ae_closedBridge_eq_bridge T] with f hf he
  simpa only [he] using hf

end PerronWright.BrownianBridgeDiffuseIncrements
