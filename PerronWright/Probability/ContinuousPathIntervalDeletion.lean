import PerronWright.Probability.BrownianPathReflectionLaw
import Mathlib.Topology.Order.OrderClosed

/-! # Genuine continuous interval deletion and the parabolic parameter shift

A compensated splice is jointly continuous for every input path. When the
two cut endpoints agree, it is the literal removal of that interval.
Adding the concrete bounded-time linear correction to the Brownian splice
gives the exact remaining parabolic parameter lambda minus the cut length.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ContinuousPathIntervalDeletion

open BrownianPathLaw BrownianPathReflectionLaw

private def cutValue (a l : ℝ≥0) (f : Path) (t : ℝ≥0) : ℝ :=
  if t ≤ a then f t else f (t+l)-f (a+l)+f a

private theorem continuous_joint_cutValue :
    Continuous (fun p : (Path × ℝ≥0 × ℝ≥0) × ℝ≥0 ↦ cutValue p.1.2.1 p.1.2.2 p.1.1 p.2) := by
  have hleft : Continuous (fun p : (Path × ℝ≥0 × ℝ≥0) × ℝ≥0 ↦ p.1.1 p.2) :=
    continuous_fst.fst.eval continuous_snd
  have hright : Continuous (fun p : (Path × ℝ≥0 × ℝ≥0) × ℝ≥0 ↦
      p.1.1 (p.2+p.1.2.2)-p.1.1 (p.1.2.1+p.1.2.2)+p.1.1 p.1.2.1) :=
    ((continuous_fst.fst.eval (continuous_snd.add continuous_fst.snd.snd)).sub
      (continuous_fst.fst.eval (continuous_fst.snd.fst.add continuous_fst.snd.snd))).add
        (continuous_fst.fst.eval continuous_fst.snd.fst)
  exact Continuous.if_le hleft hright continuous_snd continuous_fst.snd.fst
    (fun p he ↦ by simp only [he,sub_self,zero_add])

def deletionPath (a l : ℝ≥0) (f : Path) : Path :=
  ⟨cutValue a l f,by
    simpa only [Function.comp_def] using continuous_joint_cutValue.comp
      (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ≥0 ↦ ((f,a,l),t)))⟩

theorem deletionPath_apply (a l : ℝ≥0) (f : Path) (t : ℝ≥0) :
    deletionPath a l f t = if t ≤ a then f t else f (t+l)-f (a+l)+f a := rfl

theorem continuous_joint_deletionPath :
    Continuous (fun p : Path × ℝ≥0 × ℝ≥0 ↦ deletionPath p.2.1 p.2.2 p.1) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_joint_cutValue

theorem measurable_joint_deletionPath :
    Measurable (fun p : Path × ℝ≥0 × ℝ≥0 ↦ deletionPath p.2.1 p.2.2 p.1) :=
  continuous_joint_deletionPath.measurable

theorem deletionPath_closed_apply (a l : ℝ≥0) (f : Path) (hclosed : f (a+l) = f a)
    (t : ℝ≥0) : deletionPath a l f t = if t ≤ a then f t else f (t+l) := by
  rw [deletionPath_apply,hclosed]
  split_ifs <;> ring

def correctedDeletionPath (a l : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ deletionPath a l f t+(l : ℝ)*(min t a : ℝ≥0),
    (continuous_path (deletionPath a l f)).add
      (continuous_const.mul (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))⟩

theorem correctedDeletionPath_apply (a l : ℝ≥0) (f : Path) (t : ℝ≥0) :
    correctedDeletionPath a l f t = deletionPath a l f t+(l : ℝ)*(min t a : ℝ≥0) := rfl

theorem continuous_joint_correctedDeletionPath :
    Continuous (fun p : Path × ℝ≥0 × ℝ≥0 ↦ correctedDeletionPath p.2.1 p.2.2 p.1) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_joint_cutValue.add
    ((NNReal.continuous_coe.comp continuous_fst.snd.snd).mul
      (NNReal.continuous_coe.comp (continuous_snd.min continuous_fst.snd.fst)))

theorem parabolic_deletion_eq (lambda : ℝ) (a l : ℝ≥0) (f : Path) :
    deletionPath a l (driftPath lambda f) =
      driftPath (lambda-(l : ℝ)) (correctedDeletionPath a l f) := by
  apply ContinuousMap.ext
  intro t
  change (if t ≤ a then f t+lambda*(t : ℝ)-(t : ℝ)^2/2 else
      (f (t+l)+lambda*(t+l : ℝ≥0)-(t+l : ℝ≥0)^2/2)-
        (f (a+l)+lambda*(a+l : ℝ≥0)-(a+l : ℝ≥0)^2/2)+
          (f a+lambda*(a : ℝ)-(a : ℝ)^2/2)) =
    ((if t ≤ a then f t else f (t+l)-f (a+l)+f a)+(l : ℝ)*(min t a : ℝ≥0))+
      (lambda-(l : ℝ))*(t : ℝ)-(t : ℝ)^2/2
  by_cases ht : t ≤ a
  · simp only [if_pos ht,min_eq_left ht]
    ring
  · simp only [if_neg ht,min_eq_right (le_of_not_ge ht),NNReal.coe_add]
    ring

end PerronWright.ContinuousPathIntervalDeletion
