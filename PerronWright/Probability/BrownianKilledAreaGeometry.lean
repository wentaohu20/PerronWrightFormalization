import PerronWright.Probability.BrownianKilledSemigroup
import PerronWright.Probability.BrownianBridgeCyclicArea

/-! # Literal path-area addition on actual surviving Brownian segments

All identities here are deterministic identities of the actual continuous
paths, including zero durations. Survival makes the area above the killing
boundary nonnegative. These give the genuine area weight used in the
killed-area transition kernel; no Feynman--Kac identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section

namespace PerronWright.BrownianKilledAreaGeometry

open BrownianPathLaw BrownianPathIndependentIncrements BrownianBridgeCyclicArea
open ContinuousPathFirstPassage

theorem pathArea_future_segment (s t : ℝ≥0) (f : Path) :
    (∫ r in (s : ℝ)..((s+t : ℝ≥0) : ℝ), f (Real.toNNReal r)) =
      pathArea t (futurePath s f)+(t : ℝ)*f s := by
  have he := intervalIntegral.integral_comp_add_left
    (fun r : ℝ ↦ f (Real.toNNReal r)) (s : ℝ) (a := 0) (b := (t : ℝ))
  rw [add_zero] at he
  rw [NNReal.coe_add,← he]
  have hi : (∫ r in (0 : ℝ)..(t : ℝ), f (Real.toNNReal ((s : ℝ)+r))) =
      ∫ r in (0 : ℝ)..(t : ℝ), futurePath s f (Real.toNNReal r)+f s := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := (by simpa only [uIcc_of_le t.coe_nonneg] using hr : r ∈ Icc 0 (t : ℝ)).1
    have hn : Real.toNNReal ((s : ℝ)+r) = s+Real.toNNReal r := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ (add_nonneg s.coe_nonneg hr0),NNReal.coe_add,
        Real.coe_toNNReal _ hr0]
    dsimp only
    rw [hn,futurePath_eval,sub_add_cancel]
  have hfuture : IntervalIntegrable (fun r : ℝ ↦ futurePath s f (Real.toNNReal r))
      volume 0 t :=
    (((continuous_path (futurePath s f)).comp continuous_real_toNNReal).intervalIntegrable 0 t)
  rw [hi,intervalIntegral.integral_add hfuture
    intervalIntegrable_const,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,pathArea]

theorem pathArea_add (s t : ℝ≥0) (f : Path) :
    pathArea (s+t) f = pathArea s f+pathArea t (futurePath s f)+(t : ℝ)*f s := by
  have hc : Continuous (fun r : ℝ ↦ f (Real.toNNReal r)) :=
    (continuous_path f).comp continuous_real_toNNReal
  change (∫ r in (0 : ℝ)..((s+t : ℝ≥0) : ℝ), f (Real.toNNReal r)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s ((s+t : ℝ≥0) : ℝ)),
    pathArea_future_segment]
  simp only [pathArea,add_assoc]

theorem pathArea_past (t : ℝ≥0) (f : Path) : pathArea t (pastPath t f) = pathArea t f := by
  unfold pathArea
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ≤ (t : ℝ) := (by simpa only [uIcc_of_le t.coe_nonneg] using hr : r ∈ Icc 0 (t : ℝ)).2
  dsimp only
  rw [pastPath_eval,min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hrT)]

def shiftedArea (level x : ℝ) (t : ℝ≥0) (f : Path) : ℝ :=
  (t : ℝ)*(x-level)+pathArea t f

theorem measurable_joint_shiftedArea (level : ℝ) (t : ℝ≥0) :
    Measurable (fun p : ℝ × Path ↦ shiftedArea level p.1 t p.2) :=
  (measurable_const.mul (measurable_fst.sub_const level)).add
    ((measurable_pathArea t).comp measurable_snd)

theorem shiftedArea_past (level x : ℝ) (t : ℝ≥0) (f : Path) :
    shiftedArea level x t (pastPath t f) = shiftedArea level x t f := by
  rw [shiftedArea,shiftedArea,pathArea_past]

theorem shiftedArea_add (level x : ℝ) (s t : ℝ≥0) (f : Path) :
    shiftedArea level x (s+t) f =
      shiftedArea level x s f+shiftedArea level (x+f s) t (futurePath s f) := by
  unfold shiftedArea
  rw [pathArea_add,NNReal.coe_add]
  ring

theorem shiftedArea_nonneg_of_survival (level x : ℝ) (t : ℝ≥0) (f : Path)
    (hf : f ∈ survival (level-x) t) : 0 ≤ shiftedArea level x t f := by
  have he : shiftedArea level x t f =
      ∫ r in (0 : ℝ)..(t : ℝ), (x-level)+f (Real.toNNReal r) := by
    have hsample : IntervalIntegrable (fun r : ℝ ↦ f (Real.toNNReal r)) volume 0 t :=
      (((continuous_path f).comp continuous_real_toNNReal).intervalIntegrable 0 t)
    unfold shiftedArea pathArea
    rw [intervalIntegral.integral_add intervalIntegrable_const hsample,
      intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
  rw [he]
  apply intervalIntegral.integral_nonneg t.coe_nonneg
  intro r hr
  have hs := ((mem_survival_iff (level-x) t f).mp hf) (Real.toNNReal r)
    (Real.toNNReal_le_iff_le_coe.mpr hr.2)
  linarith

end PerronWright.BrownianKilledAreaGeometry
