import PerronWright.Probability.BrownianBridgeCyclicPathLaw
import Mathlib.Algebra.Order.ToIntervalMod

/-! # Exact modulo and minimum geometry of continuous closed bridges

The cyclic splice equals the literal reduction modulo T, has a jointly
measurable path map, and shifts any genuine interval minimizer to a
nonnegative path. No measurable minimizer selection, almost-sure uniqueness
or positive-excursion distribution is asserted here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeCyclicGeometry

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCycleKernel
open BrownianBridgeCyclicPath BrownianBridgeCyclicPathLaw
open BrownianPinnedBridgeArea BrownianGaussianSkeleton

def moduloTime (T : ℝ≥0) (hT : 0 < T) (s t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (toIcoMod (show 0 < (T : ℝ) from hT) 0 ((s : ℝ)+(t : ℝ)))

theorem cycleTime_modulo_value (T s t : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (ht : t ≤ T) (f : Path) :
    closedBridge T (cycleTime T s t) f = closedBridge T (moduloTime T hT s t) f := by
  have hp : 0 < (T : ℝ) := hT
  have he : toIcoMod hp 0 ((s : ℝ)+(t : ℝ)) = toIcoMod hp 0 (cycleTime T s t : ℝ) := by
    rw [cycleTime_real]
    unfold realCycleTime
    split_ifs with h
    · rfl
    · exact (toIcoMod_sub hp 0 ((s : ℝ)+(t : ℝ))).symm
  have hc := cycleTime_le T s t hs ht
  rcases lt_or_eq_of_le hc with hc'|hc'
  · have hm : toIcoMod hp 0 (cycleTime T s t : ℝ) = (cycleTime T s t : ℝ) :=
      (toIcoMod_eq_self hp).mpr ⟨(cycleTime T s t).coe_nonneg,by simpa only [zero_add] using (show (cycleTime T s t : ℝ) < (T : ℝ) from hc')⟩
    simp only [moduloTime,he,hm,Real.toNNReal_coe]
  · have hm : toIcoMod hp 0 (T : ℝ) = 0 := by
      simpa only [zero_add] using toIcoMod_apply_right hp 0
    simp only [moduloTime,he,hc',hm,Real.toNNReal_zero,
      closedBridge_zero,closedBridge_endpoint T hT f]

theorem cyclicBridgePath_eq_modulo (T s t : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path) :
    cyclicBridgePath T hT s f t =
      closedBridge T (moduloTime T hT s (min t T)) f-closedBridge T s f := by
  change cyclicValue T s (min t T) f = _
  unfold cyclicValue
  rw [cycleTime_modulo_value T s (min t T) hT hs (min_le_right _ _) f]

theorem measurable_cycleTime (T : ℝ≥0) : Measurable (fun p : ℝ≥0 × ℝ≥0 ↦ cycleTime T p.1 p.2) := by
  unfold cycleTime
  exact Measurable.ite (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet
    (continuous_fst.add continuous_snd).measurable
    ((continuous_fst.add continuous_snd).sub continuous_const).measurable

theorem continuous_joint_closedBridge (T : ℝ≥0) :
    Continuous (fun p : Path × ℝ≥0 ↦ closedBridge T p.2 p.1) := by
  unfold closedBridge bridge
  exact (continuous_joint_eval.sub
    ((NNReal.continuous_coe.comp continuous_snd).div_const (T : ℝ) |>.mul
      ((continuous_eval T).comp continuous_fst))).sub
      ((continuous_const.sub ((NNReal.continuous_coe.comp continuous_snd).div_const (T : ℝ))).mul
        ((continuous_eval 0).comp continuous_fst))

/-- Joint path Borel measurability permits composition with any genuinely
proved measurable shift. It does not assume such a minimum selector. -/
theorem measurable_joint_cyclicBridgePath (T : ℝ≥0) (hT : 0 < T) :
    Measurable (fun p : ℝ≥0 × Path ↦ cyclicBridgePath T hT p.1 p.2) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun p : ℝ≥0 × Path ↦ fun q ↦
    cyclicValue T p.1 (min (rationalTimeReal q) T) p.2)
  apply measurable_pi_lambda
  intro q
  unfold cyclicValue
  have hm : Measurable (fun p : ℝ≥0 × Path ↦ cycleTime T p.1 (min (rationalTimeReal q) T)) :=
    (measurable_cycleTime T).comp (measurable_fst.prodMk measurable_const)
  exact ((continuous_joint_closedBridge T).measurable.comp (measurable_snd.prodMk hm)).sub
    ((continuous_joint_closedBridge T).measurable.comp (measurable_snd.prodMk measurable_fst))

theorem exists_closedBridge_minimizer (T : ℝ≥0) (f : Path) :
    ∃ s : ℝ≥0, s ≤ T ∧ ∀ t : ℝ≥0, t ≤ T → closedBridge T s f ≤ closedBridge T t f := by
  obtain ⟨s,hs,hm⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMinOn
    (show (Icc (0 : ℝ≥0) T).Nonempty from ⟨0,by simp⟩)
    (continuous_sample_closedBridge T f).continuousOn
  exact ⟨s,hs.2,fun t ht ↦ hm ⟨(show 0 ≤ t from zero_le),ht⟩⟩

theorem cyclicBridgePath_nonneg_of_minimizer (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path)
    (hm : ∀ t : ℝ≥0, t ≤ T → closedBridge T s f ≤ closedBridge T t f) :
    ∀ t : ℝ≥0, 0 ≤ cyclicBridgePath T hT s f t := by
  intro t
  change 0 ≤ closedBridge T (cycleTime T s (min t T)) f-closedBridge T s f
  exact sub_nonneg.mpr (hm _ (cycleTime_le T s _ hs (min_le_right _ _)))

theorem exists_nonnegative_minimum_shift (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    ∃ s : ℝ≥0, s ≤ T ∧
      (∀ t : ℝ≥0, t ≤ T → closedBridge T s f ≤ closedBridge T t f) ∧
      (∀ t : ℝ≥0, 0 ≤ cyclicBridgePath T hT s f t) := by
  obtain ⟨s,hs,hm⟩ := exists_closedBridge_minimizer T f
  exact ⟨s,hs,hm,cyclicBridgePath_nonneg_of_minimizer T s hT hs f hm⟩

end PerronWright.BrownianBridgeCyclicGeometry
