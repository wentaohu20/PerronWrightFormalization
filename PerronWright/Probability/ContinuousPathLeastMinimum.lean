import PerronWright.Probability.BrownianPathLaw
import Mathlib.Topology.Order.Compact

/-! # Genuine measurable earliest minimizer of a continuous path

The minimum is the actual infimum of the image of [0,T]. The earliest
minimizer is the actual infimum of its nonempty compact set of minimizing
times. Compactness proves attainment and leastness; continuous prefix
minima prove measurability. No random minimum or selector hypothesis is
introduced, and no almost-sure uniqueness is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathLeastMinimum

open BrownianPathLaw

def minimumValue (T : ℝ≥0) (f : Path) : ℝ := sInf ((fun t ↦ f t) '' Icc 0 T)

def minimizingTimes (T : ℝ≥0) (f : Path) : Set ℝ≥0 :=
  Icc 0 T ∩ {t | f t = minimumValue T f}

def leastMinimizer (T : ℝ≥0) (f : Path) : ℝ≥0 := sInf (minimizingTimes T f)

theorem continuous_minimumValue (T : ℝ≥0) : Continuous (minimumValue T) :=
  (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).continuous_sInf continuous_joint_eval

theorem exists_minimumValue (T : ℝ≥0) (f : Path) :
    ∃ t : ℝ≥0, t ≤ T ∧ minimumValue T f = f t ∧ ∀ s : ℝ≥0, s ≤ T → f t ≤ f s := by
  obtain ⟨t,ht,he,hm⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_sInf_image_eq_and_le
    (show (Icc (0 : ℝ≥0) T).Nonempty from ⟨0,by simp⟩) (continuous_path f).continuousOn
  exact ⟨t,ht.2,he,fun s hs ↦ hm s ⟨zero_le,hs⟩⟩

theorem minimumValue_le (T : ℝ≥0) (f : Path) (t : ℝ≥0) (ht : t ≤ T) :
    minimumValue T f ≤ f t := by
  obtain ⟨s,_,he,hm⟩ := exists_minimumValue T f
  rw [he]
  exact hm t ht

theorem minimizingTimes_nonempty (T : ℝ≥0) (f : Path) : (minimizingTimes T f).Nonempty := by
  obtain ⟨t,ht,he,_⟩ := exists_minimumValue T f
  exact ⟨t,⟨⟨zero_le,ht⟩,he.symm⟩⟩

theorem isCompact_minimizingTimes (T : ℝ≥0) (f : Path) : IsCompact (minimizingTimes T f) :=
  isCompact_Icc.inter_right (isClosed_eq (continuous_path f) continuous_const)

theorem leastMinimizer_isLeast (T : ℝ≥0) (f : Path) :
    IsLeast (minimizingTimes T f) (leastMinimizer T f) :=
  (isCompact_minimizingTimes T f).isLeast_sInf (minimizingTimes_nonempty T f)

theorem leastMinimizer_le_time (T : ℝ≥0) (f : Path) : leastMinimizer T f ≤ T :=
  (leastMinimizer_isLeast T f).1.1.2

theorem leastMinimizer_value (T : ℝ≥0) (f : Path) : f (leastMinimizer T f) = minimumValue T f :=
  (leastMinimizer_isLeast T f).1.2

theorem leastMinimizer_le (T : ℝ≥0) (f : Path) (t : ℝ≥0)
    (ht : t ≤ T) (he : f t = minimumValue T f) : leastMinimizer T f ≤ t :=
  (leastMinimizer_isLeast T f).2 ⟨⟨zero_le,ht⟩,he⟩

theorem leastMinimizer_le_iff_prefix_minimum (T a : ℝ≥0) (f : Path) :
    leastMinimizer T f ≤ a ↔ minimumValue (min a T) f = minimumValue T f := by
  have hprefix : minimumValue T f ≤ minimumValue (min a T) f := by
    obtain ⟨t,ht,he,_⟩ := exists_minimumValue (min a T) f
    rw [he]
    exact minimumValue_le T f t (ht.trans (min_le_right _ _))
  constructor
  · intro h
    apply le_antisymm _ hprefix
    rw [← leastMinimizer_value T f]
    exact minimumValue_le (min a T) f _ (le_min h (leastMinimizer_le_time T f))
  · intro h
    obtain ⟨t,ht,he,_⟩ := exists_minimumValue (min a T) f
    have he' : f t = minimumValue T f := he.symm.trans h
    exact (leastMinimizer_le T f t (ht.trans (min_le_right _ _)) he').trans
      (ht.trans (min_le_left _ _))

/-- Earliest minimum is measurable even for paths with multiple or
non-isolated minima: sublevel events are equality of true continuous
prefix and full minimum functionals. -/
theorem measurable_leastMinimizer (T : ℝ≥0) : Measurable (leastMinimizer T) := by
  apply measurable_of_Iic
  intro a
  have he : (leastMinimizer T) ⁻¹' Iic a =
      {f | minimumValue (min a T) f = minimumValue T f} := by
    ext f
    exact leastMinimizer_le_iff_prefix_minimum T a f
  rw [he]
  exact (isClosed_eq (continuous_minimumValue _) (continuous_minimumValue _)).measurableSet

def scaledLeastMinimizer (T : ℝ≥0) (f : Path) : ℝ≥0 := leastMinimizer T f/T

theorem measurable_scaledLeastMinimizer (T : ℝ≥0) : Measurable (scaledLeastMinimizer T) :=
  (measurable_leastMinimizer T).div_const T

theorem scaledLeastMinimizer_mem (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    scaledLeastMinimizer T f ∈ Icc 0 1 := by
  constructor
  · exact zero_le
  · unfold scaledLeastMinimizer
    exact (div_le_iff₀ hT).mpr (by simpa only [one_mul] using leastMinimizer_le_time T f)

end PerronWright.ContinuousPathLeastMinimum
