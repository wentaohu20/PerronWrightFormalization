import PerronWright.Probability.BrownianPathReflectionLaw
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

/-! # Literal first downcrossings of continuous paths

The first passage time is the infimum of the actual closed sublevel
time set, with value infinity only if that set is empty. Closedness
proves attainment, running minima identify all finite-horizon events,
and these identities prove actual Borel measurability. A path starting
above the level hits that level exactly at its first finite passage.
There is no stopping-time, strong-Markov, or excursion-law hypothesis.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ContinuousPathFirstPassage

open BrownianPathLaw ContinuousPathReflection

def sublevelTimes (level : ℝ) (f : Path) : Set ℝ≥0 := {t | f t ≤ level}

theorem isClosed_sublevelTimes (level : ℝ) (f : Path) :
    IsClosed (sublevelTimes level f) :=
  isClosed_le (continuous_path f) continuous_const

def firstPassage (level : ℝ) (f : Path) : ℝ≥0∞ :=
  if (sublevelTimes level f).Nonempty then (sInf (sublevelTimes level f) : ℝ≥0) else ⊤

theorem firstPassage_eq_top_iff (level : ℝ) (f : Path) :
    firstPassage level f = ⊤ ↔ ∀ t : ℝ≥0, level < f t := by
  unfold firstPassage
  by_cases h : (sublevelTimes level f).Nonempty
  · rw [if_pos h]
    simp only [ENNReal.coe_ne_top,false_iff]
    obtain ⟨t,ht⟩ := h
    intro hn
    exact (not_le_of_gt (hn t)) ht
  · rw [if_neg h]
    simp only [true_iff]
    intro t
    exact lt_of_not_ge (fun ht ↦ h ⟨t,ht⟩)

theorem firstPassage_le_iff (level : ℝ) (f : Path) (T : ℝ≥0) :
    firstPassage level f ≤ T ↔ ∃ t : ℝ≥0, t ≤ T ∧ f t ≤ level := by
  have hb : BddBelow (sublevelTimes level f) := ⟨0,fun _ _ ↦ zero_le⟩
  by_cases h : (sublevelTimes level f).Nonempty
  · rw [firstPassage,if_pos h,ENNReal.coe_le_coe]
    constructor
    · intro ht
      exact ⟨sInf (sublevelTimes level f),ht,
        (isClosed_sublevelTimes level f).csInf_mem h hb⟩
    · rintro ⟨t,ht,hf⟩
      exact (csInf_le hb hf).trans ht
  · rw [firstPassage,if_neg h]
    constructor
    · intro ht
      exact False.elim (ENNReal.coe_ne_top (le_antisymm le_top ht))
    · rintro ⟨t,_,ht⟩
      exact False.elim (h ⟨t,ht⟩)

theorem firstPassage_le_iff_minimum (level : ℝ) (f : Path) (T : ℝ≥0) :
    firstPassage level f ≤ T ↔ runningMinimum f T ≤ level := by
  rw [firstPassage_le_iff]
  constructor
  · rintro ⟨t,ht,hf⟩
    exact (runningMinimum_le (continuous_path f) ht).trans hf
  · intro h
    obtain ⟨t,ht,he⟩ := runningMinimum_attained (continuous_path f) T
    exact ⟨t,ht.2,he ▸ h⟩

theorem before_firstPassage (level : ℝ) (f : Path) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < firstPassage level f) : level < f t := by
  apply lt_of_not_ge
  intro hf
  have h := (firstPassage_le_iff level f t).mpr ⟨t,le_rfl,hf⟩
  exact (not_le_of_gt ht) h

theorem firstPassage_attained (level : ℝ) (f : Path)
    (hfin : firstPassage level f ≠ ⊤) : f (firstPassage level f).toNNReal ≤ level := by
  have h := (firstPassage_le_iff level f (firstPassage level f).toNNReal).mp
    (by rw [ENNReal.coe_toNNReal hfin])
  have hs : (sublevelTimes level f).Nonempty := by obtain ⟨t,_,ht⟩ := h; exact ⟨t,ht⟩
  rw [firstPassage,if_pos hs,ENNReal.toNNReal_coe]
  exact (isClosed_sublevelTimes level f).csInf_mem hs ⟨0,fun _ _ ↦ zero_le⟩

theorem firstPassage_exact_level (level : ℝ) (f : Path) (hstart : level < f 0)
    (hfin : firstPassage level f ≠ ⊤) : f (firstPassage level f).toNNReal = level := by
  let τ := (firstPassage level f).toNNReal
  have hhit : f τ ≤ level := firstPassage_attained level f hfin
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ τ)
    (continuous_path f).continuousOn (show level ∈ Icc (f τ) (f 0) from ⟨hhit,hstart.le⟩)
  have hτ : τ ≤ t := by
    have h := (firstPassage_le_iff level f t).mpr ⟨t,le_rfl,he.le⟩
    rw [← ENNReal.coe_toNNReal hfin] at h
    exact ENNReal.coe_le_coe.mp h
  have het : t = τ := le_antisymm ht.2 hτ
  change f τ = level
  rw [← het]
  exact he

theorem continuous_minimum_at (T : ℝ≥0) : Continuous (fun f : Path ↦ runningMinimum f T) :=
  BrownianPathReflectionLaw.continuous_joint_minimum.comp (continuous_id.prodMk continuous_const)

theorem measurable_firstPassage (level : ℝ) : Measurable (firstPassage level) := by
  apply measurable_of_Iic
  intro x
  by_cases hx : x = ⊤
  · simp only [hx,Iic_top,preimage_univ,MeasurableSet.univ]
  · have he : firstPassage level ⁻¹' Iic x =
        {f : Path | runningMinimum f x.toNNReal ≤ level} := by
      ext f
      rw [← ENNReal.coe_toNNReal hx]
      exact firstPassage_le_iff_minimum level f x.toNNReal
    rw [he]
    exact (isClosed_le (continuous_minimum_at _) continuous_const).measurableSet

theorem measurable_joint_firstPassage :
    Measurable (fun p : ℝ × Path ↦ firstPassage p.1 p.2) := by
  apply measurable_of_Iic
  intro x
  by_cases hx : x = ⊤
  · simp only [hx,Iic_top,preimage_univ,MeasurableSet.univ]
  · have he : (fun p : ℝ × Path ↦ firstPassage p.1 p.2) ⁻¹' Iic x =
        {p : ℝ × Path | runningMinimum p.2 x.toNNReal ≤ p.1} := by
      ext p
      rw [← ENNReal.coe_toNNReal hx]
      exact firstPassage_le_iff_minimum p.1 p.2 x.toNNReal
    rw [he]
    exact (isClosed_le ((continuous_minimum_at _).comp continuous_snd) continuous_fst).measurableSet

/-- Actual evaluation at the measurable first passage, with the usual
zero convention for the time conversion on the no-passage event. -/
theorem measurable_firstPassage_eval (level : ℝ) :
    Measurable (fun f : Path ↦ f (firstPassage level f).toNNReal) :=
  continuous_joint_eval.measurable.comp
    (measurable_id.prodMk (measurable_firstPassage level).ennreal_toNNReal)

theorem measurable_joint_firstPassage_eval :
    Measurable (fun p : ℝ × Path ↦ p.2 (firstPassage p.1 p.2).toNNReal) :=
  continuous_joint_eval.measurable.comp
    (measurable_snd.prodMk measurable_joint_firstPassage.ennreal_toNNReal)

def survival (level : ℝ) (T : ℝ≥0) : Set Path := {f | level < runningMinimum f T}

theorem isOpen_survival (level : ℝ) (T : ℝ≥0) : IsOpen (survival level T) :=
  isOpen_lt continuous_const (continuous_minimum_at T)

theorem measurableSet_survival (level : ℝ) (T : ℝ≥0) : MeasurableSet (survival level T) :=
  (isOpen_survival level T).measurableSet

theorem mem_survival_iff (level : ℝ) (T : ℝ≥0) (f : Path) :
    f ∈ survival level T ↔ ∀ t : ℝ≥0, t ≤ T → level < f t := by
  constructor
  · intro h t ht
    exact h.trans_le (runningMinimum_le (continuous_path f) ht)
  · intro h
    obtain ⟨t,ht,he⟩ := runningMinimum_attained (continuous_path f) T
    change level < runningMinimum f T
    rw [he]
    exact h t ht.2

theorem mem_survival_iff_firstPassage (level : ℝ) (T : ℝ≥0) (f : Path) :
    f ∈ survival level T ↔ (T : ℝ≥0∞) < firstPassage level f := by
  change level < runningMinimum f T ↔ _
  rw [← not_le,← firstPassage_le_iff_minimum,not_le]

end PerronWright.ContinuousPathFirstPassage
