import PerronWright.Probability.BrownianFirstPassageReflection

/-! # Actual first-passage grid fibers depend only on the stopped past

The grid is the existing first grid point at or after literal first
passage, capped at its final point. Each selected-time event is proved
unchanged by stopping at that time. Joint path continuity also supplies
the deterministic approximation needed for a true stopped-future law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassagePastFibers

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageGridReflection BrownianFirstPassageReflection

theorem continuous_joint_pastPath :
    Continuous (fun p : ℝ≥0 × Path ↦ pastPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_joint_eval.comp
    (continuous_fst.snd.prodMk (continuous_snd.min continuous_fst.fst))

theorem continuous_joint_futurePath :
    Continuous (fun p : ℝ≥0 × Path ↦ futurePath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_joint_eval.comp
    (continuous_fst.snd.prodMk (continuous_fst.fst.add continuous_snd))).sub
    (continuous_joint_eval.comp (continuous_fst.snd.prodMk continuous_fst.fst))

theorem firstPassage_le_pastPath (level : ℝ) (T s : ℝ≥0) (hs : s ≤ T) (f : Path) :
    firstPassage level (pastPath T f) ≤ s ↔ firstPassage level f ≤ s := by
  rw [firstPassage_le_iff,firstPassage_le_iff]
  constructor <;> rintro ⟨v,hv,hf⟩
  · exact ⟨v,hv,by simpa only [pastPath_eval,min_eq_left (hv.trans hs)] using hf⟩
  · exact ⟨v,hv,by simpa only [pastPath_eval,min_eq_left (hv.trans hs)] using hf⟩

theorem gridIndex_pastPath_stable (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (m : ℕ) (i : Fin (m+1)) (f : Path) :
    gridIndex level t m (pastPath (t i) f) = i ↔ gridIndex level t m f = i := by
  rw [gridIndex_eq_iff,gridIndex_eq_iff]
  have hi := firstPassage_le_pastPath level (t i) (t i) le_rfl f
  have hj (j : ℕ) (hji : j < i.val) :
      (t j : ℝ≥0∞) < firstPassage level (pastPath (t i) f) ↔
      (t j : ℝ≥0∞) < firstPassage level f := by
    rw [← not_le,← not_le]
    exact not_congr (firstPassage_le_pastPath level (t i) (t j) (ht hji.le) f)
  constructor <;> rintro ⟨ha,hb⟩
  · exact ⟨(or_congr hi Iff.rfl).mp ha,fun j hji ↦ (hj j hji).mp (hb j hji)⟩
  · exact ⟨(or_congr hi Iff.rfl).mpr ha,fun j hji ↦ (hj j hji).mpr (hb j hji)⟩

def selectedPast (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : ℝ≥0 × Path :=
  (selectedTime level t m f,pastPath (selectedTime level t m f) f)

def selectedFuture (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : Path :=
  futurePath (selectedTime level t m f) f

theorem measurable_selectedTime (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (selectedTime level t m) :=
  (measurable_of_countable (fun i : Fin (m+1) ↦ t i)).comp (measurable_gridIndex level t m)

theorem measurable_selectedPast (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (selectedPast level t m) :=
  (measurable_selectedTime level t m).prodMk
    (continuous_joint_pastPath.measurable.comp
      ((measurable_selectedTime level t m).prodMk measurable_id))

theorem measurable_selectedFuture (level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (selectedFuture level t m) :=
  continuous_joint_futurePath.measurable.comp
    ((measurable_selectedTime level t m).prodMk measurable_id)

end PerronWright.BrownianFirstPassagePastFibers
