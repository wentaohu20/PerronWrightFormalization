import PerronWright.Probability.BrownianFirstPassagePastFibers
import PerronWright.Probability.BrownianPathReflectionLaw

/-! # Actual parabolic hitting times depend only on the Brownian past

The deterministic drift is retained when the Brownian path is stopped.
This proves actual grid-fiber causality for the parabolic hitting time;
it does not assume that a drifted path is Brownian.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassagePastFibers

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassagePastFibers BrownianFirstPassageGridReflection

theorem measurable_actual_driftPath (lambda : ℝ) :
    Measurable (BrownianPathReflectionLaw.driftPath lambda) :=
  (BrownianPathReflectionLaw.continuous_driftPath.comp
    (continuous_const.prodMk continuous_id)).measurable

theorem firstPassage_le_stoppedBrownian (lambda level : ℝ) (T s : ℝ≥0)
    (hs : s ≤ T) (f : Path) :
    firstPassage level (BrownianPathReflectionLaw.driftPath lambda (pastPath T f)) ≤ s ↔
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≤ s := by
  rw [firstPassage_le_iff,firstPassage_le_iff]
  constructor <;> rintro ⟨v,hv,hf⟩
  · exact ⟨v,hv,by simpa only [BrownianPathReflectionLaw.driftPath_apply,
      pastPath_eval,min_eq_left (hv.trans hs)] using hf⟩
  · exact ⟨v,hv,by simpa only [BrownianPathReflectionLaw.driftPath_apply,
      pastPath_eval,min_eq_left (hv.trans hs)] using hf⟩

def parabolicGridIndex (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : Fin (m+1) :=
  gridIndex level t m (BrownianPathReflectionLaw.driftPath lambda f)

theorem measurable_parabolicGridIndex (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (parabolicGridIndex lambda level t m) :=
  (measurable_gridIndex level t m).comp (measurable_actual_driftPath lambda)

theorem parabolicGridIndex_pastPath_stable (lambda level : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (m : ℕ) (i : Fin (m+1)) (f : Path) :
    parabolicGridIndex lambda level t m (pastPath (t i) f) = i ↔
      parabolicGridIndex lambda level t m f = i := by
  unfold parabolicGridIndex
  rw [gridIndex_eq_iff,gridIndex_eq_iff]
  have hi := firstPassage_le_stoppedBrownian lambda level (t i) (t i) le_rfl f
  have hj (j : ℕ) (hji : j < i.val) :
      (t j : ℝ≥0∞) < firstPassage level (BrownianPathReflectionLaw.driftPath lambda (pastPath (t i) f)) ↔
        (t j : ℝ≥0∞) < firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) := by
    rw [← not_le,← not_le]
    exact not_congr (firstPassage_le_stoppedBrownian lambda level (t i) (t j) (ht hji.le) f)
  constructor <;> rintro ⟨ha,hb⟩
  · exact ⟨(or_congr hi Iff.rfl).mp ha,fun j hji ↦ (hj j hji).mp (hb j hji)⟩
  · exact ⟨(or_congr hi Iff.rfl).mpr ha,fun j hji ↦ (hj j hji).mpr (hb j hji)⟩

def parabolicSelectedTime (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : ℝ≥0 :=
  t (parabolicGridIndex lambda level t m f)

theorem measurable_parabolicSelectedTime (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (parabolicSelectedTime lambda level t m) :=
  (measurable_of_countable (fun i : Fin (m+1) ↦ t i)).comp
    (measurable_parabolicGridIndex lambda level t m)

def parabolicSelectedPast (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : ℝ≥0 × Path :=
  (parabolicSelectedTime lambda level t m f,pastPath (parabolicSelectedTime lambda level t m f) f)

def parabolicSelectedFuture (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) (f : Path) : Path :=
  futurePath (parabolicSelectedTime lambda level t m f) f

theorem measurable_parabolicSelectedPast (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (parabolicSelectedPast lambda level t m) :=
  (measurable_parabolicSelectedTime lambda level t m).prodMk
    (continuous_joint_pastPath.measurable.comp
      ((measurable_parabolicSelectedTime lambda level t m).prodMk measurable_id))

theorem measurable_parabolicSelectedFuture (lambda level : ℝ) (t : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (parabolicSelectedFuture lambda level t m) :=
  continuous_joint_futurePath.measurable.comp
    ((measurable_parabolicSelectedTime lambda level t m).prodMk measurable_id)

def parabolicCappedTime (lambda level : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0 :=
  BrownianFirstPassageReflection.cappedTime level T (BrownianPathReflectionLaw.driftPath lambda f)

theorem measurable_parabolicCappedTime (lambda level : ℝ) (T : ℝ≥0) :
    Measurable (parabolicCappedTime lambda level T) :=
  (BrownianFirstPassageReflection.measurable_cappedTime level T).comp
    (measurable_actual_driftPath lambda)

theorem parabolicCappedTime_coe (lambda level : ℝ) (T : ℝ≥0) (f : Path) :
    (parabolicCappedTime lambda level T f : ℝ≥0∞) =
      min (firstPassage level (BrownianPathReflectionLaw.driftPath lambda f)) (T : ℝ≥0∞) :=
  BrownianFirstPassageReflection.cappedTime_coe level T (BrownianPathReflectionLaw.driftPath lambda f)

theorem dyadic_parabolicSelectedTime_tendsto (lambda level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ parabolicSelectedTime lambda level (dyadicGrid n)
      (DyadicFloorGeometry.index n T) f) atTop (𝓝 (parabolicCappedTime lambda level T f)) :=
  BrownianFirstPassageReflection.dyadic_selectedTime_tendsto level T
    (BrownianPathReflectionLaw.driftPath lambda f)

end PerronWright.BrownianParabolicFirstPassagePastFibers
