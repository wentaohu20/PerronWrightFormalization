import PerronWright.Probability.BrownianBridgeMinimumShift
import PerronWright.Probability.BrownianEntranceFiniteDimensionalFamily
import PerronWright.Probability.BrownianEntranceContinuousRealization

/-! # Literal ordered sampling and actual stopped minimum-shift support -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section

namespace PerronWright.BrownianMinimumShiftOrderedSampling

open BrownianPathLaw BrownianBridgeMinimumShift BrownianEntranceFiniteDimensionalFamily

def tailTimes (k : ℕ) (times : Fin (k+2) → ℝ≥0) : Fin (k+1) → ℝ≥0 :=
  fun i ↦ times i.succ

theorem tailTimes_strictMono (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) : StrictMono (tailTimes k times) := by
  intro i j hij
  exact hstrict (by simpa only [Fin.lt_def,Fin.val_succ] using Nat.succ_lt_succ hij)

theorem tailTimes_first_positive (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0) : 0 < tailTimes k times 0 := by
  rw [← hzero]
  exact hstrict (by simp : (0 : Fin (k+2)) < (0 : Fin (k+1)).succ)

theorem tailTimes_last (k : ℕ) (times : Fin (k+2) → ℝ≥0) :
    tailTimes k times (Fin.last k) = times (Fin.last (k+1)) := rfl

theorem cons_tailTimes (k : ℕ) (times : Fin (k+2) → ℝ≥0) (hzero : times 0 = 0) :
    Fin.cons 0 (tailTimes k times) = times := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hzero.symm
  · rfl

theorem orderedEval_tailTimes (k : ℕ) (times : Fin (k+2) → ℝ≥0) (f : Path) :
    orderedEval k times f = fun i ↦ f (tailTimes k times i.castSucc) := by
  funext i
  simp only [orderedEval,tailTimes,Fin.succ_castSucc]

theorem ae_minimumShiftLaw_stopped_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂minimumShiftLaw T hT, ∀ t, T ≤ t → f t = 0 := by
  apply (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable
    (BrownianEntranceContinuousRealization.measurableSet_stopped_zero T)).mpr
  exact Eventually.of_forall (fun f t ht ↦ minimumShiftPath_stopped T hT f t ht)

end PerronWright.BrownianMinimumShiftOrderedSampling
