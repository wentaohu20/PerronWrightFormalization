import PerronWright.Probability.BrownianParabolicPassageParameterMeasurability
import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull
import PerronWright.Probability.BrownianParabolicStoppedTiltGeometry
import PerronWright.Probability.BrownianMinimumFuturePostUnit
import PerronWright.Probability.BrownianParabolicCompletedMinimumSource

/-! # Joint Borel passage, complete-shape, and residual-driver states

The retained past is the actual stopped parabolic driver, not the stopped
raw Brownian input. All parameters, durations, and paths vary jointly;
zero durations are included in these deterministic measurable maps.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace PerronWright.BrownianCompletedExcursionPassageShapeMeasurability

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathFirstPassage BrownianFirstPassageStrongMarkov
open BrownianFirstPassagePastFibers BrownianFirstPassageUncappedLaw
open BrownianParabolicFirstPassageStoppedTiltFull BrownianParabolicPassageParameterMeasurability
open BrownianMinimumFuturePostUnit BrownianPathDilationLaw
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicCompletedMinimumSource

theorem measurable_joint_actualDriverPassagePast :
    Measurable (fun q : (ℝ × ℝ) × Path ↦ actualDriverPassagePast q.1.1 q.1.2 q.2) := by
  have hd : Measurable (fun q : (ℝ × ℝ) × Path ↦ driftPath q.1.1 q.2) :=
    continuous_driftPath.measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  have ht := measurable_joint_parabolicPassageTime
  have hp := ht.prodMk (continuous_joint_pastPath.measurable.comp (ht.prodMk hd))
  simpa only [actualDriverPassagePast,passagePast,passageTime,Function.comp_def] using hp

def completedPassageState (lambda : ℝ)
    (q : ℝ × ((ℝ × Path) × (Path × Path))) : CompletedState :=
  let p := actualDriverPassagePast lambda (-q.2.1.1) q.2.1.2
  let l := Real.toNNReal q.1
  (p,-q.2.1.1,(l,brownianDilation l q.2.2.1),
    driftPath (lambda-(p.1 : ℝ)-(l : ℝ)) q.2.2.2)

theorem measurable_joint_completedPassageState :
    Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      completedPassageState q.1 q.2) := by
  have hp : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      actualDriverPassagePast q.1 (-q.2.2.1.1) q.2.2.1.2) := by
    have hg : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
        ((q.1,-q.2.2.1.1),q.2.2.1.2)) :=
      (measurable_fst.prodMk measurable_snd.snd.fst.fst.neg).prodMk measurable_snd.snd.fst.snd
    simpa only [Function.comp_def] using measurable_joint_actualDriverPassagePast.comp hg
  have hl : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      Real.toNNReal q.2.1) := measurable_snd.fst.real_toNNReal
  have he : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      brownianDilation (Real.toNNReal q.2.1) q.2.2.2.1) :=
    measurable_joint_brownianDilation.comp (hl.prodMk measurable_snd.snd.snd.fst)
  have hr : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      driftPath (q.1-((actualDriverPassagePast q.1 (-q.2.2.1.1) q.2.2.1.2).1 : ℝ)-
        (Real.toNNReal q.2.1 : ℝ)) q.2.2.2.2) :=
    continuous_driftPath.measurable.comp
      ((measurable_fst.sub hp.fst.coe_nnreal_real |>.sub hl.coe_nnreal_real).prodMk
        measurable_snd.snd.snd.snd)
  simpa only [completedPassageState,Pi.neg_apply] using
    hp.prodMk (measurable_snd.snd.fst.fst.neg.prodMk ((hl.prodMk he).prodMk hr))

def completedPassageDensity (lambda : ℝ)
    (q : ℝ × ((ℝ × Path) × (Path × Path))) : ℝ≥0∞ :=
  let p := actualDriverPassagePast lambda (-q.2.1.1) q.2.1.2
  density (lambda-(p.1 : ℝ)) (Real.toNNReal q.1)
    (brownianDilation (Real.toNNReal q.1) q.2.2.1)

theorem measurable_joint_completedPassageDensity :
    Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      completedPassageDensity q.1 q.2) := by
  have hp : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      (completedPassageState q.1 q.2).1.1) := measurable_joint_completedPassageState.fst.fst
  have hshape : Measurable (fun q : ℝ × (ℝ × ((ℝ × Path) × (Path × Path))) ↦
      (completedPassageState q.1 q.2).2.2.1) := measurable_joint_completedPassageState.snd.snd.fst
  simpa only [completedPassageDensity,completedPassageState,Function.comp_def,Pi.sub_apply] using
    measurable_joint_density.comp ((measurable_fst.sub hp.coe_nnreal_real).prodMk hshape)

end PerronWright.BrownianCompletedExcursionPassageShapeMeasurability
