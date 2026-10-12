import PerronWright.Probability.BrownianParabolicFirstPassagePastFibers

/-! # Actual parabolic passage paths are jointly Borel in both parameters

These literal joint maps allow the fixed-parameter product identities
to be integrated over a past-measurable drift and negative level.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicPassageParameterMeasurability

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassagePastFibers

theorem measurable_joint_parabolicFirstPassage :
    Measurable (fun p : (ℝ × ℝ) × Path ↦
      firstPassage p.1.2 (BrownianPathReflectionLaw.driftPath p.1.1 p.2)) :=
  measurable_joint_firstPassage.comp (measurable_fst.snd.prodMk
    (BrownianPathReflectionLaw.continuous_driftPath.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)))

theorem measurable_joint_parabolicPassageTime :
    Measurable (fun p : (ℝ × ℝ) × Path ↦
      (firstPassage p.1.2 (BrownianPathReflectionLaw.driftPath p.1.1 p.2)).toNNReal) :=
  measurable_joint_parabolicFirstPassage.ennreal_toNNReal

theorem measurable_joint_parabolicPassagePast :
    Measurable (fun p : (ℝ × ℝ) × Path ↦
      ((firstPassage p.1.2 (BrownianPathReflectionLaw.driftPath p.1.1 p.2)).toNNReal,
        pastPath (firstPassage p.1.2 (BrownianPathReflectionLaw.driftPath p.1.1 p.2)).toNNReal p.2)) :=
  measurable_joint_parabolicPassageTime.prodMk (continuous_joint_pastPath.measurable.comp
    (measurable_joint_parabolicPassageTime.prodMk measurable_snd))

theorem measurable_joint_parabolicPassageFuture :
    Measurable (fun p : (ℝ × ℝ) × Path ↦
      futurePath (firstPassage p.1.2 (BrownianPathReflectionLaw.driftPath p.1.1 p.2)).toNNReal p.2) :=
  continuous_joint_futurePath.measurable.comp
    (measurable_joint_parabolicPassageTime.prodMk measurable_snd)

end PerronWright.BrownianParabolicPassageParameterMeasurability
