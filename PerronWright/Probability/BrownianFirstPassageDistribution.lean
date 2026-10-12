import PerronWright.Probability.BrownianFirstPassageZeroDrift
import PerronWright.Probability.BrownianPathExtremaTails

/-! # The actual zero-drift Brownian first-passage distribution

The time law is the pushforward of the constructed Brownian path law by
the literal first passage (converted to real time). Its finite positive
support is proved, rather than imposed. The exact CDF follows from the
already proved path reflection identity and the attained running minimum.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageDistribution

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageZeroDrift

def realTime (level : ℝ) (f : Path) : ℝ := (firstPassage level f).toNNReal

theorem measurable_realTime (level : ℝ) : Measurable (realTime level) :=
  measurable_coe_nnreal_real.comp (measurable_firstPassage level).ennreal_toNNReal

def timeLaw (level : ℝ) : Measure ℝ := pathLaw.map (realTime level)

instance timeLaw_isProbability (level : ℝ) : IsProbabilityMeasure (timeLaw level) :=
  Measure.isProbabilityMeasure_map (measurable_realTime level).aemeasurable

theorem timeLaw_apply (level : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    timeLaw level A = pathLaw {f : Path | realTime level f ∈ A} :=
  Measure.map_apply (measurable_realTime level) hA

theorem measurableSet_firstPassage_le (level : ℝ) (T : ℝ≥0) :
    MeasurableSet {f : Path | firstPassage level f ≤ (T : ℝ≥0∞)} :=
  (measurable_firstPassage level) measurableSet_Iic

theorem firstPassage_cdf (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | firstPassage level f ≤ (T : ℝ≥0∞)} =
      2 * gaussianReal 0 T (Iic level) := by
  have he : {f : Path | firstPassage level f ≤ (T : ℝ≥0∞)} =
      {f : Path | ContinuousPathReflection.runningMinimum f T ≤ level} := by
    ext f
    exact firstPassage_le_iff_minimum level f T
  rw [he]
  exact BrownianPathExtremaTails.runningMinimum_tail level hlevel T hT

theorem realTime_pos_ae (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, 0 < realTime level f := by
  filter_upwards [ae_firstPassage_ne_top level hlevel,ae_firstPassage_pos level hlevel]
    with f hf hp
  exact_mod_cast (ENNReal.toNNReal_pos_iff.mpr ⟨hp,lt_top_iff_ne_top.mpr hf⟩)

theorem timeLaw_Iic_of_nonpos (level : ℝ) (hlevel : level < 0)
    (T : ℝ) (hT : T ≤ 0) : timeLaw level (Iic T) = 0 := by
  rw [timeLaw_apply level measurableSet_Iic]
  have he : ({f : Path | realTime level f ∈ Iic T} : Set Path) =ᵐ[pathLaw] (∅ : Set Path) := by
    filter_upwards [realTime_pos_ae level hlevel] with f hf
    exact propext (iff_false_intro (not_le_of_gt (hT.trans_lt hf)))
  rw [measure_congr he,measure_empty]

theorem timeLaw_Iic (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) :
    timeLaw level (Iic (T : ℝ)) = 2 * gaussianReal 0 T (Iic level) := by
  rw [timeLaw_apply level measurableSet_Iic]
  calc
    _ = pathLaw {f : Path | firstPassage level f ≤ (T : ℝ≥0∞)} := by
      apply measure_congr
      filter_upwards [ae_firstPassage_ne_top level hlevel] with f hf
      apply propext
      change ((firstPassage level f).toNNReal : ℝ) ≤ (T : ℝ) ↔ _
      calc
        _ ↔ (firstPassage level f).toNNReal ≤ T := NNReal.coe_le_coe
        _ ↔ ((firstPassage level f).toNNReal : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
          ENNReal.coe_le_coe.symm
        _ ↔ _ := by
          rw [ENNReal.coe_toNNReal hf]
          exact Iff.rfl
    _ = _ := firstPassage_cdf level hlevel T hT

theorem timeLaw_positive (level : ℝ) (hlevel : level < 0) :
    timeLaw level (Ioi 0) = 1 := by
  rw [timeLaw_apply level measurableSet_Ioi]
  have he : {f : Path | realTime level f ∈ Ioi 0} =ᵐ[pathLaw] univ := by
    filter_upwards [realTime_pos_ae level hlevel] with f hf
    exact propext (iff_true_intro hf)
  rw [measure_congr he,measure_univ]

end PerronWright.BrownianFirstPassageDistribution
