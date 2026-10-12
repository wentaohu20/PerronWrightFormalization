import PerronWright.Probability.BrownianClippedExcursionSpatialCells
import PerronWright.Probability.BrownianClippedExcursionPoissonMarks
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Actual spatial counts realize the clipped area-rate excursion marks

All finite rational-coordinate laws are computed from the actual spatial
point measure. Genuine projective uniqueness then identifies the entire
rational count-family law with the constructed countable area-rate marking
law. This is a conditional bounded-window spatial identification, not the
full-time excursion law or the Wright factorial-density formula.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianClippedSpatialMarkIdentification

open BrownianPathLaw BrownianClippedExcursionSpatialCells
  BrownianClippedExcursionPoissonMarks BrownianWindowExcursionAreas
  BrownianUnderGraphPoissonLaw FinitePointMeasureCompact

def spatialRationalCounts (H lambda : ℝ) (f : Path)
    (η : PointMeasure (ℝ × ℝ)) (q : ℚ) : ℕ :=
  count η (retainedCell H lambda q f)

theorem measurable_spatialRationalCounts (H lambda : ℝ) (f : Path) :
    Measurable (spatialRationalCounts H lambda f) :=
  FinitePointMeasureMeasurable.measurable_count_vector _
    (fun q ↦ measurableSet_retainedCell H lambda q f)

theorem measurable_rationalCount : Measurable rationalCount :=
  measurable_pi_lambda _ (fun q ↦ measurable_pi_apply (Encodable.encode q))

/-- Exact finite laws of the already constructed countable marks. -/
theorem markLaw_map_finite_rationalCounts (H lambda : ℝ) (f : Path) (I : Finset ℚ) :
    (markLaw H lambda f).map (fun (m : ℕ → ℕ) (q : I) ↦ rationalCount m q.1) =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea H lambda q.1 f) := by
  have hi := (markLaw_rationalCounts_independent H lambda f).precomp
    (g := fun q : I ↦ (q : ℚ)) Subtype.coe_injective
  have he := hi.map_fun_eq_pi_map (fun q : I ↦
    (measurable_pi_apply (Encodable.encode (q : ℚ))).aemeasurable)
  change (markLaw H lambda f).map (fun (m : ℕ → ℕ) (q : I) ↦ rationalCount m q.1) =
    Measure.pi (fun q : I ↦ (markLaw H lambda f).map (fun m ↦ rationalCount m q.1)) at he
  rw [he]
  unfold PoissonCountKernel.finiteCountLaw
  congr 1
  funext q
  exact (markLaw_hasLaw_rationalCount H lambda f q.1).map_eq

/-- Counts from the actual spatial process have exactly the complete
countable area-rate mark law on the nonrepeating rational components. -/
theorem spatial_count_law_eq_markLaw (H : ℝ≥0) (lambda : ℝ) (f : Path) :
    (law lambda 0 H f).map (spatialRationalCounts H lambda f) =
      (markLaw H lambda f).map rationalCount := by
  let μ := (law lambda 0 H f).map (spatialRationalCounts H lambda f)
  let ν := (markLaw H lambda f).map rationalCount
  have hm (I : Finset ℚ) : μ.map I.restrict =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea H lambda q.1 f) := by
    rw [show μ = (law lambda 0 H f).map (spatialRationalCounts H lambda f) from rfl,
      Measure.map_map I.measurable_restrict (measurable_spatialRationalCounts H lambda f)]
    exact law_finite_retained_counts H lambda f I
  have hn (I : Finset ℚ) : ν.map I.restrict =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea H lambda q.1 f) := by
    rw [show ν = (markLaw H lambda f).map rationalCount from rfl,
      Measure.map_map I.measurable_restrict measurable_rationalCount]
    exact markLaw_map_finite_rationalCounts H lambda f I
  have hμ : IsProjectiveLimit μ (fun I : Finset ℚ ↦ μ.map I.restrict) := fun _ ↦ rfl
  have hν : IsProjectiveLimit ν (fun I : Finset ℚ ↦ μ.map I.restrict) :=
    fun I ↦ (hn I).trans (hm I).symm
  exact hμ.unique hν

end PerronWright.BrownianClippedSpatialMarkIdentification
