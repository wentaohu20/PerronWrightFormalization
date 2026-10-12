import PerronWright.Probability.BrownianClippedExcursionMovingCounts
import PerronWright.Probability.BrownianUnderGraphSpatialJointLaw
import PerronWright.Probability.BrownianClippedSpatialMarkIdentification

/-!
# Actual spatial atoms realize the complete clipped Brownian joint mark law

Counts in the genuine moving retained-component cells are jointly
measurable. The proved full conditional count law is integrated to identify
the actual spatial-source/count pair with the already constructed actual
area-rate marking-source/count pair. All conditional equalities and all
moving-count measurability obligations are discharged for the literal model.
The windows remain clipped; full-time excursions and their density are
not asserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianClippedSpatialJointMarkLaw

open BrownianPathLaw BrownianClippedExcursionMovingCounts FinitePointMeasureCompact
open BrownianClippedSpatialMarkIdentification

/-- A proved dependent-map Fubini identity; the actual applications below
discharge its conditional equality from the genuine spatial construction. -/
theorem joint_pair_map_eq {S E F D : Type*}
    [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace D]
    (μ : Measure S) [SFinite μ] (κ : Kernel S E) (η : Kernel S F)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (X : S × E → D) (Y : S × F → D) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ s, (κ s).map (fun e ↦ X (s,e)) = (η s).map (fun f ↦ Y (s,f))) :
    (μ ⊗ₘ κ).map (fun p ↦ (p.1,X p)) = (μ ⊗ₘ η).map (fun p ↦ (p.1,Y p)) := by
  have hXM : Measurable (fun p : S × E ↦ (p.1,X p)) := measurable_fst.prodMk hX
  have hYM : Measurable (fun p : S × F ↦ (p.1,Y p)) := measurable_fst.prodMk hY
  ext A hA
  rw [Measure.map_apply hXM hA,Measure.map_apply hYM hA,
    Measure.compProd_apply (hA.preimage hXM),Measure.compProd_apply (hA.preimage hYM)]
  apply lintegral_congr
  intro s
  have hAs : MeasurableSet (Prod.mk s ⁻¹' A) := measurable_prodMk_left hA
  have hXs : Measurable (fun e : E ↦ X (s,e)) :=
    hX.comp (measurable_const.prodMk measurable_id)
  have hYs : Measurable (fun f : F ↦ Y (s,f)) :=
    hY.comp (measurable_const.prodMk measurable_id)
  have he := congrArg (fun ν : Measure D ↦ ν (Prod.mk s ⁻¹' A)) (h s)
  rw [Measure.map_apply hXs hAs,Measure.map_apply hYs hAs] at he
  exact he

/-- Actual planar component counts and the genuine area-rate countable
marks have exactly the same whole path/count joint law. -/
theorem pathJointLaw_map_counts_eq_markJointLaw (H : ℝ≥0) (lambda : ℝ) :
    (BrownianUnderGraphSpatialKernel.pathJointLaw lambda 0 H).map
      (fun p : Path × PointMeasure (ℝ × ℝ) ↦ (p.1,spatialCounts H lambda p)) =
    (BrownianClippedExcursionPoissonMarks.pathJointLaw H lambda).map
      (fun p : Path × (ℕ → ℕ) ↦ (p.1,BrownianClippedExcursionPoissonMarks.rationalCount p.2)) := by
  apply joint_pair_map_eq
    pathLaw (BrownianUnderGraphSpatialKernel.spatialKernel lambda 0 H)
    (CountablePoissonKernel.rateKernel
      (BrownianClippedExcursionPoissonMarks.naturalRates H lambda)
      (BrownianClippedExcursionPoissonMarks.measurable_naturalRates H lambda))
    (spatialCounts H lambda)
    (fun p : Path × (ℕ → ℕ) ↦ BrownianClippedExcursionPoissonMarks.rationalCount p.2)
    (measurable_spatialCounts H lambda) (measurable_rationalCount.comp measurable_snd)
  intro f
  exact spatial_count_law_eq_markLaw H lambda f

/-- Terminal source-space identity: real planar atoms counted in real
moving Brownian component cells realize the entire constructed marking
law jointly with the actual Gaussian source, without conditional interfaces. -/
theorem actualJointLaw_map_counts_eq_markJointLaw (H : ℝ≥0) (lambda : ℝ) :
    (BrownianUnderGraphSpatialKernel.actualJointLaw lambda 0 H).map
      (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ (p.1,actualSpatialCounts H lambda p)) =
    (BrownianClippedExcursionPoissonMarks.actualJointLaw H lambda).map
      (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
        (p.1,BrownianClippedExcursionPoissonMarks.rationalCount p.2)) := by
  apply joint_pair_map_eq
    BrownianGaussianSkeleton.rationalLaw (BrownianUnderGraphSpatialKernel.actualSpatialKernel lambda 0 H)
    (CountablePoissonKernel.rateKernel
      (BrownianClippedExcursionPoissonMarks.actualRates H lambda)
      (BrownianClippedExcursionPoissonMarks.measurable_actualRates H lambda))
    (actualSpatialCounts H lambda)
    (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ BrownianClippedExcursionPoissonMarks.rationalCount p.2)
    (measurable_actualSpatialCounts H lambda) (measurable_rationalCount.comp measurable_snd)
  intro x
  exact spatial_count_law_eq_markLaw H lambda (measurablePath x)

theorem hasLaw_actual_source_spatial_counts (H : ℝ≥0) (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ (p.1,actualSpatialCounts H lambda p))
      ((BrownianClippedExcursionPoissonMarks.actualJointLaw H lambda).map
        (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
          (p.1,BrownianClippedExcursionPoissonMarks.rationalCount p.2)))
      (BrownianUnderGraphSpatialKernel.actualJointLaw lambda 0 H) :=
  ⟨(measurable_fst.prodMk (measurable_actualSpatialCounts H lambda)).aemeasurable,
    actualJointLaw_map_counts_eq_markJointLaw H lambda⟩

end PerronWright.BrownianClippedSpatialJointMarkLaw
