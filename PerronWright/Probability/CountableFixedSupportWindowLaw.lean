import PerronWright.Probability.CountableComponentWindowLaw
import PerronWright.Probability.CountableFixedSupportGraphLaw

/-! # Literal fixed-support empirical-TV window law at its exact finite time

This identifies the entire genuine window probability law, including its
literal empirical probability marks, with a continuous pushforward of the
fixed critical finite model at the proved effective parameter. Neither a
window limit nor a marked convergence hypothesis is introduced.
-/

open MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace PerronWright.CountableKernel

open CountableComponentWindowLaw FinitePointMeasureCompact

theorem fixedSupportMarkedWindowLaw_eq_finite_map (M : CountableKernel)
    (m n : ℕ) (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    M.empiricalMarkedWindowLaw (fun _ ↦ m) lambda a b R hlower hlo n =
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
        (M.fixedSupportModel m hlower hlo)
        (M.fixedSupportEffectiveParameter m lambda (n + 1)) a b R (n + 1)
        (M.fixedSupportVertexTypes m (n + 1))).map
          (continuous_embedPointWindow (fun s : Finset.range (m + 1) ↦ (s : ℕ))
            a b R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [empiricalMarkedWindowLaw, ProbabilityMeasure.toMeasure_map,
    FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_toMeasure]
  rw [Measure.map_map (continuous_embedPointWindow _ a b R).measurable
    (FiniteIrreducibleMarkedComponentProcess.measurable_markedWindowPointMeasure _ a b R),
    M.fixedSupportModel_graphLaw_eq_actual m n lambda hlower hlo]
  change (M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M m (n + 1)) G a b R) =
    (M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n).map _
  congr 1
  funext G
  exact (embedPointWindow_actual_marks (fun s : Finset.range (m + 1) ↦ (s : ℕ))
    (M.fixedSupportVertexTypes m (n + 1)) G a b R).symm

theorem fixedSupportMarkedWindowLaw_integral (M : CountableKernel)
    (m n : ℕ) (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(M.empiricalMarkedWindowLaw (fun _ ↦ m)
      lambda a b R hlower hlo n : Measure _)) =
      ∫ η, F (embedPointWindow (fun s : Finset.range (m + 1) ↦ (s : ℕ)) a b R η)
        ∂(FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
          (M.fixedSupportModel m hlower hlo)
          (M.fixedSupportEffectiveParameter m lambda (n + 1)) a b R (n + 1)
          (M.fixedSupportVertexTypes m (n + 1)) : Measure _) := by
  rw [M.fixedSupportMarkedWindowLaw_eq_finite_map m n lambda a b R hlower hlo]
  exact integral_map (continuous_embedPointWindow _ a b R).measurable.aemeasurable
    hF.aestronglyMeasurable

end PerronWright.CountableKernel
