import PerronWright.Probability.GraphWindowScaledTVLaw
import PerronWright.Probability.CountableGlobalAndMarkedWindowLimit
import PerronWright.Probability.CountableStarredGlobalSizeRescaling

/-! # Literal starred countable empirical-TV window graph laws

The multiplier is the original countable beta^(1/3). Every law is the
pushforward of the actual graph probability by the actual selected
component atoms. Both closed-window endpoints are retained, and size
scaling leaves the empirical natural-type probability mark unchanged.
The raw source has its exact actual effective-parameter identity.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableStarredTVWindowLaw

open CountableKernel CountableVariationMarks CountableComponentWindowLaw
open CountableTVWindowSizeRescaling CountableTVWindowConvergence GraphWindowScaledTVLaw
open CountableStarredGlobalSizeRescaling (sizeScale sizeScale_pos)
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking
open WindowSizeRescaling

def normalizedStarredWindowLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  scaledUnmarkedWindowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
    a b R (sizeScale M hM) n

def normalizedStarredMarkedWindowLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  scaledMarkedWindowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
    (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
    a b R (sizeScale M hM) n

def unnormalizedStarredWindowLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  scaledUnmarkedWindowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R (sizeScale M hM) n

def unnormalizedStarredMarkedWindowLaw (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  scaledMarkedWindowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
    (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
    a b R (sizeScale M hM) n

theorem actualStarredAtom_mark (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (n : ℕ) {G : SimpleGraph (Fin (n+1))} (a b : ℝ) (R : ℕ)
    (C : WindowComponent a b R (sizeScale M hM) G) :
    (scaledMarkedWindowAtom (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
      a b R (sizeScale M hM) C).2.val =
      EmpiricalTypeMarks.componentMark (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
        C.val := rfl

theorem normalizedStarredMarkedWindowLaw_integral (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R n : Measure _)) =
      ∫ G, F (scaledMarkedWindowPointMeasure
        (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R (sizeScale M hM))
        ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n :=
  scaledMarkedWindowLaw_integral _ _ a b R _ n hF

theorem unnormalizedStarredMarkedWindowLaw_integral (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R n : ℕ)
    {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(unnormalizedStarredMarkedWindowLaw M hM level lambda a b R n : Measure _)) =
      ∫ G, F (scaledMarkedWindowPointMeasure
        (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R (sizeScale M hM))
        ∂M.empiricalUnnormalizedGraphLaw level lambda n :=
  scaledMarkedWindowLaw_integral _ _ a b R _ n hF

theorem normalizedStarredWindowLaw_eq_map (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) :
    normalizedStarredWindowLaw M hM level hlower hlo lambda a b R n =
      (GraphWindowSource.windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
        (a/sizeScale M hM) (b/sizeScale M hM) R n).map
          (continuous_mapPoint (windowScaleMap a b R (sizeScale_pos M hM))
            (continuous_windowScaleMap a b R (sizeScale_pos M hM))).measurable.aemeasurable :=
  scaledUnmarkedWindowLaw_eq_map _ a b R (sizeScale_pos M hM) n

theorem unnormalizedStarredWindowLaw_eq_map (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R n : ℕ) :
    unnormalizedStarredWindowLaw M hM level lambda a b R n =
      (GraphWindowSource.windowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
        (a/sizeScale M hM) (b/sizeScale M hM) R n).map
          (continuous_mapPoint (windowScaleMap a b R (sizeScale_pos M hM))
            (continuous_windowScaleMap a b R (sizeScale_pos M hM))).measurable.aemeasurable :=
  scaledUnmarkedWindowLaw_eq_map _ a b R (sizeScale_pos M hM) n

theorem normalizedStarredMarkedWindowLaw_eq_map (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) :
    normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R n =
      (M.empiricalMarkedWindowLaw level lambda (a/sizeScale M hM) (b/sizeScale M hM) R hlower hlo n).map
        (continuous_mapPoint (markedWindowScaleMap a b R (sizeScale_pos M hM))
          (continuous_markedWindowScaleMap a b R (sizeScale_pos M hM))).measurable.aemeasurable := by
  unfold normalizedStarredMarkedWindowLaw
  rw [scaledMarkedWindowLaw_eq_map _ _ a b R (sizeScale_pos M hM),
    M.graphMarkedWindowLaw_eq_empirical]

theorem unnormalizedStarredMarkedWindowLaw_eq_map (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R n : ℕ) :
    unnormalizedStarredMarkedWindowLaw M hM level lambda a b R n =
      (M.empiricalUnnormalizedMarkedWindowLaw level lambda (a/sizeScale M hM) (b/sizeScale M hM) R n).map
        (continuous_mapPoint (markedWindowScaleMap a b R (sizeScale_pos M hM))
          (continuous_markedWindowScaleMap a b R (sizeScale_pos M hM))).measurable.aemeasurable := by
  unfold unnormalizedStarredMarkedWindowLaw
  rw [scaledMarkedWindowLaw_eq_map _ _ a b R (sizeScale_pos M hM),
    M.graphMarkedWindowLaw_eq_empiricalUnnormalized]

theorem unnormalizedStarredMarkedWindowLaw_eq_normalized
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (R n : ℕ) :
    unnormalizedStarredMarkedWindowLaw M hM level lambda a b R n =
      normalizedStarredMarkedWindowLaw M hM level hlower hlo
        (M.empiricalEffectiveParameter level lambda n) a b R n := by
  apply ProbabilityMeasure.toMeasure_injective
  change (M.empiricalUnnormalizedGraphLaw level lambda n).map _ =
    (M.empiricalNormalizedGraphLaw level (M.empiricalEffectiveParameter level lambda n) hlower hlo n).map _
  rw [M.empiricalUnnormalizedGraphLaw_eq_effective_normalized level lambda hlower hlo n]

end PerronWright.CountableStarredTVWindowLaw
