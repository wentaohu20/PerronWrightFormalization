import PerronWright.Probability.MarkedWindowSizeRescaling
import PerronWright.Probability.CompactWindowMarkedLawLimit
import PerronWright.Probability.CompactStarredWindowPointLawLimit

/-!
# Actual starred empirical-mark window-law convergence

The literal `beta^(1/3)` size coordinate acts on the actual typed graph
component atoms, leaving the empirical probability-measure marks intact.
The full-sequence limit is obtained from the proved actual unstarred
marked limit and is the canonical Perron marking of the actual starred
unmarked limit. No source-limit or Brownian-realization assumption is used.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactStarredMarkedWindowLawLimit

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureMarking
  ComponentWindowPointMeasures ComponentWindowMarkedLaw ComponentWindowMarkedTransfer
  ComponentWindowMarkedConvergence CompactWindowMarkedLawLimit WindowSizeRescaling
  MarkedWindowSizeRescaling ComponentPointProcesses

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Genuine size rescaling commutes with literal constant marking of
point measures, including multiplicities and every boundary atom. -/
theorem mapPoint_constantMark (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (ν : WeakMark S) (η : PointMeasure (SurplusWindow (a / c) (b / c) R)) :
    mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable
      (constantMark ν η) =
        constantMark ν (mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc).measurable η) := by
  obtain ⟨n,x,hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  simp only [he,constantMark,mapPoint_ofAtomsPoint]
  rfl

/-- Canonical Perron marking and true size pushforward commute at law
level; this is proved from measure-map composition, not independence. -/
theorem map_canonicalPerronMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow (a / c) (b / c) R))) :
    (canonicalPerronMarkedLaw M hM (a / c) (b / c) R ν).map
      (continuous_mapPoint (markedWindowScaleMap a b R hc)
        (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable =
      canonicalPerronMarkedLaw M hM a b R (ν.map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable) := by
  apply Subtype.ext
  change ((ν : Measure (PointMeasure (SurplusWindow (a / c) (b / c) R))).map
    (constantMark (perronWeakMark M hM))).map
      (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable) =
    ((ν : Measure (PointMeasure (SurplusWindow (a / c) (b / c) R))).map
      (mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable)).map
        (constantMark (perronWeakMark M hM))
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    (continuous_constantMark _).measurable,
    Measure.map_map (continuous_constantMark _).measurable
      (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable]
  congr 1
  funext η
  exact mapPoint_constantMark a b R hc (perronWeakMark M hM) η

/-- Every positive literal size normalization of the actual marked
typed-graph window converges together with the actual unmarked window.
The marked limit is the canonical Perron marking of that unmarked limit. -/
theorem exists_unique_scaled_unmarked_and_markedWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw M lambda a b R c) atTop (𝓝 ν) ∧
        Tendsto (scaledMarkedWindowLaw M lambda a b R c) atTop
          (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a,le_rfl,hab⟩,⟨0,by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hab' : a / c ≤ b / c := (div_le_div_iff_of_pos_right hc).mpr hab
  obtain ⟨ν,⟨hν,hmarked⟩,_⟩ := exists_unique_unmarked_and_markedWindowLaw_limit
    M hM hQP lambda (a / c) (b / c) (div_pos ha hc) hab' R
  let ρ := ν.map (continuous_mapPoint (windowScaleMap a b R hc)
    (continuous_windowScaleMap a b R hc)).measurable.aemeasurable
  have hρ : Tendsto (windowLaw M lambda a b R c) atTop (𝓝 ρ) := by
    change Tendsto (fun n ↦ windowLaw M lambda a b R c n) atTop (𝓝 ρ)
    simpa only [windowLaw_eq_map_unmarkedWindowLaw M lambda a b R hc,ρ] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (unmarkedWindowLaw M lambda (a / c) (b / c) R) ν hν
          (continuous_mapPoint _ (continuous_windowScaleMap a b R hc))
  have hρmarked : Tendsto (scaledMarkedWindowLaw M lambda a b R c) atTop
      (𝓝 (canonicalPerronMarkedLaw M hM a b R ρ)) := by
    change Tendsto (fun n ↦ scaledMarkedWindowLaw M lambda a b R c n) atTop
      (𝓝 (canonicalPerronMarkedLaw M hM a b R ρ))
    simpa only [scaledMarkedWindowLaw_eq_map M lambda a b R hc,
      map_canonicalPerronMarkedLaw M hM a b R hc,ρ] using
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (markedWindowLaw M lambda (a / c) (b / c) R)
          (canonicalPerronMarkedLaw M hM (a / c) (b / c) R ν) hmarked
            (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc))
  exact ⟨ρ,⟨hρ,hρmarked⟩,fun θ hθ ↦ tendsto_nhds_unique hθ.1 hρ⟩

/-- The paper's actual `beta^(1/3)` normalization, with genuine graph
empirical marks, has its full canonical-marked weak limit. -/
theorem exists_unique_starred_unmarked_and_markedWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (starredWindowLaw M hM lambda a b R) atTop (𝓝 ν) ∧
        Tendsto (starredMarkedWindowLaw M hM lambda a b R) atTop
          (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) := by
  exact exists_unique_scaled_unmarked_and_markedWindowLaw_limit
    M hM hQP lambda a b ha hab R (sizeScale_pos M hM)

theorem exists_unique_starredMarkedWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ρ : ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)),
      Tendsto (starredMarkedWindowLaw M hM lambda a b R) atTop (𝓝 ρ) := by
  let : PolishSpace (PointMeasure (MarkedWindow S a b R)) :=
    markedPointMeasure_polishSpace M a b hab R
  let : MetricSpace (PointMeasure (MarkedWindow S a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ν,⟨_,hν⟩,_⟩ :=
    exists_unique_starred_unmarked_and_markedWindowLaw_limit M hM hQP lambda a b ha hab R
  exact ⟨canonicalPerronMarkedLaw M hM a b R ν,hν,fun ρ hρ ↦ tendsto_nhds_unique hρ hν⟩

end PerronWright.CompactStarredMarkedWindowLawLimit
