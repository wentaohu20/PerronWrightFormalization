import PerronWright.Probability.MarkedWindowSizeRescaling
import PerronWright.Probability.FiniteIrreducibleStarredWindowLaw
import PerronWright.Probability.FiniteIrreducibleMarkedPointLawLimit

/-! # Actual finite starred empirical-mark window laws

Every atom is an actual connected component of the deterministically
typed graph. Positive size dilation changes only its size coordinate,
not its surplus or empirical probability mark. Both closed-window
boundaries are transported exactly. The genuine full source spatial
and empirical-marked weak limits have already been proved; no source
convergence or Brownian identification is assumed here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleStarredMarkedWindowLaw

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureMarking
  ComponentWindowPointMeasures ComponentWindowMarkedLaw WindowSizeRescaling
open MarkedWindowSizeRescaling (scaledMarkedWindowPointMeasure scaledMarkedWindowAtom
  scaledMarkedWindowPointMeasure_eq_map markedWindowScaleMap continuous_markedWindowScaleMap)
open FiniteIrreducibleStarredWindowLaw (windowLaw windowLaw_eq_map_unmarkedWindowLaw starredWindowLaw)
open FiniteIrreduciblePointProcessNormalization
open FiniteIrreducibleComponentProcess (graphLaw)
open FiniteIrreducibleMarkedComponentProcess (perronWeakMark)
open FiniteIrreducibleMarkedWindowConvergence (canonicalPerronMarkedLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def scaledMarkedWindowLaw (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) (c : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  ⟨(graphLaw M lambda n x).map (fun G ↦ scaledMarkedWindowPointMeasure x G a b R c),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

omit [DiscreteTopology S] in
theorem scaledMarkedWindowLaw_integral (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) (c : ℝ) (n : ℕ) (x : Fin n → S)
    {F : PointMeasure (MarkedWindow S a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(scaledMarkedWindowLaw M lambda a b R c n x : Measure _)) =
      ∫ G, F (scaledMarkedWindowPointMeasure x G a b R c) ∂graphLaw M lambda n x := by
  unfold scaledMarkedWindowLaw
  exact integral_map (measurable_of_countable _).aemeasurable hF.aestronglyMeasurable

omit [DiscreteTopology S] in
/-- Exact fixed-assignment graph-law identity, retaining actual marks,
multiplicities and the two closed-window boundaries. -/
theorem scaledMarkedWindowLaw_eq_map (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    scaledMarkedWindowLaw M lambda a b R c n x =
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda (a/c) (b/c) R n x).map
        (continuous_mapPoint (markedWindowScaleMap a b R hc)
          (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (graphLaw M lambda n x).map (fun G ↦ scaledMarkedWindowPointMeasure x G a b R c) =
    ((graphLaw M lambda n x).map (fun G ↦ markedWindowPointMeasure x G (a/c) (b/c) R)).map
      (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable)
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    (FiniteIrreducibleMarkedComponentProcess.measurable_markedWindowPointMeasure x (a/c) (b/c) R)]
  congr 1
  exact funext (scaledMarkedWindowPointMeasure_eq_map a b R hc x)

def starredMarkedWindowLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  scaledMarkedWindowLaw M lambda a b R (sizeScale M hM) n x

omit [DiscreteTopology S] [MetricSpace S] [BorelSpace S] in
theorem starredMarkedWindow_atom_mark (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) {G : SimpleGraph (Fin n)} (a b : ℝ) (R : ℕ)
    (C : WindowComponent a b R (sizeScale M hM) G) :
    (scaledMarkedWindowAtom x a b R (sizeScale M hM) C).2.val =
      EmpiricalTypeMarks.componentMark x C.val := rfl

omit [DiscreteTopology S] [DecidableEq S] in
/-- Pure point-pushforward commutation, proved including multiplicities. -/
theorem mapPoint_constantMark (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (ν : WeakMark S) (η : PointMeasure (SurplusWindow (a/c) (b/c) R)) :
    mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable
      (constantMark ν η) =
        constantMark ν (mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc).measurable η) := by
  obtain ⟨n,x,hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  simp only [he,constantMark,mapPoint_ofAtomsPoint]
  rfl

omit [DiscreteTopology S] in
theorem map_canonicalPerronMarkedLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow (a/c) (b/c) R))) :
    (canonicalPerronMarkedLaw M hM (a/c) (b/c) R ν).map
      (continuous_mapPoint (markedWindowScaleMap a b R hc)
        (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable =
      canonicalPerronMarkedLaw M hM a b R (ν.map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((ν : Measure (PointMeasure (SurplusWindow (a/c) (b/c) R))).map
    (constantMark (perronWeakMark M hM))).map
      (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable) =
    ((ν : Measure (PointMeasure (SurplusWindow (a/c) (b/c) R))).map
      (mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable)).map
        (constantMark (perronWeakMark M hM))
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    (continuous_constantMark _).measurable,
    Measure.map_map (continuous_constantMark _).measurable
      (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable]
  congr 1
  exact funext (mapPoint_constantMark a b R hc (perronWeakMark M hM))

/-- Full actual unmarked and empirical-marked spatial window weak
limits for any fixed positive literal size dilation. -/
theorem exists_unique_scaled_unmarked_and_markedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (R : ℕ) {c : ℝ} (hc : 0 < c) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ windowLaw M lambda a b R c n (v n)) atTop (𝓝 ν) ∧
        Tendsto (fun n ↦ scaledMarkedWindowLaw M lambda a b R c n (v n)) atTop
          (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a,le_rfl,hab⟩,⟨0,by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hab' : a/c ≤ b/c := (div_le_div_iff_of_pos_right hc).mpr hab
  obtain ⟨ν,⟨hν,hmarked⟩,_⟩ :=
    FiniteIrreducibleMarkedPointLawLimit.exists_unique_unmarked_and_markedWindowLaw_limit
      M hM lambda (a/c) (b/c) (div_pos ha hc) hab' R v E hE hround
  let ρ := ν.map (continuous_mapPoint (windowScaleMap a b R hc)
    (continuous_windowScaleMap a b R hc)).measurable.aemeasurable
  have hρ : Tendsto (fun n ↦ windowLaw M lambda a b R c n (v n)) atTop (𝓝 ρ) := by
    simpa only [windowLaw_eq_map_unmarkedWindowLaw M lambda a b R hc,ρ] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda (a/c) (b/c) R n (v n))
        ν hν (continuous_mapPoint _ (continuous_windowScaleMap a b R hc))
  have hρmarked : Tendsto (fun n ↦ scaledMarkedWindowLaw M lambda a b R c n (v n)) atTop
      (𝓝 (canonicalPerronMarkedLaw M hM a b R ρ)) := by
    simpa only [scaledMarkedWindowLaw_eq_map M lambda a b R hc,
      map_canonicalPerronMarkedLaw M hM a b R hc,ρ] using
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda (a/c) (b/c) R n (v n))
          (canonicalPerronMarkedLaw M hM (a/c) (b/c) R ν) hmarked
            (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc))
  exact ⟨ρ,⟨hρ,hρmarked⟩,fun θ hθ ↦ tendsto_nhds_unique hθ.1 hρ⟩

theorem exists_unique_starred_unmarked_and_markedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ starredWindowLaw M hM lambda a b R n (v n)) atTop (𝓝 ν) ∧
        Tendsto (fun n ↦ starredMarkedWindowLaw M hM lambda a b R n (v n)) atTop
          (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) :=
  exists_unique_scaled_unmarked_and_markedWindowLaw_limit
    M hM lambda a b ha hab R (sizeScale_pos M hM) v E hE hround

theorem exists_unique_starredMarkedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ρ : ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)),
      Tendsto (fun n ↦ starredMarkedWindowLaw M hM lambda a b R n (v n)) atTop (𝓝 ρ) := by
  let : PolishSpace (PointMeasure (MarkedWindow S a b R)) :=
    markedPointMeasure_polishSpace M.bjrModel a b hab R
  let : MetricSpace (PointMeasure (MarkedWindow S a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ν,⟨_,hν⟩,_⟩ := exists_unique_starred_unmarked_and_markedWindowLaw_limit
    M hM lambda a b ha hab R v E hE hround
  exact ⟨canonicalPerronMarkedLaw M hM a b R ν,hν,fun ρ hρ ↦ tendsto_nhds_unique hρ hν⟩

end PerronWright.FiniteIrreducibleStarredMarkedWindowLaw

