import PerronWright.Probability.WindowSizeRescaling
import PerronWright.Probability.ComponentWindowMarkedLaw

/-!
# Literal size rescaling of actual empirical-mark window laws

Every selected atom remains an actual connected component of the sampled
typed graph. Rescaling changes only its size coordinate: the mark value
is the actual component empirical probability measure. The component
selection and closed-window boundary atoms are transported exactly.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.MarkedWindowSizeRescaling

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureFintype
  FinitePointMeasureMarking ComponentWindowPointMeasures ComponentWindowMarkedLaw
  WindowSizeRescaling EmpiricalTypeMarks AnnealedMarkedFactorialCounting ComponentPointProcesses

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def scaledMarkedWindowAtom {n : ℕ} (x : Fin n → S) {G : SimpleGraph (Fin n)}
    (a b : ℝ) (R : ℕ) (c : ℝ) (C : WindowComponent a b R c G) :
    MarkedWindow S a b R :=
  (windowAtom a b R c C,ofProbability (componentMark x C.val))

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
/-- The mark is literally the empirical sampled-type measure of the
selected actual graph component, at every rescaling parameter. -/
@[simp] theorem scaledMarkedWindowAtom_mark_val {n : ℕ} (x : Fin n → S)
    {G : SimpleGraph (Fin n)} (a b : ℝ) (R : ℕ) (c : ℝ)
    (C : WindowComponent a b R c G) :
    (scaledMarkedWindowAtom x a b R c C).2.val = componentMark x C.val := rfl

def scaledMarkedWindowPointMeasure {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (c : ℝ) : PointMeasure (MarkedWindow S a b R) :=
  ofFintype (scaledMarkedWindowAtom x a b R c (G := G))

omit [CompactSpace S] in
@[simp] theorem scaledMarkedWindowPointMeasure_one {n : ℕ} (x : Fin n → S)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    scaledMarkedWindowPointMeasure x G a b R 1 = markedWindowPointMeasure x G a b R := rfl

theorem continuous_scaledMarkedWindowPointMeasure_slice {n : ℕ}
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (c : ℝ) :
    Continuous (fun x : Fin n → S ↦ scaledMarkedWindowPointMeasure x G a b R c) := by
  apply continuous_ofFintype.comp
  exact continuous_pi (fun C ↦ continuous_const.prodMk
    (continuous_ofProbability.comp (componentMark_continuous C.val)))

theorem measurable_scaledMarkedWindowPointMeasure (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      scaledMarkedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R c) :=
  measurable_from_prod_countable_left (fun ea ↦
    (continuous_scaledMarkedWindowPointMeasure_slice (AnnealedGraph.toGraph ea) a b R c).measurable)

/-- Size is scaled but the actual weak empirical-mark coordinate is unchanged. -/
def markedWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    MarkedWindow S (a / c) (b / c) R → MarkedWindow S a b R :=
  fun z ↦ (windowScaleMap a b R hc z.1,z.2)

omit [CompactSpace S] in
theorem continuous_markedWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    Continuous (markedWindowScaleMap (S := S) a b R hc) :=
  ((continuous_windowScaleMap a b R hc).comp continuous_fst).prodMk continuous_snd

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
@[simp] theorem markedWindowScaleMap_mark_val (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (z : MarkedWindow S (a / c) (b / c) R) :
    (markedWindowScaleMap a b R hc z).2.val = z.2.val := rfl

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem markedWindowScaleMap_scaledMarkedWindowAtom {n : ℕ} (x : Fin n → S)
    {G : SimpleGraph (Fin n)} (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (C : WindowComponent (a / c) (b / c) R 1 G) :
    markedWindowScaleMap a b R hc (scaledMarkedWindowAtom x (a / c) (b / c) R 1 C) =
      scaledMarkedWindowAtom x a b R c (windowComponentEquiv a b R hc G C) := by
  apply Prod.ext
  · exact windowScaleMap_windowAtom a b R hc C
  · rfl

/-- Exact finite graph/type source formula: no component, multiplicity,
empirical mark or closed-window boundary atom is discarded. -/
theorem scaledMarkedWindowPointMeasure_eq_map (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    scaledMarkedWindowPointMeasure x G a b R c =
      mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable
        (markedWindowPointMeasure x G (a / c) (b / c) R) := by
  rw [← scaledMarkedWindowPointMeasure_one,scaledMarkedWindowPointMeasure,
    scaledMarkedWindowPointMeasure,mapPoint_ofFintype]
  apply Subtype.ext
  apply Subtype.ext
  change (∑ C : WindowComponent a b R c G, Measure.dirac (scaledMarkedWindowAtom x a b R c C)) =
    ∑ C : WindowComponent (a / c) (b / c) R 1 G,
      Measure.dirac (markedWindowScaleMap a b R hc (scaledMarkedWindowAtom x (a / c) (b / c) R 1 C))
  simp_rw [markedWindowScaleMap_scaledMarkedWindowAtom]
  exact ((windowComponentEquiv a b R hc G).sum_comp
    (fun C ↦ Measure.dirac (scaledMarkedWindowAtom x a b R c C))).symm

/-- The genuine marked law of the actual rescaled typed graph window. -/
def scaledMarkedWindowLaw (M : CompactBJRModel S) (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  (typedProbability M lambda n).map (measurable_scaledMarkedWindowPointMeasure a b R c n).aemeasurable

def starredMarkedWindowLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  scaledMarkedWindowLaw M lambda a b R (sizeScale M hM) n

theorem scaledMarkedWindowLaw_integral (M : CompactBJRModel S) (lambda a b : ℝ)
    (R : ℕ) (c : ℝ) (n : ℕ) {f : PointMeasure (MarkedWindow S a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(scaledMarkedWindowLaw M lambda a b R c n : Measure _)) =
      ∫ p, f (scaledMarkedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R c)
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  unfold scaledMarkedWindowLaw
  rw [ProbabilityMeasure.toMeasure_map]
  exact integral_map (measurable_scaledMarkedWindowPointMeasure a b R c n).aemeasurable
    hf.aestronglyMeasurable

/-- Equality of actual typed-graph source laws under continuous rescaling,
not merely an abstract coupling or assumed marked-law factorization. -/
theorem scaledMarkedWindowLaw_eq_map (M : CompactBJRModel S) (lambda a b : ℝ)
    (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledMarkedWindowLaw M lambda a b R c n =
      (markedWindowLaw M lambda (a / c) (b / c) R n).map
        (continuous_mapPoint (markedWindowScaleMap a b R hc)
          (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable := by
  apply Subtype.ext
  change (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map
      (fun p ↦ scaledMarkedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R c) =
    ((AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).map
        (fun p ↦ markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) (a / c) (b / c) R)).map
          (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable)
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    (measurable_markedWindowPointMeasure (a / c) (b / c) R n)]
  congr 1
  funext p
  exact scaledMarkedWindowPointMeasure_eq_map a b R hc p.1 (AnnealedTypedGraph.graph p)

end PerronWright.MarkedWindowSizeRescaling
