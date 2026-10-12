import PerronWright.Probability.WindowSizeRescaling
import PerronWright.Probability.CountableTVWindowConvergence

/-! # Literal positive size dilation of actual TV-marked graph windows

The marks are actual natural-type empirical probability measures in
the atomic-variation metric. Dilation changes only the size coordinate.
Component selection, closed-window endpoints and multiplicities are
transported exactly, without any compactness assumption on TV marks.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTVWindowSizeRescaling

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowConvergence
open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking
open ComponentWindowPointMeasures WindowSizeRescaling EmpiricalTypeMarks

def scaledMarkedWindowAtom {n : ℕ} (x : Fin n → ℕ) {G : SimpleGraph (Fin n)}
    (a b : ℝ) (R : ℕ) (c : ℝ) (C : WindowComponent a b R c G) : MarkedWindow a b R :=
  (windowAtom a b R c C, ofProbability (componentMark x C.val))

@[simp] theorem scaledMarkedWindowAtom_mark_val {n : ℕ} (x : Fin n → ℕ)
    {G : SimpleGraph (Fin n)} (a b : ℝ) (R : ℕ) (c : ℝ)
    (C : WindowComponent a b R c G) :
    (scaledMarkedWindowAtom x a b R c C).2.val = componentMark x C.val := rfl

def scaledMarkedWindowPointMeasure {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (c : ℝ) : PointMeasure (MarkedWindow a b R) :=
  ofFintype (scaledMarkedWindowAtom x a b R c (G := G))

@[simp] theorem scaledMarkedWindowPointMeasure_one {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    scaledMarkedWindowPointMeasure x G a b R 1 = markedWindowPointMeasure x G a b R := rfl

theorem measurable_scaledMarkedWindowPointMeasure {n : ℕ} (x : Fin n → ℕ)
    (a b : ℝ) (R : ℕ) (c : ℝ) :
    Measurable (fun G : SimpleGraph (Fin n) ↦ scaledMarkedWindowPointMeasure x G a b R c) :=
  measurable_of_countable _

def markedWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    MarkedWindow (a/c) (b/c) R → MarkedWindow a b R :=
  fun z ↦ (windowScaleMap a b R hc z.1, z.2)

theorem continuous_markedWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    Continuous (markedWindowScaleMap a b R hc) :=
  ((continuous_windowScaleMap a b R hc).comp continuous_fst).prodMk continuous_snd

@[simp] theorem markedWindowScaleMap_mark_val (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (z : MarkedWindow (a/c) (b/c) R) :
    (markedWindowScaleMap a b R hc z).2.val = z.2.val := rfl

theorem markedWindowScaleMap_scaledMarkedWindowAtom {n : ℕ} (x : Fin n → ℕ)
    {G : SimpleGraph (Fin n)} (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (C : WindowComponent (a/c) (b/c) R 1 G) :
    markedWindowScaleMap a b R hc (scaledMarkedWindowAtom x (a/c) (b/c) R 1 C) =
      scaledMarkedWindowAtom x a b R c (windowComponentEquiv a b R hc G C) := by
  apply Prod.ext
  · exact windowScaleMap_windowAtom a b R hc C
  · rfl

theorem scaledMarkedWindowPointMeasure_eq_map (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n)) :
    scaledMarkedWindowPointMeasure x G a b R c =
      mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable
        (markedWindowPointMeasure x G (a/c) (b/c) R) := by
  rw [← scaledMarkedWindowPointMeasure_one, scaledMarkedWindowPointMeasure,
    scaledMarkedWindowPointMeasure, mapPoint_ofFintype]
  apply Subtype.ext
  apply Subtype.ext
  change (∑ C : WindowComponent a b R c G, Measure.dirac (scaledMarkedWindowAtom x a b R c C)) =
    ∑ C : WindowComponent (a/c) (b/c) R 1 G,
      Measure.dirac (markedWindowScaleMap a b R hc (scaledMarkedWindowAtom x (a/c) (b/c) R 1 C))
  simp_rw [markedWindowScaleMap_scaledMarkedWindowAtom]
  exact ((windowComponentEquiv a b R hc G).sum_comp
    (fun C ↦ Measure.dirac (scaledMarkedWindowAtom x a b R c C))).symm

theorem scaledMarkedWindowPointMeasure_forget {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (c : ℝ) :
    mapPoint Prod.fst measurable_fst (scaledMarkedWindowPointMeasure x G a b R c) =
      windowPointMeasure a b R c G := by
  rw [scaledMarkedWindowPointMeasure, mapPoint_ofFintype]
  rfl

theorem mapPoint_constantMark (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (p : VariationMark) (η : PointMeasure (SurplusWindow (a/c) (b/c) R)) :
    mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable
      (constantMark p η) =
        constantMark p (mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc).measurable η) := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  simp only [he, constantMark, mapPoint_ofAtomsPoint]
  rfl

theorem map_canonicalMarkedWindowLaw (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (p : VariationMark) (μ : ProbabilityMeasure (PointMeasure (SurplusWindow (a/c) (b/c) R))) :
    (canonicalMarkedWindowLaw p (a/c) (b/c) R μ).map
      (continuous_mapPoint (markedWindowScaleMap a b R hc)
        (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable =
      canonicalMarkedWindowLaw p a b R (μ.map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure (PointMeasure (SurplusWindow (a/c) (b/c) R))).map
    (constantMark p)).map
      (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable) =
    ((μ : Measure (PointMeasure (SurplusWindow (a/c) (b/c) R))).map
      (mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable)).map
        (constantMark p)
  have hleft : Measurable (constantMark p : PointMeasure (SurplusWindow (a/c) (b/c) R) →
      PointMeasure (MarkedWindow (a/c) (b/c) R)) := by
    unfold constantMark
    exact (continuous_mapPoint (fun z : SurplusWindow (a/c) (b/c) R ↦ (z, p))
      (continuous_id.prodMk continuous_const)).measurable
  have hright : Measurable (constantMark p : PointMeasure (SurplusWindow a b R) →
      PointMeasure (MarkedWindow a b R)) := by
    unfold constantMark
    exact (continuous_mapPoint (fun z : SurplusWindow a b R ↦ (z, p))
      (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    hleft, Measure.map_map hright
      (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable]
  congr 1
  exact funext (mapPoint_constantMark a b R hc p)

end PerronWright.CountableTVWindowSizeRescaling
