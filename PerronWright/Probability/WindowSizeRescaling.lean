import PerronWright.Probability.ComponentWindowPointMeasures
import PerronWright.Probability.FinitePointMeasureMarking

/-!
# Exact positive size rescaling of actual compact-window point laws

The source window is `[a/c,b/c]` and the target window is `[a,b]`.
The finite family is the actual graph's connected-component family;
both its selection predicate and its atoms are transported exactly.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.WindowSizeRescaling

open ComponentWindowPointMeasures ComponentPointProcesses
open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking

theorem sizeRescale_mem_windowSet_iff (a b : ℝ) (R : ℕ)
    {c : ℝ} (hc : 0 < c) (z : ℝ × ℕ) :
    sizeRescale c z ∈ windowSet a b R ↔ z ∈ windowSet (a / c) (b / c) R := by
  simp only [windowSet, sizeRescale, Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
  rw [mul_comm c z.1, ← div_le_iff₀ hc, ← le_div_iff₀ hc]

def windowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    SurplusWindow (a / c) (b / c) R → SurplusWindow a b R :=
  fun z ↦ (⟨c * z.1.val, by
    have hlo := (div_le_iff₀ hc).mp z.1.property.1
    have hhi := (le_div_iff₀ hc).mp z.1.property.2
    constructor <;> nlinarith⟩, z.2)

theorem continuous_windowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    Continuous (windowScaleMap a b R hc) :=
  ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
    continuous_snd

theorem componentAtom_scaled (c : ℝ) {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) :
    componentAtom c C = sizeRescale c (componentAtom 1 C) := by
  simp [componentAtom, sizeRescale, mul_div_assoc]

def windowComponentEquiv (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    WindowComponent (a / c) (b / c) R 1 G ≃ WindowComponent a b R c G :=
  Equiv.subtypeEquivRight (fun C ↦ by
    rw [componentAtom_scaled c]
    exact (sizeRescale_mem_windowSet_iff a b R hc (componentAtom 1 C)).symm)

theorem windowScaleMap_windowAtom (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : WindowComponent (a / c) (b / c) R 1 G) :
    windowScaleMap a b R hc (windowAtom (a / c) (b / c) R 1 C) =
      windowAtom a b R c (windowComponentEquiv a b R hc G C) := by
  apply Prod.ext
  · apply Subtype.ext
    change c * (1 * (ComponentCounts.componentSize C.val : ℝ) /
      (n : ℝ) ^ (2 / 3 : ℝ)) =
        c * (ComponentCounts.componentSize C.val : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)
    simp only [one_mul, mul_div_assoc]
  · apply Fin.ext
    rfl

/-- The actual rescaled finite graph window is a genuine point-measure
pushforward, with no lost atoms on either closed-window boundary. -/
theorem windowPointMeasure_eq_map (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    windowPointMeasure a b R c G =
      mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable
        (windowPointMeasure (a / c) (b / c) R 1 G) := by
  rw [windowPointMeasure, windowPointMeasure, mapPoint_ofFintype]
  apply Subtype.ext
  apply Subtype.ext
  change (∑ C : WindowComponent a b R c G, Measure.dirac (windowAtom a b R c C)) =
    ∑ C : WindowComponent (a / c) (b / c) R 1 G,
      Measure.dirac (windowScaleMap a b R hc (windowAtom (a / c) (b / c) R 1 C))
  simp_rw [windowScaleMap_windowAtom]
  exact ((windowComponentEquiv a b R hc G).sum_comp
    (fun C ↦ Measure.dirac (windowAtom a b R c C))).symm

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Equality of the actual graph source laws in the weak-Borel space,
not only equality of their individual point configurations. -/
theorem windowLaw_eq_map_unmarkedWindowLaw (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    windowLaw M lambda a b R c n =
      (unmarkedWindowLaw M lambda (a / c) (b / c) R n).map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable := by
  apply Subtype.ext
  change (AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map (windowPointMeasure a b R c) =
    ((AnnealedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).map
        (windowPointMeasure (a / c) (b / c) R 1)).map
          (mapPoint (windowScaleMap a b R hc)
            (continuous_windowScaleMap a b R hc).measurable)
  rw [Measure.map_map
    (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable
    (measurable_windowPointMeasure (a / c) (b / c) R 1 n)]
  congr 1
  funext G
  exact windowPointMeasure_eq_map a b R hc G

end PerronWright.WindowSizeRescaling
