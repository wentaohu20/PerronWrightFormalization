import PerronWright.Probability.PointProcessNormalization
import PerronWright.Probability.FinitePointMeasureFintype
import PerronWright.Probability.FinitePointMeasureMeasurable

/-!
# Genuine graph component laws in a compact size-surplus window

The atoms are the literal connected components of the finite graph. We
filter these atoms, package their coordinates in the actual compact
window, and push the already constructed annealed graph law forward to
the weak-Borel space of finite integer point measures.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowPointMeasures

open ComponentCounts ComponentPointProcesses FinitePointMeasureCompact
open FinitePointMeasureFintype

/-- The ambient closed window corresponding to the literal compact type. -/
def windowSet (a b : ℝ) (R : ℕ) : Set (ℝ × ℕ) := Set.Icc a b ×ˢ Set.Iic R

theorem measurableSet_windowSet (a b : ℝ) (R : ℕ) :
    MeasurableSet (windowSet a b R) := measurableSet_Icc.prod measurableSet_Iic

def windowEmbedding (a b : ℝ) (R : ℕ) : SurplusWindow a b R → ℝ × ℕ :=
  fun z ↦ (z.1.val, z.2.val)

theorem continuous_windowEmbedding (a b : ℝ) (R : ℕ) :
    Continuous (windowEmbedding a b R) :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_of_discreteTopology : Continuous (fun z : Fin (R + 1) ↦ z.val)).comp
      continuous_snd)

theorem measurable_windowEmbedding (a b : ℝ) (R : ℕ) :
    Measurable (windowEmbedding a b R) := (continuous_windowEmbedding a b R).measurable

theorem windowEmbedding_mem (a b : ℝ) (R : ℕ) (z : SurplusWindow a b R) :
    windowEmbedding a b R z ∈ windowSet a b R :=
  ⟨z.1.property, Nat.le_of_lt_succ z.2.isLt⟩

/-- The original size coordinate when `c = 1`, and the paper's starred
coordinate when `c = sizeScale M hM`. -/
def componentAtom (c : ℝ) {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : ℝ × ℕ :=
  (c * (componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ), componentSurplus C)

theorem componentAtom_eq_rescale (c : ℝ) {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) :
    componentAtom c C = sizeRescale c (atom C) := by
  simp [componentAtom, sizeRescale, atom, mul_div_assoc]

def WindowComponent (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) :=
  {C : G.ConnectedComponent // componentAtom c C ∈ windowSet a b R}

instance (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype (WindowComponent a b R c G) := inferInstanceAs (Fintype {C :
      G.ConnectedComponent // componentAtom c C ∈ windowSet a b R})

def windowAtom (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ}
    {G : SimpleGraph (Fin n)} (C : WindowComponent a b R c G) :
    SurplusWindow a b R :=
  (⟨(componentAtom c C.val).1, C.property.1⟩,
    ⟨(componentAtom c C.val).2, Nat.lt_succ_iff.mpr C.property.2⟩)

@[simp] theorem windowEmbedding_windowAtom (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} {G : SimpleGraph (Fin n)} (C : WindowComponent a b R c G) :
    windowEmbedding a b R (windowAtom a b R c C) = componentAtom c C.val := rfl

/-- The actual compact-window point measure of a finite graph, with one
labelled atom per selected connected component and genuine multiplicity. -/
def windowPointMeasure (a b : ℝ) (R : ℕ) (c : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) : PointMeasure (SurplusWindow a b R) :=
  ofFintype (windowAtom a b R c (G := G))

@[simp] theorem windowPointMeasure_toMeasure (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((windowPointMeasure a b R c G : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)) =
        ∑ C : WindowComponent a b R c G, Measure.dirac (windowAtom a b R c C) := rfl

@[simp] theorem windowPointMeasure_size (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    size (windowPointMeasure a b R c G) = Fintype.card (WindowComponent a b R c G) :=
  size_ofFintype _

@[simp] theorem windowPointMeasure_mass (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    mass (windowPointMeasure a b R c G) = Fintype.card (WindowComponent a b R c G) :=
  mass_ofFintype _

/-- Measurability is into the genuine weak-Borel point-measure space.
There is no continuity assertion for a discontinuous boundary filter. -/
theorem measurable_windowPointMeasure (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    Measurable (windowPointMeasure a b R c : SimpleGraph (Fin n) →
      PointMeasure (SurplusWindow a b R)) := measurable_of_finite _

theorem windowPointMeasure_count (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) {A : Set (SurplusWindow a b R)}
    (hA : MeasurableSet A) :
    count (windowPointMeasure a b R c G) A =
      Fintype.card {C : WindowComponent a b R c G // windowAtom a b R c C ∈ A} :=
  count_ofFintype _ hA

theorem windowPointMeasure_integral (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (f : SurplusWindow a b R → ℝ) :
    (∫ z, f z ∂((windowPointMeasure a b R c G :
      FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))) =
        ∑ C : WindowComponent a b R c G, f (windowAtom a b R c C) :=
  ofFintype_integral _ _

theorem rescaled_unmarked_eq_sum (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (unmarked G).map (sizeRescale c) =
      ∑ C : G.ConnectedComponent, Measure.dirac (componentAtom c C) := by
  unfold unmarked
  rw [Measure.map_finset_sum' (sizeRescale_measurable c).aemeasurable]
  simp only [Measure.map_dirac' (sizeRescale_measurable c), componentAtom_eq_rescale]

/-- Embedding the actual window point measure in the ambient space is
exactly restriction of the original rescaled component measure. -/
theorem map_windowPointMeasure_eq_restrict (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    (((windowPointMeasure a b R c G : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).map (windowEmbedding a b R)) =
        ((unmarked G).map (sizeRescale c)).restrict (windowSet a b R) := by
  rw [windowPointMeasure_toMeasure,
    Measure.map_finset_sum' (measurable_windowEmbedding a b R).aemeasurable]
  simp only [Measure.map_dirac' (measurable_windowEmbedding a b R),
    windowEmbedding_windowAtom]
  rw [rescaled_unmarked_eq_sum]
  change (∑ C : WindowComponent a b R c G, Measure.dirac (componentAtom c C.val)) =
    Measure.restrictₗ (windowSet a b R) (∑ C, Measure.dirac (componentAtom c C))
  rw [map_sum]
  change (∑ C : WindowComponent a b R c G, Measure.dirac (componentAtom c C.val)) =
    ∑ C, (Measure.dirac (componentAtom c C)).restrict (windowSet a b R)
  simp only [restrict_dirac]
  change (∑ C : {C : G.ConnectedComponent // componentAtom c C ∈ windowSet a b R},
    Measure.dirac (componentAtom c C.val)) = _
  exact (Finset.sum_congr_set
    {C : G.ConnectedComponent | componentAtom c C ∈ windowSet a b R}
    (fun C ↦ if componentAtom c C ∈ windowSet a b R then
      Measure.dirac (componentAtom c C) else 0)
    (fun C ↦ Measure.dirac (componentAtom c C.val))
    (fun C hC ↦ if_pos hC) (fun C hC ↦ if_neg hC)).symm

/-- Ambient Borel-cell evaluation agrees with the restricted original
unmarked measure, including every atom on the closed window boundary. -/
theorem windowPointMeasure_apply_preimage (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) {B : Set (ℝ × ℕ)} (hB : MeasurableSet B) :
    ((windowPointMeasure a b R c G : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)) (windowEmbedding a b R ⁻¹' B) =
        ((unmarked G).map (sizeRescale c)) (B ∩ windowSet a b R) := by
  rw [← Measure.map_apply (measurable_windowEmbedding a b R) hB,
    map_windowPointMeasure_eq_restrict, Measure.restrict_apply hB]

theorem windowPointMeasure_count_preimage (a b : ℝ) (R : ℕ) (c : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) {B : Set (ℝ × ℕ)} (hB : MeasurableSet B) :
    (count (windowPointMeasure a b R c G) (windowEmbedding a b R ⁻¹' B) : ℝ) =
      (((unmarked G).map (sizeRescale c)).real (B ∩ windowSet a b R)) := by
  rw [← measure_real_eq_count _ ((measurable_windowEmbedding a b R) hB)]
  exact congrArg ENNReal.toReal (windowPointMeasure_apply_preimage a b R c G hB)

theorem map_unmarkedWindow_eq_restrict (a b : ℝ) (R : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    (((windowPointMeasure a b R 1 G : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).map (windowEmbedding a b R)) =
        (unmarked G).restrict (windowSet a b R) := by
  have hid : sizeRescale 1 = (id : ℝ × ℕ → ℝ × ℕ) := by
    funext z
    simp [sizeRescale]
  simpa only [hid, Measure.map_id] using map_windowPointMeasure_eq_restrict a b R 1 G

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The actual annealed compact-window law, using the existing finite
graph probability law and the weak-Borel window point-measure space. -/
def windowLaw (M : CompactBJRModel S) (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  ⟨(AnnealedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).map (windowPointMeasure a b R c),
    Measure.isProbabilityMeasure_map (measurable_windowPointMeasure a b R c n).aemeasurable⟩

@[simp] theorem windowLaw_toMeasure (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    (windowLaw M lambda a b R c n : Measure (PointMeasure (SurplusWindow a b R))) =
      (AnnealedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map (windowPointMeasure a b R c) := rfl

theorem windowLaw_integrable (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    Integrable f (windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [windowLaw_toMeasure]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_windowPointMeasure a b R c n).aemeasurable).mpr Integrable.of_finite

/-- Expectations are literal expectations under the previously
constructed graph law, not a replacement abstract process law. -/
theorem windowLaw_integral (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
        ∫ G, f (windowPointMeasure a b R c G) ∂(AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  rw [windowLaw_toMeasure]
  exact integral_map (measurable_windowPointMeasure a b R c n).aemeasurable
    hf.aestronglyMeasurable

theorem windowLaw_mass_integrable (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    Integrable (fun η ↦ (mass η : ℝ)) (windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R c n
    (NNReal.continuous_coe.measurable.comp measurable_mass)

theorem windowLaw_mass_integral (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    (∫ η, (mass η : ℝ) ∂(windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
        ∫ G, (Fintype.card (WindowComponent a b R c G) : ℝ) ∂(AnnealedGraph.law M
          (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  have hm : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦ (mass η : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_mass
  rw [windowLaw_integral M lambda a b R c n hm]
  simp only [windowPointMeasure_mass, NNReal.coe_natCast]

theorem windowLaw_count_integral (M : CompactBJRModel S)
    (lambda a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    {A : Set (SurplusWindow a b R)} (hA : MeasurableSet A) :
    (∫ η, (count η A : ℝ) ∂(windowLaw M lambda a b R c n :
      Measure (PointMeasure (SurplusWindow a b R)))) =
        ∫ G, (Fintype.card {C : WindowComponent a b R c G //
          windowAtom a b R c C ∈ A} : ℝ) ∂(AnnealedGraph.law M
            (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) := by
  have hc : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦ (count η A : ℝ)) :=
    (Nat.isClosedEmbedding_coe_real.continuous.measurable).comp
      (FinitePointMeasureMeasurable.measurable_count hA)
  rw [windowLaw_integral M lambda a b R c n hc]
  simp only [windowPointMeasure_count a b R c _ hA]

def unmarkedWindowLaw (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  windowLaw M lambda a b R 1 n

def starredWindowLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  windowLaw M lambda a b R (sizeScale M hM) n

theorem map_starredWindow_eq_restrict (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (((windowPointMeasure a b R (sizeScale M hM) G :
      FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R)).map
        (windowEmbedding a b R)) = (unmarkedStar M hM G).restrict (windowSet a b R) :=
  map_windowPointMeasure_eq_restrict a b R (sizeScale M hM) G

end PerronWright.ComponentWindowPointMeasures
