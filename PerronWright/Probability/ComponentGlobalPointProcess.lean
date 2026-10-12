import PerronWright.Probability.LocallyFinitePointMeasureVague
import PerronWright.Probability.ComponentWindowPointMeasures

/-!
# The genuine unmarked graph process on positive size times surplus

The literal finite connected-component Dirac sum is an actual locally
finite integer point measure, with its vague-Borel probability law.
Every compact subset of the ground space lies in a positive compact
size-surplus window. Actual compact-support integrals agree exactly
with their window integrals when the support is contained there.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentGlobalPointProcess

open ComponentCounts EmpiricalTypeMarks ComponentPointProcesses
open ComponentWindowPointMeasures LocallyFinitePointMeasureVague

abbrev PositiveSizeSurplus := Set.Ioi (0 : ℝ) × ℕ

instance positiveSize_locallyCompact : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

def ambientEmbedding (z : PositiveSizeSurplus) : ℝ × ℕ := (z.1.val, z.2)

theorem continuous_ambientEmbedding : Continuous ambientEmbedding :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

theorem measurable_ambientEmbedding : Measurable ambientEmbedding :=
  continuous_ambientEmbedding.measurable

theorem component_vertexCount_pos {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : 0 < n := by
  obtain ⟨v, _⟩ := componentBlock_nonempty C
  exact lt_of_le_of_lt (Nat.zero_le v.val) v.isLt

theorem atom_size_pos {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : 0 < (atom C).1 := by
  exact div_pos (Nat.cast_pos.mpr (componentSize_pos C))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (component_vertexCount_pos C)) _)

/-- The literal paper size and surplus, now in the correct positive
ground space. The empty graph has no component to be packaged. -/
def positiveAtom {n : ℕ} {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    PositiveSizeSurplus := (⟨(atom C).1, atom_size_pos C⟩, (atom C).2)

@[simp] theorem ambientEmbedding_positiveAtom {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : ambientEmbedding (positiveAtom C) = atom C := rfl

/-- The actual graph component process, not a surrogate coordinate
vector or an assumed abstract process. -/
def unmarkedProcess {n : ℕ} (G : SimpleGraph (Fin n)) :
    LocalPointMeasure PositiveSizeSurplus := ofFintype (positiveAtom (G := G))

@[simp] theorem unmarkedProcess_toMeasure {n : ℕ} (G : SimpleGraph (Fin n)) :
    (unmarkedProcess G : Measure PositiveSizeSurplus) =
      ∑ C : G.ConnectedComponent, Measure.dirac (positiveAtom C) := rfl

theorem unmarkedProcess_zero (G : SimpleGraph (Fin 0)) :
    (unmarkedProcess G : Measure PositiveSizeSurplus) = 0 := by
  let : IsEmpty G.ConnectedComponent :=
    ⟨fun C ↦ (Nat.lt_irrefl 0 (component_vertexCount_pos C)).elim⟩
  simp [unmarkedProcess_toMeasure]

/-- Mapping to the old ambient coordinates recovers exactly the
already established actual source `ComponentPointProcesses.unmarked`. -/
theorem map_unmarkedProcess {n : ℕ} (G : SimpleGraph (Fin n)) :
    (unmarkedProcess G : Measure PositiveSizeSurplus).map ambientEmbedding = unmarked G := by
  rw [unmarkedProcess_toMeasure,
    Measure.map_finset_sum' measurable_ambientEmbedding.aemeasurable]
  simp only [Measure.map_dirac' measurable_ambientEmbedding,
    ambientEmbedding_positiveAtom, unmarked]

theorem unmarkedProcess_integral {n : ℕ} (G : SimpleGraph (Fin n))
    (f : PositiveSizeSurplus → ℝ) :
    (∫ z, f z ∂(unmarkedProcess G : Measure PositiveSizeSurplus)) =
      ∑ C : G.ConnectedComponent, f (positiveAtom C) := ofFintype_integral _ _

theorem measurable_unmarkedProcess (n : ℕ) :
    Measurable (unmarkedProcess : SimpleGraph (Fin n) → LocalPointMeasure PositiveSizeSurplus) :=
  measurable_of_finite _

/-- Literal compact containment in a positive closed size-surplus
window, derived from extreme values and finite compact surplus images. -/
theorem exists_compact_window {K : Set PositiveSizeSurplus} (hK : IsCompact K) :
    ∃ a b : ℝ, ∃ R : ℕ, 0 < a ∧ a ≤ b ∧
      K ⊆ ambientEmbedding ⁻¹' windowSet a b R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, 0, zero_lt_one, le_rfl, Set.empty_subset _⟩
  have hc : Continuous (fun z : PositiveSizeSurplus ↦ z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  obtain ⟨R, hR⟩ := (hK.image continuous_snd).finite_of_discrete.bddAbove
  refine ⟨u.1.val, v.1.val, R, u.1.property, hmin hv, ?_⟩
  intro z hz
  exact ⟨⟨hmin hz, hmax hz⟩, hR (Set.mem_image_of_mem Prod.snd hz)⟩

theorem exists_test_window (f : C_c(PositiveSizeSurplus, ℝ)) :
    ∃ a b : ℝ, ∃ R : ℕ, 0 < a ∧ a ≤ b ∧
      tsupport f ⊆ ambientEmbedding ⁻¹' windowSet a b R :=
  exists_compact_window f.hasCompactSupport

def positiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (z : FinitePointMeasureCompact.SurplusWindow a b R) : PositiveSizeSurplus :=
  (⟨z.1.val, lt_of_lt_of_le ha z.1.property.1⟩, z.2.val)

theorem continuous_positiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    Continuous (positiveWindowEmbedding a b R ha) := by
  apply Continuous.prodMk
  · exact (continuous_subtype_val.comp continuous_fst).subtype_mk _
  · exact (continuous_of_discreteTopology : Continuous (fun r : Fin (R + 1) ↦ r.val)).comp
      continuous_snd

theorem measurable_positiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    Measurable (positiveWindowEmbedding a b R ha) :=
  (continuous_positiveWindowEmbedding a b R ha).measurable

def positiveWindowSet (a b : ℝ) (R : ℕ) : Set PositiveSizeSurplus :=
  ambientEmbedding ⁻¹' windowSet a b R

theorem measurableSet_positiveWindowSet (a b : ℝ) (R : ℕ) :
    MeasurableSet (positiveWindowSet a b R) :=
  measurable_ambientEmbedding (measurableSet_windowSet a b R)

theorem range_positiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    Set.range (positiveWindowEmbedding a b R ha) = positiveWindowSet a b R := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1.property, Nat.le_of_lt_succ w.2.isLt⟩
  · intro hz
    exact ⟨(⟨z.1.val, hz.1⟩, ⟨z.2, Nat.lt_succ_iff.mpr hz.2⟩), rfl⟩

theorem isCompact_positiveWindowSet (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    IsCompact (positiveWindowSet a b R) := by
  rw [← range_positiveWindowEmbedding a b R ha]
  exact isCompact_range (continuous_positiveWindowEmbedding a b R ha)

@[simp] theorem ambientEmbedding_positiveWindowEmbedding (a b : ℝ) (R : ℕ)
    (ha : 0 < a) (z : FinitePointMeasureCompact.SurplusWindow a b R) :
    ambientEmbedding (positiveWindowEmbedding a b R ha z) = windowEmbedding a b R z := rfl

@[simp] theorem positiveWindowEmbedding_windowAtom (a b : ℝ) (R : ℕ)
    (ha : 0 < a) {n : ℕ} {G : SimpleGraph (Fin n)} (C : WindowComponent a b R 1 G) :
    positiveWindowEmbedding a b R ha (windowAtom a b R 1 C) = positiveAtom C.val := by
  apply Prod.ext
  · apply Subtype.ext
    simp [positiveWindowEmbedding, windowAtom, positiveAtom, componentAtom, atom]
  · rfl

/-- The actual global source's compact-window restriction is exactly
the already constructed finite integer window measure, embedded in
the correct positive-size ground space. -/
theorem map_windowPointMeasure_eq_restrict_process (a b : ℝ) (R : ℕ) (ha : 0 < a)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    (((windowPointMeasure a b R 1 G :
      FiniteMeasure (FinitePointMeasureCompact.SurplusWindow a b R)) :
        Measure (FinitePointMeasureCompact.SurplusWindow a b R)).map
          (positiveWindowEmbedding a b R ha)) =
      (unmarkedProcess G : Measure PositiveSizeSurplus).restrict (positiveWindowSet a b R) := by
  rw [windowPointMeasure_toMeasure,
    Measure.map_finset_sum' (measurable_positiveWindowEmbedding a b R ha).aemeasurable]
  simp only [Measure.map_dirac' (measurable_positiveWindowEmbedding a b R ha),
    positiveWindowEmbedding_windowAtom]
  rw [unmarkedProcess_toMeasure]
  change (∑ C : WindowComponent a b R 1 G, Measure.dirac (positiveAtom C.val)) =
    Measure.restrictₗ (positiveWindowSet a b R) (∑ C, Measure.dirac (positiveAtom C))
  rw [map_sum]
  change (∑ C : WindowComponent a b R 1 G, Measure.dirac (positiveAtom C.val)) =
    ∑ C, (Measure.dirac (positiveAtom C)).restrict (positiveWindowSet a b R)
  simp only [restrict_dirac]
  have hm (C : G.ConnectedComponent) : positiveAtom C ∈ positiveWindowSet a b R ↔
      componentAtom 1 C ∈ windowSet a b R := by
    simp [positiveWindowSet, ambientEmbedding, positiveAtom, componentAtom, atom]
  simp only [hm]
  exact (Finset.sum_congr_set {C : G.ConnectedComponent |
    componentAtom 1 C ∈ windowSet a b R}
    (fun C ↦ if componentAtom 1 C ∈ windowSet a b R then
      Measure.dirac (positiveAtom C) else 0)
    (fun C : WindowComponent a b R 1 G ↦ Measure.dirac (positiveAtom C.val))
    (fun C hC ↦ if_pos hC) (fun C hC ↦ if_neg hC)).symm

/-- A compact-support test, contained in a literal positive window,
has exactly the same integral against the genuine global process and
the already constructed actual window point measure. -/
theorem unmarkedProcess_integral_eq_window (a b : ℝ) (R : ℕ) (ha : 0 < a)
    {n : ℕ} (G : SimpleGraph (Fin n)) (f : C_c(PositiveSizeSurplus, ℝ))
    (hf : tsupport f ⊆ ambientEmbedding ⁻¹' windowSet a b R) :
    (∫ z, f z ∂(unmarkedProcess G : Measure PositiveSizeSurplus)) =
      ∫ z, f (positiveWindowEmbedding a b R ha z)
        ∂((windowPointMeasure a b R 1 G :
          FiniteMeasure (FinitePointMeasureCompact.SurplusWindow a b R)) :
            Measure (FinitePointMeasureCompact.SurplusWindow a b R)) := by
  rw [unmarkedProcess_integral, windowPointMeasure_integral]
  simp only [positiveWindowEmbedding_windowAtom]
  apply Finset.sum_congr_set {C : G.ConnectedComponent |
    componentAtom 1 C ∈ windowSet a b R}
    (fun C ↦ f (positiveAtom C)) (fun C : WindowComponent a b R 1 G ↦ f (positiveAtom C.val))
  · intro C _
    rfl
  · intro C hC
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hC
    simpa [componentAtom, atom, positiveAtom, ambientEmbedding] using hf hs

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The actual annealed graph law pushed to the genuine vague-Borel
locally finite point-measure space. -/
def unmarkedProcessLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess,
      Measure.isProbabilityMeasure_map (measurable_unmarkedProcess n).aemeasurable⟩

@[simp] theorem unmarkedProcessLaw_toMeasure (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (unmarkedProcessLaw M lambda n : Measure (LocalPointMeasure PositiveSizeSurplus)) =
      (AnnealedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess := rfl

end PerronWright.ComponentGlobalPointProcess
