import PerronWright.Probability.ComponentGlobalPointProcess
import PerronWright.Probability.ComponentWindowMarkedLaw

/-!
# The actual empirical-marked global component point process

The mark wrapper contains a literal `ProbabilityMeasure S` and has a
proved homeomorphism to its genuine weak topology. Its compactness is
already proved from compactness of `S`, not supplied as an interface.
Every actual graph component carries its actual empirical probability
measure, giving a finite integer point measure on positive size times
surplus times weak probability marks. Its law is the genuine typed graph
law pushforward into the actual vague-Borel point-measure space.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ComponentGlobalMarkedProcess

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague WeakProbabilityMarks
open ComponentWindowPointMeasures ComponentWindowMarkedLaw EmpiricalTypeMarks
open FinitePointMeasureCompact

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

abbrev MarkedPositiveSizeSurplus (S : Type*) [MeasurableSpace S] :=
  PositiveSizeSurplus × WeakMark S

def positiveMarkedAtom {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) : MarkedPositiveSizeSurplus S :=
  (positiveAtom C, ofProbability (componentMark x C))

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
@[simp] theorem positiveMarkedAtom_mark {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) :
    (positiveMarkedAtom x C).2.val = componentMark x C := rfl

def markedProcess {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    LocalPointMeasure (MarkedPositiveSizeSurplus S) :=
  LocallyFinitePointMeasureVague.ofFintype (positiveMarkedAtom x (G := G))

@[simp] theorem markedProcess_toMeasure {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    (markedProcess x G : Measure (MarkedPositiveSizeSurplus S)) =
      ∑ C : G.ConnectedComponent, Measure.dirac (positiveMarkedAtom x C) := rfl

theorem markedProcess_zero (x : Fin 0 → S) (G : SimpleGraph (Fin 0)) :
    (markedProcess x G : Measure (MarkedPositiveSizeSurplus S)) = 0 := by
  let : IsEmpty G.ConnectedComponent :=
    ⟨fun C ↦ (Nat.lt_irrefl 0 (component_vertexCount_pos C)).elim⟩
  simp [markedProcess_toMeasure]

theorem markedProcess_integral {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (f : MarkedPositiveSizeSurplus S → ℝ) :
    (∫ z, f z ∂(markedProcess x G : Measure (MarkedPositiveSizeSurplus S))) =
      ∑ C : G.ConnectedComponent, f (positiveMarkedAtom x C) := ofFintype_integral _ _

theorem continuous_markedProcess_slice {n : ℕ} (G : SimpleGraph (Fin n)) :
    Continuous (fun x : Fin n → S ↦ markedProcess x G) := by
  apply LocallyFinitePointMeasureVague.continuous_ofFintype.comp
  exact continuous_pi (fun C ↦ continuous_const.prodMk
    (continuous_ofProbability.comp (AnnealedMarkedFactorialCounting.componentMark_continuous C)))

theorem measurable_markedProcess (n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      markedProcess p.1 (AnnealedTypedGraph.graph p)) :=
  measurable_from_prod_countable_left (fun ea ↦
    (continuous_markedProcess_slice (AnnealedGraph.toGraph ea)).measurable)

def markedProcessLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  (typedProbability M lambda n).map (measurable_markedProcess n).aemeasurable

@[simp] theorem markedProcessLaw_toMeasure (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (markedProcessLaw M lambda n : Measure (LocalPointMeasure (MarkedPositiveSizeSurplus S))) =
      (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map
          (fun p ↦ markedProcess p.1 (AnnealedTypedGraph.graph p)) := rfl

def markedPositiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    MarkedWindow S a b R → MarkedPositiveSizeSurplus S :=
  fun z ↦ (positiveWindowEmbedding a b R ha z.1, z.2)

omit [CompactSpace S] in
theorem continuous_markedPositiveWindowEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    Continuous (markedPositiveWindowEmbedding (S := S) a b R ha) :=
  ((continuous_positiveWindowEmbedding a b R ha).comp continuous_fst).prodMk continuous_snd

def markedWindowSet (a b : ℝ) (R : ℕ) : Set (MarkedPositiveSizeSurplus S) :=
  Prod.fst ⁻¹' positiveWindowSet a b R

omit [CompactSpace S] in
theorem exists_marked_test_window {D : Type*} [Fintype D]
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    ∃ a b : ℝ, ∃ R : ℕ, 0 < a ∧ a ≤ b ∧
      ∀ i, tsupport (f i) ⊆ markedWindowSet a b R := by
  have hK : IsCompact (⋃ i, tsupport (f i)) :=
    isCompact_iUnion (fun i ↦ (f i).hasCompactSupport)
  obtain ⟨a, b, R, ha, hab, hW⟩ := exists_compact_window (hK.image continuous_fst)
  refine ⟨a, b, R, ha, hab, fun i z hz ↦ ?_⟩
  exact hW ⟨z, Set.mem_iUnion.mpr ⟨i, hz⟩, rfl⟩

/-- Exact global/window equality for actual empirical-marked atoms. -/
theorem markedProcess_integral_eq_window (a b : ℝ) (R : ℕ) (ha : 0 < a)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) (hf : tsupport f ⊆ markedWindowSet a b R) :
    (∫ z, f z ∂(markedProcess x G : Measure (MarkedPositiveSizeSurplus S))) =
      ∫ z, f (markedPositiveWindowEmbedding a b R ha z)
        ∂((markedWindowPointMeasure x G a b R : FiniteMeasure (MarkedWindow S a b R)) :
          Measure (MarkedWindow S a b R)) := by
  rw [markedProcess_integral, markedWindowPointMeasure,
    FinitePointMeasureFintype.ofFintype_integral]
  simp only [markedPositiveWindowEmbedding, positiveWindowEmbedding_windowAtom]
  apply Finset.sum_congr_set {C : G.ConnectedComponent |
    componentAtom 1 C ∈ windowSet a b R}
    (fun C ↦ f (positiveMarkedAtom x C))
    (fun C : WindowComponent a b R 1 G ↦ f (positiveMarkedAtom x C.val))
  · intro C _
    rfl
  · intro C hC
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hC
    simpa [markedWindowSet, positiveWindowSet, positiveMarkedAtom, componentAtom,
      ComponentPointProcesses.atom, positiveAtom, ambientEmbedding] using hf hs

end PerronWright.ComponentGlobalMarkedProcess
