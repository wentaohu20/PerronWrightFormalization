import PerronWright.Probability.WeakProbabilityMarks
import PerronWright.Probability.FinitePointMeasureMarking
import PerronWright.Probability.CompactWindowMarkConcentration
import PerronWright.Probability.ComponentWindowTightness

/-! # Genuine weak-Borel laws of sampled-graph window empirical marks -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowMarkedLaw

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureFintype
  FinitePointMeasureMarking ComponentWindowPointMeasures EmpiricalTypeMarks
  AnnealedMarkedFactorialCounting AnnealedMarkedFactorialExchangeability ComponentWindowTightness

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- A compatible metric on the actual compact size/surplus window.
The instance is scoped, so importing this leaf changes no global metric. -/
scoped instance surplusWindowMetric (a b : ℝ) (R : ℕ) : MetricSpace (SurplusWindow a b R) :=
  TopologicalSpace.metrizableSpaceMetric (SurplusWindow a b R)

open scoped PerronWright.ComponentWindowMarkedLaw

abbrev MarkedWindow (S : Type*) [MeasurableSpace S] (a b : ℝ) (R : ℕ) :=
  SurplusWindow a b R × WeakMark S

theorem markedPointMeasure_polishSpace (M : CompactBJRModel S) (a b : ℝ)
    (hab : a ≤ b) (R : ℕ) : PolishSpace (PointMeasure (MarkedWindow S a b R)) := by
  let : Nonempty (MarkedWindow S a b R) :=
    ⟨((⟨a,le_refl a,hab⟩,⟨0,by omega⟩),ofProbability ⟨M.mu,inferInstance⟩)⟩
  exact FinitePointMeasurePolish.pointMeasure_polishSpace (E := MarkedWindow S a b R)

/-- Every atom carries the actual empirical sampled-type probability
measure of its actual connected component. -/
def markedWindowPointMeasure {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) : PointMeasure (MarkedWindow S a b R) :=
  ofFintype (fun C : WindowComponent a b R 1 G ↦
    (windowAtom a b R 1 C,ofProbability (componentMark x C.val)))

theorem continuous_markedWindowPointMeasure_slice {n : ℕ} (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) :
    Continuous (fun x : Fin n → S ↦ markedWindowPointMeasure x G a b R) := by
  apply continuous_ofFintype.comp
  exact continuous_pi (fun C ↦ continuous_const.prodMk
    (continuous_ofProbability.comp (componentMark_continuous C.val)))

theorem measurable_markedWindowPointMeasure (a b : ℝ) (R n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R) :=
  measurable_from_prod_countable_left (fun ea ↦
    (continuous_markedWindowPointMeasure_slice (AnnealedGraph.toGraph ea) a b R).measurable)

omit [CompactSpace S] in
@[simp] theorem markedWindowPointMeasure_mass {n : ℕ} (x : Fin n → S)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    mass (markedWindowPointMeasure x G a b R) = Fintype.card (WindowComponent a b R 1 G) :=
  mass_ofFintype _

omit [CompactSpace S] in
@[simp] theorem markedWindowPointMeasure_size {n : ℕ} (x : Fin n → S)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    size (markedWindowPointMeasure x G a b R) = Fintype.card (WindowComponent a b R 1 G) :=
  size_ofFintype _

def typedProbability (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure (AnnealedTypedGraph.State S n) :=
  ⟨AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n,inferInstance⟩

/-- The actual marked point-process law: the true joint graph/type law
pushes forward to actual empirical-mark window point measures. -/
def markedWindowLaw (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  (typedProbability M lambda n).map (measurable_markedWindowPointMeasure a b R n).aemeasurable

theorem markedWindowLaw_integral (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ)
    {f : PointMeasure (MarkedWindow S a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(markedWindowLaw M lambda a b R n : Measure _)) =
      ∫ p, f (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R)
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  unfold markedWindowLaw
  rw [ProbabilityMeasure.toMeasure_map]
  exact integral_map (measurable_markedWindowPointMeasure a b R n).aemeasurable hf.aestronglyMeasurable

theorem typed_windowMass_integrable (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ) :
    Integrable (fun p : AnnealedTypedGraph.State S n ↦
      (Fintype.card (WindowComponent a b R 1 (AnnealedTypedGraph.graph p)) : ℝ))
      (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) :=
  typedObservable_integrable_of_continuous_slices M _ _ _ (fun ea ↦ by
    change Continuous (fun _x : Fin n → S ↦
      (Fintype.card (WindowComponent a b R 1 (AnnealedGraph.toGraph ea)) : ℝ))
    exact continuous_const)

theorem markedWindowLaw_mass_integrable (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n : ℕ) :
    Integrable (fun η ↦ (mass η : ℝ))
      (markedWindowLaw M lambda a b R n : Measure (PointMeasure (MarkedWindow S a b R))) := by
  unfold markedWindowLaw
  rw [ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure (NNReal.continuous_coe.measurable.comp measurable_mass).aestronglyMeasurable
    (measurable_markedWindowPointMeasure a b R n).aemeasurable).mpr
  change Integrable (fun p : AnnealedTypedGraph.State S n ↦
    (mass (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R) : ℝ))
      (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n)
  simpa only [markedWindowPointMeasure_mass,NNReal.coe_natCast] using
    typed_windowMass_integrable M lambda a b R n

theorem markedWindowLaw_mass_integral_eq_unmarked (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n : ℕ) :
    (∫ η, (mass η : ℝ) ∂(markedWindowLaw M lambda a b R n :
      Measure (PointMeasure (MarkedWindow S a b R)))) =
        ∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda a b R n :
          Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [markedWindowLaw_integral M lambda a b R n
    (f := fun η ↦ (mass η : ℝ))
    (NNReal.continuous_coe.measurable.comp measurable_mass)]
  simp only [markedWindowPointMeasure_mass,NNReal.coe_natCast]
  rw [AnnealedTypedGraph.graph_expectation M _ (CriticalScaling.time_nonneg lambda n) n
    (fun G ↦ (Fintype.card (WindowComponent a b R 1 G) : ℝ))]
  exact (windowLaw_mass_integral M lambda a b R 1 n).symm

theorem isTight_markedWindowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsTightMeasureSet (Set.range (fun n ↦ (markedWindowLaw M lambda a b R n :
      Measure (PointMeasure (MarkedWindow S a b R))))) := by
  obtain ⟨B,hB,hbound⟩ := exists_window_mass_bound M hM hQP lambda a b ha hab R 1 zero_lt_one
  apply isTightMeasureSet_of_mass_moment_bound (markedWindowLaw M lambda a b R)
    (markedWindowLaw_mass_integrable M lambda a b R) B hB
  intro n
  rw [markedWindowLaw_mass_integral_eq_unmarked]
  exact hbound n

theorem isCompact_closure_markedWindowLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsCompact (closure (Set.range (markedWindowLaw M lambda a b R))) := by
  obtain ⟨B,hB,hbound⟩ := exists_window_mass_bound M hM hQP lambda a b ha hab R 1 zero_lt_one
  apply isCompact_closure_of_mass_moment_bound (markedWindowLaw M lambda a b R)
    (markedWindowLaw_mass_integrable M lambda a b R) B hB
  intro n
  rw [markedWindowLaw_mass_integral_eq_unmarked]
  exact hbound n

end PerronWright.ComponentWindowMarkedLaw
