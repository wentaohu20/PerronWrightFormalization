import PerronWright.Probability.CompactWindowBoundary

/-!
# Actual weak pushforward convergence for finite point-count vectors

For a discrete target, a clopen cell's preimage frontier consists only
of discontinuity points. Genuine open/continuity-set Portmanteau then
proves the a.e.-continuous mapping theorem for actual probability
measures. The graph application supplies a.e. continuity from the
proved shrinking-strip model estimates, not from a mapping premise.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.PointMeasureCountMapping

open FinitePointMeasureCompact FinitePointMeasureCounts FinitePointMeasureMeasurable
open ComponentWindowPointMeasures CompactWindowBoundary

theorem frontier_preimage_subset_not_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) {A : Set Y} (hA : IsClopen A) :
    frontier (f ⁻¹' A) ⊆ {x | ¬ ContinuousAt f x} := by
  intro x hx hcont
  have hx' : x ∈ closure (f ⁻¹' A) ∧ x ∉ interior (f ⁻¹' A) := hx
  by_cases ha : f x ∈ A
  · exact hx'.2 (mem_interior_iff_mem_nhds.mpr
      (hcont.preimage_mem_nhds (hA.isOpen.mem_nhds ha)))
  · have hcompl : (f ⁻¹' A)ᶜ ∈ 𝓝 x := by
      exact hcont.preimage_mem_nhds (hA.isClosed.isOpen_compl.mem_nhds ha)
    have hh := mem_interior_iff_mem_nhds.mpr hcompl
    rw [interior_compl] at hh
    exact hh hx'.1

/-- Actual probability-law weak convergence pushes forward through an
actual measurable map to a discrete space if that map is continuous at
almost every point of the actual limiting law. No atom convergence,
tightness, or mapping theorem is imposed as an unproved interface. -/
theorem tendsto_map_discrete_of_ae_continuousAt
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y] [DiscreteTopology Y]
    (νs : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hν : Tendsto νs atTop (𝓝 ν)) (f : X → Y) (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(ν : Measure X), ContinuousAt f x) :
    Tendsto (fun n ↦ (νs n).map hf.aemeasurable) atTop (𝓝 (ν.map hf.aemeasurable)) := by
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro A hA
  have hnull : (ν : Measure X) (frontier (f ⁻¹' A)) = 0 := by
    apply measure_mono_null
      (frontier_preimage_subset_not_continuousAt f (isClopen_discrete A))
    exact ae_iff.mp hcont
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν hnull
  change (ν : Measure X).map f A ≤
    liminf (fun n ↦ (νs n : Measure X).map f A) atTop
  simp only [Measure.map_apply hf hA.measurableSet]
  exact ht.liminf_eq.ge

variable {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E]
  [BorelSpace E] [Nonempty E]

/-- Null frontiers imply weak convergence of the genuine finite
integer count-vector laws, using the proved deterministic point-count
continuity theorem and the actual pushforward probability measures. -/
theorem countLaw_tendsto_of_ae_null_frontiers
    (νs : ℕ → ProbabilityMeasure (PointMeasure E)) (ν : ProbabilityMeasure (PointMeasure E))
    (hν : Tendsto νs atTop (𝓝 ν)) {D : Type*} [Fintype D] (A : D → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hfront : ∀ᵐ η : PointMeasure E ∂(ν : Measure (PointMeasure E)),
      ∀ i, ((η : FiniteMeasure E) : Measure E) (frontier (A i)) = 0) :
    Tendsto (fun n ↦ countLaw (νs n) A hA) atTop (𝓝 (countLaw ν A hA)) := by
  apply tendsto_map_discrete_of_ae_continuousAt νs ν hν
    (fun η i ↦ FinitePointMeasureCompact.count η (A i)) (measurable_count_vector A hA)
  exact hfront.mono (fun η hη ↦ tendsto_pi_nhds.mpr
    (fun i ↦ tendsto_count_of_null_frontier tendsto_id (hA i) (hη i)))

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Actual half-open cell-count laws of the genuine graph window
sequence converge to the actual pushforward count law of any genuine
weak point-measure subsequential limit. The model supplies continuity
from its already proved local factorial estimates. -/
theorem unmarked_Ico_countLaw_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Set ℕ) :
    Tendsto (fun m ↦ countLaw (unmarkedWindowLaw M lambda a b R (N m))
      (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))
      (fun _i ↦ (measurable_windowEmbedding a b R)
        (measurableSet_Ico.prod MeasurableSet.of_discrete))) atTop
      (𝓝 (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ T i))
        (fun _i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ico.prod MeasurableSet.of_discrete)))) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply tendsto_map_discrete_of_ae_continuousAt
    (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) ν hν _
    (measurable_count_vector _ (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ico.prod MeasurableSet.of_discrete)))
  exact ae_continuousAt_Ico_count_vector M hM hQP lambda a b ha hab R N hN ν hν lo hi T

theorem unmarked_Ioc_countLaw_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Set ℕ) :
    Tendsto (fun m ↦ countLaw (unmarkedWindowLaw M lambda a b R (N m))
      (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))
      (fun _i ↦ (measurable_windowEmbedding a b R)
        (measurableSet_Ioc.prod MeasurableSet.of_discrete))) atTop
      (𝓝 (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ioc (lo i) (hi i) ×ˢ T i))
        (fun _i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ioc.prod MeasurableSet.of_discrete)))) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply tendsto_map_discrete_of_ae_continuousAt
    (fun m ↦ unmarkedWindowLaw M lambda a b R (N m)) ν hν _
    (measurable_count_vector _ (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_Ioc.prod MeasurableSet.of_discrete)))
  exact ae_continuousAt_Ioc_count_vector M hM hQP lambda a b ha hab R N hN ν hν lo hi T

end PerronWright.PointMeasureCountMapping
