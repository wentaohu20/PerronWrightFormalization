import PerronWright.Probability.WindowCountGenerators
import PerronWright.Probability.PointMeasureCountMapping
import PerronWright.Probability.FiniteIrreducibleWindowBoundary
import PerronWright.Probability.FiniteIrreducibleOverlappingCellCountLaw

/-!
# A unique genuine weak limit of the unmarked compact-window point laws

The source laws are the actual finite sampled-graph component measures.
Their proved tightness supplies an actual point-law subsequential limit.
The proved boundary estimates and actual count pushforward theorem pass
finite rational cell-count laws to every such limit. The proved finite
query count-law limits identify all of those finite laws, and the
literal countable generating family identifies the whole point law.
This theorem does not identify a Brownian law or assert a local-vague
process limit.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleWindowPointLawLimit

open FinitePointMeasureCompact FinitePointMeasureMeasurable
open ComponentWindowPointMeasures ComponentWindowMixedFactorials
open FiniteIrreducibleComponentProcess FiniteIrreducibleCellFactorialCounts
open FiniteIrreducibleWindowBoundary FiniteIrreducibleWindowCountLaw
open PointMeasureCountMapping WindowCountGenerators

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem ae_generator_cell_frontier_eq_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m) (v (N m))) atTop (𝓝 ν))
    (i : Index R) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (cell a b R i)) = 0 := by
  cases i with
  | none => simp
  | some i => cases i with
    | none => simp
    | some x =>
      simpa only [cell, sizeCell, surplusCell, Finset.coe_singleton] using
        ae_sizeSurplusCell_frontier_eq_zero M hM lambda a b ha hab R v E hE hround N hN ν hν
          (Set.Iic (x.1 : ℝ)) ({x.2.val} : Set ℕ) x.1 x.1 (by simp)

theorem generator_finiteCountLaw_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m) (v (N m))) atTop (𝓝 ν))
    (I : Finset (Index R)) :
    Tendsto (fun m ↦ countLaw (unmarkedWindowLaw M lambda a b R (N m) (v (N m)))
      (fun i : I ↦ cell a b R i.val) (fun i ↦ measurableSet_cell a b R i.val)) atTop
      (𝓝 (countLaw ν (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply countLaw_tendsto_of_ae_null_frontiers _ ν hν _ _
  exact ae_all_iff.mpr (fun i : I ↦
    ae_generator_cell_frontier_eq_zero M hM lambda a b ha hab R v E hE hround N hN ν hν i.val)

/-- Different genuine weak subsequential point-law limits are ruled
out by the actual finite query count-law limits and the proved rational
generating family. No target point-law identification is assumed. -/
theorem subsequential_limits_eq (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E)
    (N P : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hP : Tendsto P atTop atTop)
    (ν ρ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (N m) (v (N m))) atTop (𝓝 ν))
    (hρ : Tendsto (fun m ↦ unmarkedWindowLaw M lambda a b R (P m) (v (P m))) atTop (𝓝 ρ)) :
    ν = ρ := by
  apply probabilityMeasure_eq_of_finite_cell_countLaws a b R hab ν ρ
  intro I
  let J : I → Set ℝ := fun i ↦ sizeCell R i.val
  let T : I → Finset ℕ := fun i ↦ surplusCell R i.val
  have hJ : ∀ i, MeasurableSet (J i) := fun i ↦ measurableSet_sizeCell R i.val
  have hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0 :=
    fun i ↦ volume_frontier_sizeCell R i.val
  obtain ⟨θ, hθ, _⟩ :=
    FiniteIrreducibleOverlappingCellCountLaw.exists_unique_actual_overlappingCellCountLaw_limit
      M hM lambda a b ha hab R J T hJ hJf v E hE hround
  have hνcount : Tendsto (fun m ↦ FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R (N m) (v (N m)) J T hJ)
      atTop (𝓝 (countLaw ν (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
    simpa only [FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw, sizeSurplusCells, cell, J, T] using
      generator_finiteCountLaw_tendsto M hM lambda a b ha hab R v E hE hround N hN ν hν I
  have hρcount : Tendsto (fun m ↦ FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw M lambda a b R (P m) (v (P m)) J T hJ)
      atTop (𝓝 (countLaw ρ (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
    simpa only [FiniteIrreducibleCellFactorialCounts.sizeSurplusCountLaw, sizeSurplusCells, cell, J, T] using
      generator_finiteCountLaw_tendsto M hM lambda a b ha hab R v E hE hround P hP ρ hρ I
  exact (tendsto_nhds_unique (hθ.comp hN) hνcount).symm.trans
    (tendsto_nhds_unique (hθ.comp hP) hρcount)

/-- There exists a unique genuine probability measure on the actual
weak-Borel compact-window integer point-measure space to which the
entire actual unmarked graph-component law sequence converges weakly.
Only literal finite irreducible criticality and the actual O(1) counts are used. -/
theorem exists_unique_unmarkedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) atTop (𝓝 ν) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hc := isCompact_closure_unmarkedWindowLaws M hM lambda a b ha hab R v E hE hround
  obtain ⟨ν, _, N, hN, hν⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  have hfull : Tendsto (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) atTop (𝓝 ν) := by
    apply hc.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall (fun n ↦ subset_closure (Set.mem_range_self n)))
    intro ρ _ hcluster
    obtain ⟨P, hP, hρ⟩ := hcluster.tendsto_subseq
    exact subsequential_limits_eq M hM lambda a b ha hab R v E hE hround P N
      hP.tendsto_atTop hN.tendsto_atTop ρ ν hρ hν
  exact ⟨ν, hfull, fun ρ hρ ↦ tendsto_nhds_unique hρ hfull⟩

end PerronWright.FiniteIrreducibleWindowPointLawLimit

