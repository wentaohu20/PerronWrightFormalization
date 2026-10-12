import PerronWright.Probability.GraphWindowSpatialLimit

/-! # Literal density moments of actual graph spatial window limits

Boundary nullity and actual joint cell-law convergence identify the
mixed factorial moments of the genuine spatial weak limit. These are
properties of the constructed limit, not moment-identification inputs.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowDensityMoments

open GraphWindowSource GraphWindowFactorialLimits GraphWindowSpatialLimit
  GraphWindowCellFactorials GraphWindowBoundary
open ComponentWindowPointMeasures ComponentWindowMixedFactorials
  FinitePointMeasureCompact FinitePointMeasureMeasurable FactorialCountDeterminacy
  PointMeasureCountMapping
open CompactSizeCellFactorialLimits (cellMomentMass)

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

theorem interval_cell_factorials_of_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (windowLaw ρ a b R) atTop (𝓝 ν))
    {d : ℕ} (lo hi : Fin d → ℝ) (T : Fin d → Finset ℕ)
    (hdis : Pairwise (fun i j ↦ Disjoint
      (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T i)
      (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T j))) :
    (∀ q, Integrable (factorialPolynomial q)
      (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
        (fun i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ))) ∧
    (∀ q, factorialMoment
      (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
        (fun i ↦ (measurable_windowEmbedding a b R)
          (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ)) q =
        cellMomentMass alpha beta lambda a b R (fun i ↦ Set.Ico (lo i) (hi i)) T q) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a,le_rfl,hab⟩,⟨0,by omega⟩)⟩
  let J : Fin d → Set ℝ := fun i ↦ Set.Ico (lo i) (hi i)
  have hJ : ∀ i, MeasurableSet (J i) := fun _ ↦ measurableSet_Ico
  have hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0 :=
    fun i ↦ SizeCellIndicators.volume_frontier_Ico (lo i) (hi i)
  let A : Fin d → Set (SurplusWindow a b R) :=
    fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J T i
  have hA : ∀ i, MeasurableSet (A i) :=
    fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J T hJ i)
  have hfront : ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ∀ i, ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (A i)) = 0 :=
    ae_all_iff.mpr (fun i ↦ ae_Ico_cell_frontier_eq_zero ρ hbeta hlocal a b ha hab R
      id tendsto_id ν hν (lo i) (hi i) (T i : Set ℕ))
  have hmap := countLaw_tendsto_of_ae_null_frontiers
    (windowLaw ρ a b R) ν hν A hA hfront
  obtain ⟨μ,hμ,_⟩ := exists_unique_actual_jointCellCountLaw_limit ρ hbeta hlocal ha hab R
    J T hJ hJf hdis
  have ht : Tendsto (fun n ↦ countLaw (windowLaw ρ a b R n) A hA)
      atTop (𝓝 μ) := hμ.2.2
  have he : countLaw ν A hA = μ := tendsto_nhds_unique hmap ht
  change (∀ q, Integrable (factorialPolynomial q) (countLaw ν A hA : Measure (Fin d → ℕ))) ∧
    (∀ q, factorialMoment (countLaw ν A hA : Measure (Fin d → ℕ)) q =
      cellMomentMass alpha beta lambda a b R J T q)
  rw [he]
  exact ⟨hμ.1,hμ.2.1⟩

theorem exists_actual_window_limit_with_all_interval_factorials {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw ρ a b R) atTop (𝓝 ν) ∧
      ∀ (d : ℕ) (lo hi : Fin d → ℝ) (T : Fin d → Finset ℕ),
        Pairwise (fun i j ↦ Disjoint
          (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T i)
          (sizeSurplusCells (fun i ↦ Set.Ico (lo i) (hi i)) T j)) →
        (∀ q, Integrable (factorialPolynomial q)
          (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
            (fun i ↦ (measurable_windowEmbedding a b R)
              (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ))) ∧
        (∀ q, factorialMoment
          (countLaw ν (fun i ↦ windowEmbedding a b R ⁻¹' (Set.Ico (lo i) (hi i) ×ˢ (T i : Set ℕ)))
            (fun i ↦ (measurable_windowEmbedding a b R)
              (measurableSet_Ico.prod (T i).measurableSet)) : Measure (Fin d → ℕ)) q =
            cellMomentMass alpha beta lambda a b R (fun i ↦ Set.Ico (lo i) (hi i)) T q) := by
  obtain ⟨ν,hν,_⟩ := exists_unique_windowLaw_limit ρ hbeta hlocal ha hab R
  refine ⟨ν,hν,?_⟩
  intro d lo hi T hdis
  exact interval_cell_factorials_of_limit ρ hbeta hlocal ha hab R ν hν lo hi T hdis

end PerronWright.GraphWindowDensityMoments
