import PerronWright.Probability.GraphWindowCellFactorials
import PerronWright.Probability.GraphWindowBoundary
import PerronWright.Probability.WindowCountGenerators
import PerronWright.Probability.PointMeasureCountMapping

/-! # Genuine full-sequence spatial window limits of actual graph laws

Actual graph-law tightness constructs weak subsequential point laws.
Proved null boundaries pass rational finite cell counts to each limit;
proved joint cell laws and the generating family identify them. This is
a full spatial limit, not just a total-component count limit. Brownian
identification is a separate still-required theorem.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1800000

namespace PerronWright.GraphWindowSpatialLimit

open GraphWindowSource GraphWindowFactorialLimits GraphWindowCellFactorials GraphWindowBoundary
open FinitePointMeasureCompact FinitePointMeasureMeasurable
  ComponentWindowPointMeasures ComponentWindowMixedFactorials
  PointMeasureCountMapping WindowCountGenerators

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

theorem ae_generator_cell_frontier_eq_zero {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν)) (i : Index R) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R) ∂(ν : Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (cell a b R i)) = 0 := by
  cases i with
  | none => simp
  | some i => cases i with
    | none => simp
    | some x =>
      simpa only [cell, sizeCell, surplusCell, Finset.coe_singleton] using
        ae_sizeSurplusCell_frontier_eq_zero ρ hbeta hlocal a b ha hab R N hN ν hν
          (Set.Iic (x.1 : ℝ)) ({x.2.val} : Set ℕ) x.1 x.1 (by simp)

theorem generator_finiteCountLaw_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν)) (I : Finset (Index R)) :
    Tendsto (fun m ↦ countLaw (windowLaw ρ a b R (N m))
      (fun i : I ↦ cell a b R i.val) (fun i ↦ measurableSet_cell a b R i.val)) atTop
      (𝓝 (countLaw ν (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply countLaw_tendsto_of_ae_null_frontiers _ ν hν _ _
  exact ae_all_iff.mpr (fun i : I ↦
    ae_generator_cell_frontier_eq_zero ρ hbeta hlocal ha hab R N hN ν hν i.val)

theorem subsequential_limits_eq {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (N P : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hP : Tendsto P atTop atTop)
    (ν μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hν : Tendsto (fun m ↦ windowLaw ρ a b R (N m)) atTop (𝓝 ν))
    (hμ : Tendsto (fun m ↦ windowLaw ρ a b R (P m)) atTop (𝓝 μ)) : ν = μ := by
  apply probabilityMeasure_eq_of_finite_cell_countLaws a b R hab ν μ
  intro I
  let J : I → Set ℝ := fun i ↦ sizeCell R i.val
  let T : I → Finset ℕ := fun i ↦ surplusCell R i.val
  have hJ : ∀ i, MeasurableSet (J i) := fun i ↦ measurableSet_sizeCell R i.val
  have hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0 :=
    fun i ↦ volume_frontier_sizeCell R i.val
  obtain ⟨θ, hθ, _⟩ := exists_unique_actual_overlappingCellCountLaw_limit
    ρ hbeta hlocal ha hab R J T hJ hJf
  have hνcount : Tendsto (fun m ↦ GraphWindowCellFactorials.sizeSurplusCountLaw ρ a b R (N m) J T hJ)
      atTop (𝓝 (countLaw ν (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
    simpa only [GraphWindowCellFactorials.sizeSurplusCountLaw, sizeSurplusCells, cell, J, T] using
      generator_finiteCountLaw_tendsto ρ hbeta hlocal ha hab R N hN ν hν I
  have hμcount : Tendsto (fun m ↦ GraphWindowCellFactorials.sizeSurplusCountLaw ρ a b R (P m) J T hJ)
      atTop (𝓝 (countLaw μ (fun i : I ↦ cell a b R i.val)
        (fun i ↦ measurableSet_cell a b R i.val))) := by
    simpa only [GraphWindowCellFactorials.sizeSurplusCountLaw, sizeSurplusCells, cell, J, T] using
      generator_finiteCountLaw_tendsto ρ hbeta hlocal ha hab R P hP μ hμ I
  exact (tendsto_nhds_unique (hθ.comp hN) hνcount).symm.trans
    (tendsto_nhds_unique (hθ.comp hP) hμcount)

theorem exists_unique_windowLaw_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw ρ a b R) atTop (𝓝 ν) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hc := isCompact_closure_windowLaws ρ hbeta hlocal ha hab R
  obtain ⟨ν, _, N, hN, hν⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  have hfull : Tendsto (windowLaw ρ a b R) atTop (𝓝 ν) := by
    apply hc.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall (fun n ↦ subset_closure (Set.mem_range_self n)))
    intro μ _ hcluster
    obtain ⟨P, hP, hμ⟩ := hcluster.tendsto_subseq
    exact subsequential_limits_eq ρ hbeta hlocal ha hab R P N
      hP.tendsto_atTop hN.tendsto_atTop μ ν hμ hν
  exact ⟨ν, hfull, fun μ hμ ↦ tendsto_nhds_unique hμ hfull⟩

end PerronWright.GraphWindowSpatialLimit
