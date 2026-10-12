import PerronWright.Probability.FinitePointMeasureCompact
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Instances.Nat

/-!
# Intrinsic point counts, partition integrals and continuity sets

Partition tests are expressed in the actual integer counts of a point
measure. Actual finite-measure weak convergence gives count-vector
convergence at literal null-frontier continuity sets. No point-process
convergence or count-map continuity is assumed as an interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FinitePointMeasureCounts

open FiniteAtomicPointMeasure FinitePointMeasureCompact

variable {E : Type*} [MeasurableSpace E]

/-- The intrinsic vector of actual integer cell counts. -/
def cellCounts {d : ℕ} (η : PointMeasure E) (p : E → Fin d) : Fin d → ℕ :=
  fun i ↦ count η {z | p z = i}

theorem cellCounts_ofAtomsPoint {n d : ℕ} (x : Fin n → E)
    {p : E → Fin d} (hp : Measurable p) :
    cellCounts (ofAtomsPoint x) p = partitionCounts x p := by
  funext i
  exact count_ofAtomsPoint x (hp (measurableSet_singleton i))

theorem cellCounts_sum {d : ℕ} (η : PointMeasure E)
    {p : E → Fin d} (hp : Measurable p) :
    (∑ i, cellCounts η p i) = size η := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he, cellCounts_ofAtomsPoint x hp, size_ofAtomsPoint, partitionCounts_sum]

/-- Partition integration on the actual point measure, independent of
any chosen atomic representation. -/
theorem integral_partition [MeasurableSingletonClass E] {d : ℕ}
    (η : PointMeasure E) {p : E → Fin d} (hp : Measurable p) (c : Fin d → ℝ) :
    (∫ z, c (p z) ∂((η : FiniteMeasure E) : Measure E)) =
      ∑ i, c i * (cellCounts η p i : ℝ) := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he, ofAtomsPoint_val, cellCounts_ofAtomsPoint x hp]
  exact partition_integral x p c

/-- Uniform finite-partition approximation has an actual error bounded
by `ε` times the actual point count. -/
theorem integral_partition_error [MeasurableSingletonClass E] {d : ℕ}
    (η : PointMeasure E) {p : E → Fin d} (hp : Measurable p)
    (c : Fin d → ℝ) (f : E → ℝ) (ε : ℝ)
    (happrox : ∀ z, |f z - c (p z)| ≤ ε) :
    |(∫ z, f z ∂((η : FiniteMeasure E) : Measure E)) -
      ∑ i, c i * (cellCounts η p i : ℝ)| ≤ (size η : ℝ) * ε := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he, ofAtomsPoint_val, cellCounts_ofAtomsPoint x hp, size_ofAtomsPoint]
  exact partition_integral_error x p c f ε (fun j ↦ happrox (x j))

variable [TopologicalSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E]

/-- Portmanteau at continuity sets for actual finite measures. The
zero-mass case is controlled by the actual total masses; the nonzero
case uses genuine normalized probability measures. -/
theorem tendsto_finiteMeasure_real_of_null_frontier [Nonempty E]
    {J : Type*} {L : Filter J} {μs : J → FiniteMeasure E} {μ : FiniteMeasure E}
    (ht : Tendsto μs L (𝓝 μ)) {A : Set E}
    (hboundary : (μ : Measure E) (frontier A) = 0) :
    Tendsto (fun j ↦ (μs j : Measure E).real A) L (𝓝 ((μ : Measure E).real A)) := by
  by_cases hzero : μ = 0
  · have hm := NNReal.continuous_coe.tendsto μ.mass |>.comp ht.mass
    rw [hzero, FiniteMeasure.zero_mass, NNReal.coe_zero] at hm
    rw [hzero, FiniteMeasure.toMeasure_zero, measureReal_zero_apply]
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hm
    intro j
    exact_mod_cast FiniteMeasure.apply_le_mass (μs j) A
  · have hn := FiniteMeasure.tendsto_normalize_of_tendsto ht hzero
    have hb : μ.normalize (frontier A) = 0 := by
      rw [FiniteMeasure.normalize_eq_of_nonzero μ hzero]
      have hz : μ (frontier A) = 0 :=
        (FiniteMeasure.null_iff_toMeasure_null μ _).mpr hboundary
      simp [hz]
    have ha := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
    have hv := ht.mass.mul ha
    simp only [← FiniteMeasure.self_eq_mass_mul_normalize] at hv
    simpa only [Function.comp_def, FiniteMeasure.measureReal_eq_coe_coeFn] using
      (NNReal.continuous_coe.tendsto (μ A)).comp hv

/-- Actual weak point-measure convergence implies integer count
convergence at every actual null-frontier continuity set. -/
theorem tendsto_count_of_null_frontier [Nonempty E]
    {J : Type*} {L : Filter J} {ηs : J → PointMeasure E} {η : PointMeasure E}
    (ht : Tendsto ηs L (𝓝 η)) {A : Set E} (hA : MeasurableSet A)
    (hboundary : ((η : FiniteMeasure E) : Measure E) (frontier A) = 0) :
    Tendsto (fun j ↦ count (ηs j) A) L (𝓝 (count η A)) := by
  have hf := tendsto_finiteMeasure_real_of_null_frontier
    ((continuous_val.tendsto η).comp ht) hboundary
  simp only [Function.comp_apply, measure_real_eq_count _ hA] at hf
  apply Nat.isClosedEmbedding_coe_real.isEmbedding.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def] using hf

/-- Actual finite count-vector convergence on a family of continuity
sets, with no assumed mapping theorem for count coordinates. -/
theorem tendsto_count_vector_of_null_frontiers [Nonempty E]
    {J : Type*} {L : Filter J} {ηs : J → PointMeasure E} {η : PointMeasure E}
    (ht : Tendsto ηs L (𝓝 η)) {d : ℕ} (A : Fin d → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hboundary : ∀ i, ((η : FiniteMeasure E) : Measure E) (frontier (A i)) = 0) :
    Tendsto (fun j i ↦ count (ηs j) (A i)) L (𝓝 (fun i ↦ count η (A i))) := by
  exact tendsto_pi_nhds.mpr (fun i ↦ tendsto_count_of_null_frontier ht (hA i) (hboundary i))

theorem continuous_count_of_isClopen [Nonempty E] {A : Set E} (hA : IsClopen A) :
    Continuous (fun η : PointMeasure E ↦ count η A) := by
  apply continuous_iff_continuousAt.mpr
  intro η
  exact tendsto_count_of_null_frontier tendsto_id hA.isOpen.measurableSet
    (by rw [hA.frontier_eq]; exact measure_empty)

theorem measurable_count_of_isClopen [Nonempty E] {A : Set E} (hA : IsClopen A) :
    Measurable (fun η : PointMeasure E ↦ count η A) :=
  (continuous_count_of_isClopen hA).measurable

end PerronWright.FinitePointMeasureCounts
