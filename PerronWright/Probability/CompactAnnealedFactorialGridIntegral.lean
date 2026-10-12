import PerronWright.Probability.CompactAnnealedFactorialWindowIntegral
import PerronWright.Probability.CriticalFloorCells

/-! # Exact graph-count interpretation of floor-cell integrals

Each full critical floor cell contributes the actual prescribed-size
factorial expectation. Finite unions of these cells consequently give
literal sums of actual expectations, before any limiting argument.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Topology Classical

noncomputable section

namespace PerronWright.CompactAnnealedFactorialGridIntegral

open CompactAnnealedFactorialLocal CriticalFloorCells

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem localExpectation_eq_on_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ)
    {x : Fin q → ℝ} (hx : x ∈ cell ((n : ℝ)^(2/3 : ℝ)) k) :
    localExpectation M lambda n x r = (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  have he := floor_eq_on_cell (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) k hx
  simp only [localExpectation,CriticalScaling.size,he]

theorem integrableOn_localExpectation_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ) :
    IntegrableOn (fun x ↦ localExpectation M lambda n x r)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  let : IsFiniteMeasure (volume.restrict (cell ((n : ℝ)^(2/3 : ℝ)) k)) :=
    isFiniteMeasure_restrict_cell _ k
  apply (integrable_const ((n : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n)).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  exact (localExpectation_eq_on_cell M lambda hn k r hx).symm

theorem integral_localExpectation_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ) :
    (∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k, localExpectation M lambda n x r) =
      ∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  calc
    _ = ∫ _x in cell ((n : ℝ)^(2/3 : ℝ)) k,
        (n : ℝ)^(2*(q : ℝ)/3) *
          ∫ G, (ComponentCounts.count G k r : ℝ)
            ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun _ hx ↦ localExpectation_eq_on_cell M lambda hn k r hx)
    _ = _ := by
      rw [setIntegral_const,smul_eq_mul,measureReal_def,critical_cell_volume_toReal hn]
      have hp := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn)
        (2*(q : ℝ)/3)).ne'
      field_simp

/-- Every finite prescribed-size collection is exactly represented by
the union of its full half-open floor cells. -/
theorem integral_localExpectation_grid (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (A : Finset (Fin q → ℕ)) (r : Fin q → ℕ) :
    (∫ x in ⋃ k ∈ A, cell ((n : ℝ)^(2/3 : ℝ)) k,
      localExpectation M lambda n x r) =
      ∑ k ∈ A, ∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_localExpectation_cell M lambda hn k r)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_localExpectation_cell M lambda hn k r)

end PerronWright.CompactAnnealedFactorialGridIntegral
