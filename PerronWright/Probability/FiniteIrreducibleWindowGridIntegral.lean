import PerronWright.Probability.FiniteIrreducibleWindowExpectation
import PerronWright.Probability.CriticalFloorCells

/-! # Exact deterministic factorial expectations from full floor cells -/

open MeasureTheory Filter Topology
open scoped Real BigOperators Topology Classical
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleWindowGridIntegral

open FiniteIrreducibleWindowExpectation FiniteIrreducibleComponentProcess CriticalFloorCells

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem localExpectation_eq_on_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ)
    {x : Fin q → ℝ} (hx : x ∈ cell ((n : ℝ)^(2/3 : ℝ)) k) :
    localExpectation M lambda n x0 x r = (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0 := by
  have he := floor_eq_on_cell (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) k hx
  simp only [localExpectation, FiniteIrreducibleLocalMainIdentity.scaledFactorialExpectation,
    CriticalScaling.size, he, graphLaw]

theorem integrableOn_localExpectation_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ) :
    IntegrableOn (fun x ↦ localExpectation M lambda n x0 x r)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  let : IsFiniteMeasure (volume.restrict (cell ((n : ℝ)^(2/3 : ℝ)) k)) :=
    isFiniteMeasure_restrict_cell _ k
  apply (integrable_const ((n : ℝ)^(2*(q : ℝ)/3) *
    ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0)).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  exact (localExpectation_eq_on_cell M lambda hn x0 k r hx).symm

theorem integral_localExpectation_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ) :
    (∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k, localExpectation M lambda n x0 x r) =
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0 := by
  calc
    _ = ∫ _x in cell ((n : ℝ)^(2/3 : ℝ)) k,
        (n : ℝ)^(2*(q : ℝ)/3) *
          ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0 :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun _ hx ↦ localExpectation_eq_on_cell M lambda hn x0 k r hx)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, critical_cell_volume_toReal hn]
      have hp := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (2*(q : ℝ)/3)).ne'
      field_simp

theorem integral_localExpectation_grid (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S)
    (A : Finset (Fin q → ℕ)) (r : Fin q → ℕ) :
    (∫ x in ⋃ k ∈ A, cell ((n : ℝ)^(2/3 : ℝ)) k, localExpectation M lambda n x0 x r) =
      ∑ k ∈ A, ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x0 := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_localExpectation_cell M lambda hn x0 k r)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_localExpectation_cell M lambda hn x0 k r)

end PerronWright.FiniteIrreducibleWindowGridIntegral
