import PerronWright.Probability.FiniteIrreducibleWindowGridIntegral
import PerronWright.Probability.CriticalWeightedFloorIntegral

/-! # Exact weighted full floor cells for the fixed-type graph law

Only the pure floor geometry is reused from the compact files.
The measure in all three identities is the actual fixed assignment law.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section

namespace PerronWright.FiniteIrreducibleWeightedFloorIntegral

open CriticalFloorCells CriticalWeightedFloorIntegral
open FiniteIrreducibleWindowExpectation FiniteIrreducibleWindowGridIntegral
  FiniteIrreducibleComponentProcess

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem integrableOn_weightedFloor_cell (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ) (F : (Fin q → ℝ) → ℝ) :
    IntegrableOn (fun x ↦ F (normalizedFloor n x) * localExpectation M lambda n x0 x r)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  apply ((integrableOn_localExpectation_cell M lambda hn x0 k r).const_mul
    (F (normalizedInteger n k))).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  rw [normalizedFloor_eq_on_cell hn k hx]

theorem integral_weightedFloor_cell (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ) (F : (Fin q → ℝ) → ℝ) :
    (∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor n x) * localExpectation M lambda n x0 x r) =
        F (normalizedInteger n k) * ∫ G, (ComponentCounts.count G k r : ℝ)
          ∂graphLaw M lambda n x0 := by
  calc
    _ = ∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k,
        F (normalizedInteger n k) * localExpectation M lambda n x0 x r :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun x hx ↦ by rw [normalizedFloor_eq_on_cell hn k hx])
    _ = _ := by rw [integral_const_mul,integral_localExpectation_cell M lambda hn x0 k r]

theorem integral_weightedFloor_grid (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (F : (Fin q → ℝ) → ℝ) :
    (∫ x in ⋃ k ∈ K, cell ((n : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor n x) * localExpectation M lambda n x0 x r) =
        ∑ k ∈ K, F (normalizedInteger n k) *
          ∫ G, (ComponentCounts.count G k r : ℝ)
            ∂graphLaw M lambda n x0 := by
  rw [integral_biUnion_finset K (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_weightedFloor_cell M lambda hn x0 k r F)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_weightedFloor_cell M lambda hn x0 k r F)

end PerronWright.FiniteIrreducibleWeightedFloorIntegral

