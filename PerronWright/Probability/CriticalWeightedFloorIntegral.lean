import PerronWright.Probability.CompactAnnealedFactorialGridIntegral
import PerronWright.Probability.CriticalFloorWindow

/-! # Exact weighted floor-cell sums for actual component expectations -/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology

noncomputable section

namespace PerronWright.CriticalWeightedFloorIntegral

open CriticalFloorCells CompactAnnealedFactorialLocal CompactAnnealedFactorialGridIntegral

def normalizedFloor {q : ℕ} (n : ℕ) (x : Fin q → ℝ) : Fin q → ℝ :=
  fun i ↦ (CriticalScaling.size (x i) n : ℝ)/(n : ℝ)^(2/3 : ℝ)

def normalizedInteger {q : ℕ} (n : ℕ) (k : Fin q → ℕ) : Fin q → ℝ :=
  fun i ↦ (k i : ℝ)/(n : ℝ)^(2/3 : ℝ)

theorem normalizedFloor_eq_on_cell {n q : ℕ} (hn : 0 < n) (k : Fin q → ℕ)
    {x : Fin q → ℝ} (hx : x ∈ cell ((n : ℝ)^(2/3 : ℝ)) k) :
    normalizedFloor n x = normalizedInteger n k := by
  have he := floor_eq_on_cell (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) k hx
  funext i
  simp only [normalizedFloor,normalizedInteger,CriticalScaling.size,congrFun he i]

/-- Any function of the countable integer floor vector is measurable;
no global measurability premise on the weighted test is needed here. -/
theorem measurable_weightedFloor {q : ℕ} (n : ℕ) (F : (Fin q → ℝ) → ℝ) :
    Measurable (fun x : Fin q → ℝ ↦ F (normalizedFloor n x)) := by
  have hk : Measurable (fun x : Fin q → ℝ ↦ fun i ↦ CriticalScaling.size (x i) n) := by
    apply measurable_pi_lambda
    intro i
    exact Nat.measurable_floor.comp ((measurable_pi_apply i).mul_const _)
  exact (measurable_of_countable (fun k : Fin q → ℕ ↦ F (normalizedInteger n k))).comp hk

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem integrableOn_weightedFloor_cell (M : CompactBJRModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ) (F : (Fin q → ℝ) → ℝ) :
    IntegrableOn (fun x ↦ F (normalizedFloor n x) * localExpectation M lambda n x r)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  apply ((integrableOn_localExpectation_cell M lambda hn k r).const_mul
    (F (normalizedInteger n k))).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  rw [normalizedFloor_eq_on_cell hn k hx]

theorem integral_weightedFloor_cell (M : CompactBJRModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ) (F : (Fin q → ℝ) → ℝ) :
    (∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor n x) * localExpectation M lambda n x r) =
        F (normalizedInteger n k) * ∫ G, (ComponentCounts.count G k r : ℝ)
          ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n := by
  calc
    _ = ∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k,
        F (normalizedInteger n k) * localExpectation M lambda n x r :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun x hx ↦ by rw [normalizedFloor_eq_on_cell hn k hx])
    _ = _ := by rw [integral_const_mul,integral_localExpectation_cell M lambda hn k r]

theorem integral_weightedFloor_grid (M : CompactBJRModel S) (lambda : ℝ)
    {n q : ℕ} (hn : 0 < n) (K : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (F : (Fin q → ℝ) → ℝ) :
    (∫ x in ⋃ k ∈ K, cell ((n : ℝ)^(2/3 : ℝ)) k,
      F (normalizedFloor n x) * localExpectation M lambda n x r) =
        ∑ k ∈ K, F (normalizedInteger n k) *
          ∫ G, (ComponentCounts.count G k r : ℝ)
            ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n := by
  rw [integral_biUnion_finset K (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_weightedFloor_cell M lambda hn k r F)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_weightedFloor_cell M lambda hn k r F)

end PerronWright.CriticalWeightedFloorIntegral
