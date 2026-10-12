import PerronWright.Probability.CriticalScaling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor

/-! # Exact cells of the critical floor discretization

Positive integer size tuples have literal half-open rectangular fibers.
Their cell volume is the exact reciprocal scaling factor, not an
asymptotic Riemann-sum premise.
-/

open MeasureTheory Set
open scoped Real BigOperators Classical

noncomputable section

namespace PerronWright.CriticalFloorCells

def cell {q : ℕ} (h : ℝ) (k : Fin q → ℕ) : Set (Fin q → ℝ) :=
  Set.univ.pi (fun i ↦ Set.Ico ((k i : ℝ)/h) (((k i : ℝ)+1)/h))

theorem mem_cell {q : ℕ} {h : ℝ} {k : Fin q → ℕ} {x : Fin q → ℝ} :
    x ∈ cell h k ↔ ∀ i, (k i : ℝ)/h ≤ x i ∧ x i < ((k i : ℝ)+1)/h := by
  simp only [cell, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_const]

theorem floor_fiber_eq_cell {q : ℕ} {h : ℝ} (hh : 0 < h)
    (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    {x : Fin q → ℝ | (fun i ↦ ⌊x i*h⌋₊) = k} = cell h k := by
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff, mem_cell]
  apply forall_congr'
  intro i
  rw [Nat.floor_eq_iff' (Nat.ne_of_gt (hk i)), div_le_iff₀ hh, lt_div_iff₀ hh]

theorem floor_eq_on_cell {q : ℕ} {h : ℝ} (hh : 0 < h)
    (k : Fin q → ℕ) {x : Fin q → ℝ} (hx : x ∈ cell h k) :
    (fun i ↦ ⌊x i*h⌋₊) = k := by
  ext i
  have hxi := mem_cell.mp hx i
  apply Nat.floor_eq_iff (a := x i*h) (by
    have hkn : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
    exact hkn.trans ((div_le_iff₀ hh).mp hxi.1)) |>.mpr
  exact ⟨(div_le_iff₀ hh).mp hxi.1,(lt_div_iff₀ hh).mp hxi.2⟩

theorem measurableSet_cell {q : ℕ} (h : ℝ) (k : Fin q → ℕ) :
    MeasurableSet (cell h k) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ico)

theorem disjoint_cells {q : ℕ} {h : ℝ} (hh : 0 < h)
    {k l : Fin q → ℕ} (hkl : k ≠ l) : Disjoint (cell h k) (cell h l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  exact hkl ((floor_eq_on_cell hh k hxk).symm.trans (floor_eq_on_cell hh l hxl))

theorem isFiniteMeasure_restrict_cell {q : ℕ} (h : ℝ) (k : Fin q → ℕ) :
    IsFiniteMeasure (volume.restrict (cell h k)) := by
  apply isFiniteMeasure_restrict.mpr
  rw [cell,Real.volume_pi_Ico]
  exact ENNReal.prod_ne_top (fun _ _ ↦ ENNReal.ofReal_ne_top)

theorem cell_volume_toReal {q : ℕ} {h : ℝ} (hh : 0 < h) (k : Fin q → ℕ) :
    (volume (cell h k)).toReal = (1/h)^q := by
  have hle : (fun i : Fin q ↦ (k i : ℝ)/h) ≤ fun i ↦ ((k i : ℝ)+1)/h := by
    intro i
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  rw [cell,Real.volume_pi_Ico_toReal hle]
  have hd (i : Fin q) : ((k i : ℝ)+1)/h - (k i : ℝ)/h = 1/h := by ring
  simp only [hd,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem critical_cell_volume_toReal {n q : ℕ} (hn : 0 < n) (k : Fin q → ℕ) :
    (volume (cell ((n : ℝ)^(2/3 : ℝ)) k)).toReal =
      1/(n : ℝ)^(2*(q : ℝ)/3) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [cell_volume_toReal (Real.rpow_pos_of_pos hnR _), div_pow, one_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
  congr 1
  ring

end PerronWright.CriticalFloorCells
