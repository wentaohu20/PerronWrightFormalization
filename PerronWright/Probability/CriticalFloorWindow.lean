import PerronWright.Probability.CriticalFloorCells
import PerronWright.Probability.FactorialWindowMass
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Pi

/-! # Actual integer windows and their critical floor cells -/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Classical Topology

noncomputable section

namespace PerronWright.CriticalFloorWindow

open CriticalFloorCells FactorialDensity

def indices (q : ℕ) (h a b : ℝ) : Finset (Fin q → ℕ) :=
  Fintype.piFinset (fun _ : Fin q ↦ Finset.Icc ⌈a*h⌉₊ ⌊b*h⌋₊)

def grid (q : ℕ) (h a b : ℝ) : Set (Fin q → ℝ) :=
  ⋃ k ∈ indices q h a b, cell h k

theorem mem_indices {q : ℕ} {h a b : ℝ} (hh : 0 < h) (hb : 0 ≤ b)
    {k : Fin q → ℕ} : k ∈ indices q h a b ↔
      ∀ i, (k i : ℝ)/h ∈ Set.Icc a b := by
  simp only [indices,Fintype.mem_piFinset,Finset.mem_Icc,Nat.ceil_le]
  have hb' : 0 ≤ b*h := mul_nonneg hb hh.le
  simp_rw [Nat.le_floor_iff hb']
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨(le_div_iff₀ hh).mpr ha,(div_le_iff₀ hh).mpr hb⟩
  · intro hk
    exact ⟨(le_div_iff₀ hh).mp hk.1,(div_le_iff₀ hh).mp hk.2⟩

theorem mem_grid {q : ℕ} {h a b : ℝ} (hh : 0 < h) (hb : 0 ≤ b)
    {x : Fin q → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x ∈ grid q h a b ↔
      (fun i ↦ (⌊x i*h⌋₊ : ℝ)/h) ∈ sizeWindow q a b := by
  simp only [grid,Set.mem_iUnion]
  constructor
  · rintro ⟨k,hk,hxk⟩
    have he := floor_eq_on_cell hh k hxk
    apply mem_sizeWindow.mpr
    intro i
    simpa only [congrFun he i] using ((mem_indices hh hb).mp hk i)
  · intro hxw
    refine ⟨fun i ↦ ⌊x i*h⌋₊,(mem_indices hh hb).mpr (mem_sizeWindow.mp hxw),?_⟩
    apply mem_cell.mpr
    intro i
    exact ⟨(div_le_iff₀ hh).mpr (Nat.floor_le (mul_nonneg (hx i) hh.le)),
      (lt_div_iff₀ hh).mpr (Nat.lt_floor_add_one _)⟩

theorem measurableSet_grid (q : ℕ) (h a b : ℝ) : MeasurableSet (grid q h a b) :=
  (indices q h a b).measurableSet_biUnion (fun k _ ↦ measurableSet_cell h k)

theorem grid_subset_expanded {q : ℕ} {h a b : ℝ} (hh : 0 < h)
    (ha : 0 < a) (hb : 0 ≤ b) (hsmall : 1/h ≤ 1) :
    grid q h a b ⊆ sizeWindow q (a/2) (b+1) := by
  intro x hx
  obtain ⟨k,hk,hxk⟩ := (show ∃ k ∈ indices q h a b, x ∈ cell h k by simpa [grid] using hx)
  apply mem_sizeWindow.mpr
  have hki := (mem_indices hh hb).mp hk
  have hxi := mem_cell.mp hxk
  intro i
  have he : ((k i : ℝ)+1)/h = (k i : ℝ)/h + 1/h := by ring
  constructor
  · exact (by linarith : a/2 ≤ a).trans ((hki i).1.trans (hxi i).1)
  · have hi := (hxi i).2
    rw [he] at hi
    linarith [(hki i).2]

theorem critical_grid_indicator_eventually {q : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {x : Fin q → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hboundary : (x ∈ Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) ↔ x ∈ sizeWindow q a b) :
    ∀ᶠ n : ℕ in atTop,
      (x ∈ grid q ((n : ℝ)^(2/3 : ℝ)) a b) ↔ x ∈ sizeWindow q a b := by
  have ht : Tendsto (fun n : ℕ ↦ fun i ↦
      (CriticalScaling.size (x i) n : ℝ)/(n : ℝ)^(2/3 : ℝ)) atTop (𝓝 x) :=
    tendsto_pi_nhds.mpr (fun i ↦ CriticalScaling.size_normalized_tendsto (hx i))
  by_cases hw : x ∈ sizeWindow q a b
  · have ho : x ∈ Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b) := hboundary.mpr hw
    have hopen : IsOpen (Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) :=
      isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)
    filter_upwards [eventually_ge_atTop 1,ht.eventually (hopen.mem_nhds ho)] with n hn hxn
    have hm : (fun i ↦ (CriticalScaling.size (x i) n : ℝ)/(n : ℝ)^(2/3 : ℝ)) ∈
        sizeWindow q a b := mem_sizeWindow.mpr (fun i ↦
          ⟨((Set.mem_pi.mp hxn) i (Set.mem_univ i)).1.le,
            ((Set.mem_pi.mp hxn) i (Set.mem_univ i)).2.le⟩)
    exact iff_of_true ((mem_grid (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega : 0 < n)) _)
      (ha.le.trans hab) hx).mpr hm) hw
  · have ho : x ∈ (sizeWindow q a b)ᶜ := hw
    filter_upwards [eventually_ge_atTop 1,ht.eventually (isClosed_Icc.isOpen_compl.mem_nhds ho)]
      with n hn hxn
    have hg : x ∉ grid q ((n : ℝ)^(2/3 : ℝ)) a b := by
      intro hg
      exact hxn ((mem_grid (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega : 0 < n)) _)
        (ha.le.trans hab) hx).mp hg)
    exact iff_of_false hg hw

end PerronWright.CriticalFloorWindow
