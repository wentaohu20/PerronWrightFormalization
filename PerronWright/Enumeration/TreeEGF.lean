import PerronWright.Enumeration.TreeDissymmetry
import Mathlib.RingTheory.PowerSeries.Derivative


open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright.CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Actual finite vertex-rooted tree sum, with the same annealed weights. -/
def vertexRootedTreeWeight (M : CompactBJRModel S) (g : C(S, ℝ)) (k : ℕ) : ℝ :=
  ∑ H : SimpleGraph (Fin k),
    if H.IsTree then ∑ _v : Fin k, M.fieldGraphWeight g H else 0

/-- Actual finite edge-rooted tree sum, with the same annealed weights. -/
def edgeRootedTreeWeight (M : CompactBJRModel S) (g : C(S, ℝ)) (k : ℕ) : ℝ :=
  ∑ H : SimpleGraph (Fin k),
    if H.IsTree then ∑ _e ∈ H.edgeFinset, M.fieldGraphWeight g H else 0

theorem fieldConnectedWeight_zero_surplus_eq_vertex_sub_edge
    (M : CompactBJRModel S) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) :
    M.fieldConnectedWeight g k 0 =
      M.vertexRootedTreeWeight g k - M.edgeRootedTreeWeight g k :=
  M.fieldConnectedWeight_zero_surplus_dissymmetry g hk

theorem vertexRootedTreeWeight_eq_card_mul
    (M : CompactBJRModel S) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) :
    M.vertexRootedTreeWeight g k =
      (k : ℝ) * M.fieldConnectedWeight g k 0 := by
  classical
  unfold vertexRootedTreeWeight fieldConnectedWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  have htree :
      (H.Connected ∧ H.edgeFinset.card = k + 0 - 1) ↔ H.IsTree := by
    simpa only [add_zero] using connected_zero_surplus_iff_tree hk H
  by_cases ht : H.IsTree
  · rw [if_pos ht, if_pos (htree.mpr ht)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  · rw [if_neg ht, if_neg (htree.not.mpr ht)]
    ring

/-- Formal exponential generating function of the actual tree weights. -/
def treeEGF (M : CompactBJRModel S) (g : C(S, ℝ)) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else
    M.fieldConnectedWeight g k 0 / (Nat.factorial k : ℝ))

/-- Formal EGF for trees with one distinguished labelled vertex. -/
def vertexRootedTreeEGF (M : CompactBJRModel S) (g : C(S, ℝ)) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else
    M.vertexRootedTreeWeight g k / (Nat.factorial k : ℝ))

/-- Formal EGF for trees with one distinguished edge. -/
def edgeRootedTreeEGF (M : CompactBJRModel S) (g : C(S, ℝ)) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else
    M.edgeRootedTreeWeight g k / (Nat.factorial k : ℝ))

theorem treeEGF_eq_vertex_sub_edge (M : CompactBJRModel S) (g : C(S, ℝ)) :
    M.treeEGF g = M.vertexRootedTreeEGF g - M.edgeRootedTreeEGF g := by
  ext k
  rw [map_sub]
  simp only [treeEGF, vertexRootedTreeEGF, edgeRootedTreeEGF,
    PowerSeries.coeff_mk]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    rw [M.fieldConnectedWeight_zero_surplus_eq_vertex_sub_edge g
      (Nat.pos_of_ne_zero hk)]
    ring

theorem vertexRootedTreeEGF_eq_X_derivative (M : CompactBJRModel S)
    (g : C(S, ℝ)) :
    M.vertexRootedTreeEGF g =
      PowerSeries.X * PowerSeries.derivative ℝ (M.treeEGF g) := by
  ext k
  cases k with
  | zero => simp [vertexRootedTreeEGF, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [vertexRootedTreeEGF, treeEGF, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ↓reduceIte]
    rw [M.vertexRootedTreeWeight_eq_card_mul g (Nat.zero_lt_succ n)]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    ring

end PerronWright.CompactBJRModel
