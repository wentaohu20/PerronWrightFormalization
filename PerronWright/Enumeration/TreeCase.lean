import PerronWright.Enumeration.FieldWeight
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open scoped Classical
noncomputable section
namespace PerronWright.CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem connected_zero_surplus_iff_tree {k : ℕ} (hk : 0 < k)
    (H : SimpleGraph (Fin k)) :
    (H.Connected ∧ H.edgeFinset.card = k - 1) ↔ H.IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · rintro ⟨hconn, hcard⟩
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← H.edgeFinset_card, Nat.card_eq_fintype_card]
    simp only [Fintype.card_fin]
    omega
  · rintro ⟨hconn, hcard⟩
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← H.edgeFinset_card, Nat.card_eq_fintype_card] at hcard
    simp only [Fintype.card_fin] at hcard
    omega

theorem connectedWeight_zero_surplus_eq_tree_sum (M : CompactBJRModel S)
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    M.connectedWeight t k 0 =
      ∑ H : SimpleGraph (Fin k), if H.IsTree then M.graphWeight t H else 0 := by
  unfold connectedWeight
  apply Finset.sum_congr rfl
  intro H _
  simp only [add_zero]
  simp only [connected_zero_surplus_iff_tree hk H]

end PerronWright.CompactBJRModel

