import PerronWright.Enumeration.TreeCase

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright.CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exact weighted vertex-rooted versus edge-rooted dissymmetry at each
positive labelled size. The graph weight is the actual annealed field weight. -/
theorem fieldConnectedWeight_zero_surplus_dissymmetry
    (M : CompactBJRModel S) (g : C(S, ℝ)) {k : ℕ} (hk : 0 < k) :
    M.fieldConnectedWeight g k 0 =
      (∑ H : SimpleGraph (Fin k),
        if H.IsTree then ∑ _v : Fin k, M.fieldGraphWeight g H else 0) -
      (∑ H : SimpleGraph (Fin k),
        if H.IsTree then ∑ _e ∈ H.edgeFinset, M.fieldGraphWeight g H else 0) := by
  classical
  unfold fieldConnectedWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  have htree :
      (H.Connected ∧ H.edgeFinset.card = k + 0 - 1) ↔ H.IsTree := by
    simpa only [add_zero] using connected_zero_surplus_iff_tree hk H
  by_cases ht : H.IsTree
  · have he : H.edgeFinset.card = k - 1 :=
      (connected_zero_surplus_iff_tree hk H).mpr ht |>.2
    rw [if_pos (htree.mpr ht), if_pos ht, if_pos ht]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      he, nsmul_eq_mul]
    rw [Nat.cast_sub (show 1 ≤ k from hk)]
    ring
  · simp only [ht, htree.not.mpr ht, ↓reduceIte, sub_zero]

end PerronWright.CompactBJRModel
