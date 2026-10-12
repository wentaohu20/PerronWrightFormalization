import PerronWright.Enumeration.KernelLengthRegroup

/-!
# Literal marked path factors

This stage isolates the only analytic object needed for decorated suppressed
edges.  Length zero is a direct edge; positive length integrates the actual
path graph with one supplied continuous mark at every internal vertex.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Literal path contribution with one already-pruned continuous mark on
each internal core vertex. -/
def markedPathFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) :
    (n : ℕ) → (Fin n → C(S, ℝ)) → S → S → ℝ
  | 0, _, a, b => t * M.kernel a b
  | n + 1, marks, a, b =>
      ∫ x : Fin (n + 1) → S,
        (∏ i : Fin (n + 1), marks i (x i)) *
          interiorPathObservable M t n a b x
        ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)

/-- Removing all attached-tree marks recovers the previously formalized
path kernel exactly, including the direct-edge case. -/
theorem markedPathFactor_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (a b : S) :
    markedPathFactor M t n (fun _ => 1) a b =
      pathKernel M t n (a, b) := by
  cases n with
  | zero => rfl
  | succ n =>
      change
        (∫ x : Fin (n + 1) → S,
          (∏ i : Fin (n + 1), (1 : C(S, ℝ)) (x i)) *
            interiorPathObservable M t n a b x
          ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) = _
      simp only [ContinuousMap.one_apply, Finset.prod_const_one, one_mul]
      exact interiorPathGraphWeight_eq_pathKernel M t (n + 1) a b

/-- Reversing the Hamilton order, ordered internal marks, and endpoints
simultaneously leaves the contribution unchanged.  Thus the orientation
needed to store path marks is auxiliary rather than analytic data. -/
theorem markedPathFactor_reverse
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    (marks : Fin n → C(S, ℝ)) (a b : S) :
    markedPathFactor M t n marks a b =
      markedPathFactor M t n (fun i => marks i.rev) b a := by
  cases n with
  | zero =>
      change t * M.kernel a b = t * M.kernel b a
      rw [M.kernel.symmetric a b]
  | succ n =>
      let F : C((Fin (n + 1) → S), ℝ) := ⟨fun x =>
        (∏ i : Fin (n + 1), marks i (x i)) *
          interiorPathObservable M t n a b x, by fun_prop⟩
      change (∫ x : Fin (n + 1) → S, F x
          ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) = _
      calc
        _ = ∫ x : Fin (n + 1) → S, F (fun i => x i.rev)
            ∂Measure.pi (fun _ : Fin (n + 1) => M.mu) :=
          (integral_pathObservable_rev M n F).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with x
          have hprod :
              (∏ i : Fin (n + 1), marks i (x i.rev)) =
                ∏ i : Fin (n + 1), marks i.rev (x i) := by
            exact Fintype.prod_equiv (Fin.revPerm (n := n + 1))
              (fun i : Fin (n + 1) => marks i (x i.rev))
              (fun i : Fin (n + 1) => marks i.rev (x i))
              (fun i => by simp)
          change
            (∏ i : Fin (n + 1), marks i (x i.rev)) *
                interiorPathObservable M t n a b (fun i => x i.rev) =
              (∏ i : Fin (n + 1), marks i.rev (x i)) *
                interiorPathObservable M t n b a x
          rw [hprod, interiorPathObservable_rev M t n a b x]

end PerronWright.GraphCore
