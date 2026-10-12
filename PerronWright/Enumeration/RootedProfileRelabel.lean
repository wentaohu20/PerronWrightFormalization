import PerronWright.Enumeration.FixedRootedGraphProfile
import PerronWright.Enumeration.CorePathIntegral

/-!
# Rooted finite-graph profiles under relabelling

This file proves the relabelling statement needed to identify the sum of
independently labelled root branches with the actual rooted-tree coefficient.
It uses the already-proved graph-integrand invariance and iid product-measure
reindexing; no relabelling hypothesis is introduced.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem fieldGraphWeightIntegrand_zero_eq_finiteGraphWeightIntegrand_one
    (M : CompactBJRModel S) {k : ℕ}
    (G : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.fieldGraphWeightIntegrand 0 G x =
      GraphCore.finiteGraphWeightIntegrand M 1 G x := by
  unfold CompactBJRModel.fieldGraphWeightIntegrand
    GraphCore.finiteGraphWeightIntegrand CompactBJRModel.edgeFactor
  simp only [ContinuousMap.zero_apply, zero_sub, neg_mul, one_mul]

/-- The complement coordinates left after fixing a root are carried to the
complement coordinates of its image under a vertex permutation. -/
noncomputable def rootComplementEquiv {m : ℕ}
    (e : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1)) : Fin m ≃ Fin m :=
  (finSuccAboveEquiv v).trans <|
    (e.subtypeEquiv (fun i => by simp)).trans
      (finSuccAboveEquiv (e v)).symm

theorem rootComplementEquiv_succAbove {m : ℕ}
    (e : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1)) (i : Fin m) :
    e (v.succAbove i) =
      (e v).succAbove (rootComplementEquiv e v i) := by
  let e₀ : {i : Fin (m + 1) // i ≠ v} ≃
      {j : Fin (m + 1) // j ≠ e v} :=
    e.subtypeEquiv (fun i => by simp)
  have h := congrArg Subtype.val
    ((finSuccAboveEquiv (e v)).apply_symm_apply
      (e₀ (finSuccAboveEquiv v i)))
  change e (v.succAbove i) =
    (e v).succAbove
      ((finSuccAboveEquiv (e v)).symm
        (e₀ (finSuccAboveEquiv v i)))
  exact h.symm

/-- Relabelling a finite graph and its distinguished root leaves its
type-resolved zero-field rooted profile unchanged. -/
theorem CompactBJRModel.fixedRootedGraphProfileMap_comap_equiv
    (M : CompactBJRModel S) {m : ℕ}
    (G : SimpleGraph (Fin (m + 1)))
    (e : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1)) :
    M.fixedRootedGraphProfileMap (G.comap e) v =
      M.fixedRootedGraphProfileMap G (e v) := by
  ext root
  rw [M.fixedRootedGraphProfileMap_apply,
    M.fixedRootedGraphProfileMap_apply]
  unfold CompactBJRModel.fixedRootedGraphProfile
  let q : Fin m ≃ Fin m := rootComplementEquiv e v
  have hcomp (z : Fin m → S) :
      (Fin.insertNth (e v) root (fun j => z (q.symm j))) ∘ e =
        Fin.insertNth v root z := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove v j with rfl | ⟨i, rfl⟩
    · simp only [Function.comp_apply, Fin.insertNth_apply_same]
    · rw [Function.comp_apply, rootComplementEquiv_succAbove]
      simp only [Fin.insertNth_apply_succAbove, q, Equiv.symm_apply_apply]
  have hpoint (z : Fin m → S) :
      M.fieldGraphWeightIntegrand 0 (G.comap e)
          (Fin.insertNth v root z) =
        M.fieldGraphWeightIntegrand 0 G
          (Fin.insertNth (e v) root (fun j => z (q.symm j))) := by
    rw [fieldGraphWeightIntegrand_zero_eq_finiteGraphWeightIntegrand_one,
      fieldGraphWeightIntegrand_zero_eq_finiteGraphWeightIntegrand_one]
    have hiso := GraphCore.finiteGraphWeightIntegrand_iso M 1
      (G.comap e) G (SimpleGraph.Iso.comap e G)
      (Fin.insertNth (e v) root (fun j => z (q.symm j)))
    change GraphCore.finiteGraphWeightIntegrand M 1 (G.comap e)
        ((Fin.insertNth (e v) root (fun j => z (q.symm j))) ∘ e) =
      GraphCore.finiteGraphWeightIntegrand M 1 G
        (Fin.insertNth (e v) root (fun j => z (q.symm j))) at hiso
    rw [hcomp] at hiso
    exact hiso
  calc
    (∫ z : Fin m → S,
        M.fieldGraphWeightIntegrand 0 (G.comap e)
          (Fin.insertNth v root z)
        ∂Measure.pi (fun _ : Fin m => M.mu)) =
      ∫ z : Fin m → S,
        M.fieldGraphWeightIntegrand 0 G
          (Fin.insertNth (e v) root (fun j => z (q.symm j)))
        ∂Measure.pi (fun _ : Fin m => M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ y : Fin m → S,
        M.fieldGraphWeightIntegrand 0 G
          (Fin.insertNth (e v) root y)
        ∂Measure.pi (fun _ : Fin m => M.mu) := by
      exact (GraphCore.integral_pi_reindex M.mu q
        (fun y : Fin m → S =>
          M.fieldGraphWeightIntegrand 0 G
            (Fin.insertNth (e v) root y))).symm

/-- Relabelling all vertices by a permutation gives an equivalence on the
finite type of labelled trees. -/
noncomputable def treeGraphPermEquiv {k : ℕ}
    (e : Equiv.Perm (Fin k)) :
    {G : SimpleGraph (Fin k) // G.IsTree} ≃
      {G : SimpleGraph (Fin k) // G.IsTree} :=
  e.simpleGraph.subtypeEquiv fun G => by
    exact (SimpleGraph.Iso.comap e.symm G).isTree_iff.symm

/-- After summing over every labelled tree, the type-resolved rooted profile
does not depend on which label is declared to be the root. -/
theorem CompactBJRModel.sum_tree_fixedRootedGraphProfileMap_eq_root_zero
    (M : CompactBJRModel S) {m : ℕ} (v : Fin (m + 1)) :
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap H.1 v) =
      ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap H.1 0 := by
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 v
  let E := treeGraphPermEquiv e
  calc
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap H.1 v) =
      ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap (E H).1 v := by
      exact (E.sum_comp
        (fun H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree} =>
          M.fixedRootedGraphProfileMap H.1 v)).symm
    _ = ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap H.1 0 := by
      apply Fintype.sum_congr
      intro H
      change M.fixedRootedGraphProfileMap (H.1.comap e.symm) v = _
      rw [M.fixedRootedGraphProfileMap_comap_equiv H.1 e.symm v]
      rw [Equiv.symm_swap, Equiv.swap_apply_right]

end PerronWright
