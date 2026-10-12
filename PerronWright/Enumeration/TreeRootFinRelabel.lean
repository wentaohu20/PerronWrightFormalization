import PerronWright.Enumeration.TreeRootPartition
import Mathlib.Data.Fin.SuccPred

/-!
# Relabelling the blocks of a finite rooted tree

For a graph on `Fin (n + 1)` rooted at zero, the graph on the other
vertices is isomorphic to a graph on `Fin n`. Its connected blocks form a
finite partition. Each block can in turn be relabelled by `Fin |B|`, and,
when the original graph is a tree, the relabelled block graph is a tree.
-/

open scoped Classical

namespace PerronWright

noncomputable def finRootlessGraphIso (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) :
    H.comap (Fin.succ : Fin n → Fin (n + 1)) ≃g
      H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1))) := by
  let e : Fin n ≃ ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1))) :=
    Equiv.ofBijective (fun i : Fin n =>
      (⟨i.succ, i.succ_ne_zero⟩ : ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))))
      ⟨(fun i j hij => Fin.succ_injective n (congr_arg Subtype.val hij)), by
        intro j
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero j.property
        exact ⟨i, Subtype.ext hi⟩⟩
  refine { e with map_rel_iff' := ?_ }
  intro a b
  change H.Adj a.succ b.succ ↔ H.Adj a.succ b.succ
  exact Iff.rfl

noncomputable def finRootlessPartition (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (H.comap (Fin.succ : Fin n → Fin (n + 1))).reachableSetoid

theorem finRootlessPartition_mem_part_iff (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) (i j : Fin n) :
    j ∈ (finRootlessPartition n H).part i ↔
      (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).connectedComponentMk
        ⟨i.succ, i.succ_ne_zero⟩ =
      (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).connectedComponentMk
        ⟨j.succ, j.succ_ne_zero⟩ := by
  rw [finRootlessPartition, Finpartition.mem_part_ofSetoid_iff_rel,
    SimpleGraph.ConnectedComponent.eq]
  exact (SimpleGraph.Iso.reachable_iff (φ := finRootlessGraphIso n H)).symm

theorem finRootlessPartition_part_eq_component_supp (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) (i : Fin n) :
    (((finRootlessPartition n H).part i : Finset (Fin n)) : Set (Fin n)) =
      ((H.comap (Fin.succ : Fin n → Fin (n + 1))).connectedComponentMk i).supp := by
  ext j
  rw [Finset.mem_coe, finRootlessPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (H.comap Fin.succ).Reachable i j ↔
    (H.comap Fin.succ).connectedComponentMk j =
      (H.comap Fin.succ).connectedComponentMk i
  constructor
  · intro h
    exact (SimpleGraph.ConnectedComponent.eq.mpr h).symm
  · intro h
    exact SimpleGraph.ConnectedComponent.eq.mp h.symm

theorem finRootlessPartition_part_isTree (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) (i : Fin n) :
    ((H.comap (Fin.succ : Fin n → Fin (n + 1))).induce
      ((((finRootlessPartition n H).part i : Finset (Fin n)) : Set (Fin n)))).IsTree := by
  let e : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩
  have hacyc : (H.comap (Fin.succ : Fin n → Fin (n + 1))).IsAcyclic :=
    hT.isAcyclic.of_comap e
  rw [finRootlessPartition_part_eq_component_supp]
  exact hacyc.isTree_connectedComponent _

noncomputable def finRootlessBlockTreeGraph (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) (i : Fin n) :
    SimpleGraph (Fin ((finRootlessPartition n H).part i).card) :=
  let B := (finRootlessPartition n H).part i
  ((H.comap (Fin.succ : Fin n → Fin (n + 1))).induce (B : Set (Fin n))).comap
    (B.equivFin.symm : Fin B.card → B)

theorem finRootlessBlockTreeGraph_isTree (n : ℕ)
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) (i : Fin n) :
    (finRootlessBlockTreeGraph n H i).IsTree := by
  let B := (finRootlessPartition n H).part i
  let G := (H.comap (Fin.succ : Fin n → Fin (n + 1))).induce (B : Set (Fin n))
  have hG : G.IsTree := finRootlessPartition_part_isTree n H hT i
  exact (SimpleGraph.Iso.comap B.equivFin.symm G).isTree_iff.mpr hG

end PerronWright
