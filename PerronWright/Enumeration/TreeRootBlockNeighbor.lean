import PerronWright.Enumeration.TreeRootBlockIntegral

/-!
# The unique root edge of a root-deleted tree block

If a labelled tree is cut at its distinguished root, every resulting block
contains exactly one endpoint of an edge from the root.  This is the
combinatorial fact that turns the product of root-edge kernels in one block
into a single kernel factor.  Together with `TreeRootBlockIntegral`, it is the
first local ingredient in the all-size rooted-tree coefficient recursion.
-/

open scoped Classical

namespace PerronWright

/-- Every part of the rootless partition of a tree contains a unique vertex
adjacent to the root. -/
theorem finRootlessPartition_part_existsUnique_root_neighbor
    {n : ℕ} (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : Finset (Fin n))
    (hB : B ∈ (finRootlessPartition n H).parts) :
    ∃! i : Fin n, i ∈ B ∧ H.Adj 0 i.succ := by
  classical
  let P := finRootlessPartition n H
  obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
  let c : (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).ConnectedComponent :=
    (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).connectedComponentMk
      ⟨i.succ, i.succ_ne_zero⟩
  obtain ⟨u, ⟨h0u, huc⟩, hu⟩ :=
    tree_root_component_unique_neighbor H hT 0 c
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0u.ne.symm
  have hjpart : j ∈ P.part i := by
    apply (finRootlessPartition_mem_part_iff n H i j).2
    exact huc.symm
  have hpart : P.part i = B := P.part_eq_of_mem hB hi
  have hjB : j ∈ B := by simpa only [hpart] using hjpart
  refine ⟨j, ⟨hjB, h0u⟩, ?_⟩
  intro k hk
  have hkpart : k ∈ P.part i := by simpa only [hpart] using hk.1
  have hkc :
      (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).connectedComponentMk
        ⟨k.succ, k.succ_ne_zero⟩ = c := by
    exact ((finRootlessPartition_mem_part_iff n H i k).1 hkpart).symm
  have hs : k.succ = j.succ := hu k.succ ⟨hk.2, hkc⟩
  exact Fin.succ_injective n hs

/-- In one root-deleted block of a tree, the product of all conditional root
kernel factors is the single factor belonging to the block's unique root
neighbor.  The existential formulation avoids introducing a choice-dependent
auxiliary symbol into later coefficient formulas. -/
theorem CompactBJRModel.tree_root_block_kernel_product_eq_single
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : Finset (Fin n))
    (hB : B ∈ (finRootlessPartition n H).parts) :
    ∃ i ∈ B, H.Adj 0 i.succ ∧
      ∀ (root : S) (z : Fin n → S),
        (∏ j ∈ B, if H.Adj 0 j.succ then M.kernel root (z j) else 1) =
          M.kernel root (z i) := by
  classical
  obtain ⟨i, hi, huniq⟩ :=
    finRootlessPartition_part_existsUnique_root_neighbor H hT B hB
  refine ⟨i, hi.1, hi.2, ?_⟩
  intro root z
  calc
    _ = (if H.Adj 0 i.succ then M.kernel root (z i) else 1) := by
      apply Finset.prod_eq_single_of_mem i hi.1
      intro j hj hji
      have hnot : ¬H.Adj 0 j.succ := by
        intro hadj
        exact hji (huniq j ⟨hj, hadj⟩)
      simp only [hnot, ↓reduceIte]
    _ = M.kernel root (z i) := if_pos hi.2

end PerronWright
