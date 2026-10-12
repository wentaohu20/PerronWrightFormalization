import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Components after removing the root of a tree

Each connected component of the induced graph on vertices other than the root
has exactly one vertex adjacent to the root. This is the combinatorial first
step toward decomposing a finite labelled rooted tree into rooted branches.
-/

open scoped Classical

namespace PerronWright

theorem tree_root_neighbors_distinct_components
    {V : Type*} (H : SimpleGraph V) (hT : H.IsTree)
    (r u v : V) (hru : H.Adj r u) (hrv : H.Adj r v)
    (huv : u ≠ v) :
    (H.induce {r}ᶜ).connectedComponentMk ⟨u, hru.ne.symm⟩ ≠
      (H.induce {r}ᶜ).connectedComponentMk ⟨v, hrv.ne.symm⟩ := by
  intro heq
  have hreach := SimpleGraph.ConnectedComponent.eq.mp heq
  obtain ⟨p⟩ := hreach
  let q : (H.induce {r}ᶜ).Walk ⟨u, hru.ne.symm⟩ ⟨v, hrv.ne.symm⟩ := p.toPath.1
  let e : H.induce {r}ᶜ ↪g H := SimpleGraph.Embedding.induce {r}ᶜ
  have hq0 : q.IsPath := p.toPath.2
  have hq : (q.map e.toHom).IsPath := hq0.map e.injective
  have htwo : (hru.symm.toWalk.concat hrv).IsPath := by
    apply hru.symm.isPath_toWalk.concat
    simp [huv.symm, hrv.ne.symm]
  have huniq : q.map e.toHom = hru.symm.toWalk.concat hrv :=
    (hT.existsUnique_path u v).unique hq htwo
  have hroot : r ∈ (q.map e.toHom).support := by
    rw [huniq]
    change r ∈ [u, r, v]
    simp
  rw [SimpleGraph.Walk.support_map] at hroot
  simp only [List.mem_map] at hroot
  obtain ⟨w, _, hw⟩ := hroot
  exact w.property hw

theorem tree_root_component_has_neighbor
    {V : Type*} (H : SimpleGraph V) (hT : H.IsTree)
    (r : V) (c : (H.induce {r}ᶜ).ConnectedComponent) :
    ∃ u : V, ∃ hru : H.Adj r u,
      (H.induce {r}ᶜ).connectedComponentMk ⟨u, hru.ne.symm⟩ = c := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep c
  obtain ⟨p, hp, _⟩ := hT.existsUnique_path r x.1
  have hxr : (x : V) ≠ r := x.property
  obtain ⟨u, hru, t, hpdecomp⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p
  subst p
  have hnot : r ∉ t.support :=
    ((SimpleGraph.Walk.cons_isPath_iff hru t).mp hp).2
  have hcont : ∀ z : V, z ∈ t.support → z ∈ ({r}ᶜ : Set V) := by
    intro z hz
    exact fun hzr => hnot (hzr ▸ hz)
  refine ⟨u, hru, ?_⟩
  apply SimpleGraph.ConnectedComponent.sound
  exact ⟨t.induce {r}ᶜ hcont⟩

theorem tree_root_component_unique_neighbor
    {V : Type*} (H : SimpleGraph V) (hT : H.IsTree)
    (r : V) (c : (H.induce {r}ᶜ).ConnectedComponent) :
    ∃! u : V, ∃ hru : H.Adj r u,
      (H.induce {r}ᶜ).connectedComponentMk ⟨u, hru.ne.symm⟩ = c := by
  obtain ⟨u, hru, hu⟩ := tree_root_component_has_neighbor H hT r c
  refine ⟨u, ⟨hru, hu⟩, ?_⟩
  intro v hv
  obtain ⟨hrv, hv⟩ := hv
  by_contra hne
  exact tree_root_neighbors_distinct_components H hT r u v hru hrv
    (fun he => hne he.symm) (hu.trans hv.symm)

end PerronWright
