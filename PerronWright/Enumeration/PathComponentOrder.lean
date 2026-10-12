import PerronWright.Enumeration.DegreeTwoPaths
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

set_option linter.style.haveILetI false in
/-- A finite tree of maximum degree two admits a walk that visits every
vertex exactly once. -/
theorem exists_hamiltonianPath_of_isTree_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (htree : H.IsTree) (hdeg : ∀ v, H.degree v ≤ 2) :
    ∃ u v, ∃ p : H.Walk u v, p.IsHamiltonian := by
  classical
  rcases subsingleton_or_nontrivial V with hsub | hnon
  · letI : Subsingleton V := hsub
    letI : Nonempty V := htree.connected.nonempty
    let u : V := Classical.choice inferInstance
    exact ⟨u, u, .nil, SimpleGraph.Walk.IsHamiltonian.of_subsingleton⟩
  · letI : Nontrivial V := hnon
    obtain ⟨u, v, p, hp, hmax⟩ :=
      SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
    obtain ⟨u', v', hne⟩ := exists_pair_ne V
    obtain ⟨p', hp'⟩ := htree.connected.exists_isPath u' v'
    have hnil : ¬p.Nil := by
      intro h
      have hpzero : p.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr h
      have hp'pos : 0 < p'.length := Nat.pos_of_ne_zero fun hp'zero =>
        hne (SimpleGraph.Walk.eq_of_length_eq_zero hp'zero)
      have := hmax u' v' p' hp'
      omega
    have hdu : H.degree u = 1 := by
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      refine ⟨p.snd, p.adj_snd hnil, fun w hadj => ?_⟩
      apply htree.isAcyclic.eq_snd_of_adj_start hp hadj
      have hnot : ¬(p.cons hadj.symm).IsPath := by
        intro hpath
        have := hmax w v (p.cons hadj.symm) hpath
        simp only [SimpleGraph.Walk.length_cons] at this
        omega
      exact Classical.byContradiction fun hsupp =>
        hnot (hp.cons hsupp)
    have hdv : H.degree v = 1 := by
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      refine ⟨p.penultimate, (p.adj_penultimate hnil).symm, fun w hadj => ?_⟩
      apply htree.isAcyclic.eq_penultimate_of_adj_end hp hadj
      have hnot : ¬(p.concat hadj).IsPath := by
        intro hpath
        have := hmax u w (p.concat hadj) hpath
        simp only [SimpleGraph.Walk.length_concat] at this
        omega
      exact Classical.byContradiction fun hsupp =>
        hnot (hp.concat hsupp hadj)
    refine ⟨u, v, p, hp.isHamiltonian_of_mem ?_⟩
    intro z
    by_contra hz
    have hclosed : ∀ a ∈ p.support, ∀ b, H.Adj a b → b ∈ p.support := by
      intro a ha b hab
      by_cases hau : a = u
      · subst a
        obtain ⟨q, hq, huniq⟩ :=
          SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdu
        have hb : b = p.snd :=
          (huniq b hab).trans (huniq p.snd (p.adj_snd hnil)).symm
        rw [hb]
        exact p.getVert_mem_support 1
      by_cases hav : a = v
      · subst a
        obtain ⟨q, hq, huniq⟩ :=
          SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdv
        have hb : b = p.penultimate :=
          (huniq b hab).trans
            (huniq p.penultimate (p.adj_penultimate hnil).symm).symm
        rw [hb]
        exact p.getVert_mem_support (p.length - 1)
      obtain ⟨i, hia, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        apply hau
        simpa using hia.symm
      have hil : i ≠ p.length := by
        intro hil
        rw [hil, p.getVert_length] at hia
        exact hav hia.symm
      have hi_le : i ≤ p.length := hi
      have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have hi_lt : i < p.length := lt_of_le_of_ne hi_le hil
      let aPrev := p.getVert (i - 1)
      let aNext := p.getVert (i + 1)
      have hprev : H.Adj aPrev a := by
        have hadj := p.adj_getVert_succ (show i - 1 < p.length by omega)
        have hs : i - 1 + 1 = i := by omega
        simpa only [aPrev, hia, hs] using hadj
      have hnext : H.Adj a aNext := by
        have hadj := p.adj_getVert_succ hi_lt
        simpa only [aNext, hia] using hadj
      have hneigh : aPrev ≠ aNext := by
        intro heq
        have hind := hp.getVert_injOn
          (show i - 1 ≤ p.length by omega)
          (show i + 1 ≤ p.length by omega) heq
        omega
      have hpair : ({aPrev, aNext} : Finset V) = H.neighborFinset a := by
        apply Finset.eq_of_subset_of_card_le
        · intro q hq
          have hq' : q = aPrev ∨ q = aNext := by simpa using hq
          rcases hq' with rfl | rfl
          · exact (H.mem_neighborFinset a aPrev).mpr hprev.symm
          · exact (H.mem_neighborFinset a aNext).mpr hnext
        · rw [H.card_neighborFinset_eq_degree]
          simpa [Finset.card_pair hneigh] using hdeg a
      have hb : b ∈ ({aPrev, aNext} : Finset V) := by
        rw [hpair]
        exact (H.mem_neighborFinset a b).mpr hab
      have hb' : b = aPrev ∨ b = aNext := by simpa using hb
      rcases hb' with rfl | rfl
      · exact p.getVert_mem_support (i - 1)
      · exact p.getVert_mem_support (i + 1)
    have hfull := closed_nonempty_eq_univ_of_connected H htree.connected
      ⟨u, p.start_mem_support⟩ hclosed
    have : z ∈ p.support := by
      have hzuniv : z ∈ (Set.univ : Set V) := Set.mem_univ z
      rw [← hfull] at hzuniv
      exact hzuniv
    exact hz this

/-- A Hamiltonian path in a finite tree uses every edge of the tree.
This rules out hidden chords when the path is used as a coordinate
ordering. -/
theorem hamiltonianPath_edges_toFinset_eq_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (htree : H.IsTree) {u v : V} (p : H.Walk u v)
    (hp : p.IsHamiltonian) :
    p.edges.toFinset = H.edgeFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    apply H.mem_edgeFinset.mpr
    apply p.edges_subset_edgeSet
    simpa using he
  · have hpCard : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup hp.isPath.isTrail.edges_nodup,
        p.length_edges]
    have htreeCard := htree.card_edgeFinset
    rw [hpCard, hp.length_eq]
    omega

/-- A Hamiltonian path in a finite tree gives an actual graph
isomorphism from the standard path graph, not merely an injective
graph homomorphism. -/
def hamiltonianPathGraphIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (htree : H.IsTree) {u v : V} (p : H.Walk u v)
    (hp : p.IsHamiltonian) :
    SimpleGraph.pathGraph (p.length + 1) ≃g H := by
  let f : Fin (p.length + 1) → V := fun i => p.getVert i
  have hfInj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.isPath.getVert_injOn
      (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  have hfSurj : Function.Surjective f := by
    intro z
    obtain ⟨n, hn⟩ := hp.getVert_surjective z
    by_cases hnl : n ≤ p.length
    · exact ⟨⟨n, by omega⟩, hn⟩
    · refine ⟨⟨p.length, by omega⟩, ?_⟩
      change p.getVert p.length = z
      rw [← hn, p.getVert_length,
        p.getVert_of_length_le (le_of_not_ge hnl)]
  let e : Fin (p.length + 1) ≃ V :=
    Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  have he_apply (i : Fin (p.length + 1)) : e i = p.getVert i := by
    rfl
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_rel_iff' := ?_ }
  intro i j
  constructor
  · intro hij
    have hedgeFin : s(e i, e j) ∈ H.edgeFinset :=
      H.mem_edgeFinset.mpr (H.mem_edgeSet.mpr hij)
    have hall := hamiltonianPath_edges_toFinset_eq_edgeFinset H htree p hp
    have hedge : s(e i, e j) ∈ p.edges := by
      rw [← hall] at hedgeFin
      simpa using hedgeFin
    obtain ⟨n, hn, hpair⟩ := (p.mk_mem_edges_iff_exists).mp hedge
    let ni : Fin (p.length + 1) := ⟨n, by omega⟩
    let nj : Fin (p.length + 1) := ⟨n + 1, by omega⟩
    rcases Sym2.eq_iff.mp hpair with hdir | hrev
    · have hni : ni = i := by
        apply e.injective
        rw [he_apply ni]
        simpa [ni] using hdir.1
      have hnj : nj = j := by
        apply e.injective
        rw [he_apply nj]
        simpa [nj] using hdir.2
      rw [← hni, ← hnj]
      apply SimpleGraph.pathGraph_adj.mpr
      exact Or.inl rfl
    · have hni : ni = j := by
        apply e.injective
        rw [he_apply ni]
        simpa [ni] using hrev.1
      have hnj : nj = i := by
        apply e.injective
        rw [he_apply nj]
        simpa [nj] using hrev.2
      rw [← hnj, ← hni]
      apply SimpleGraph.pathGraph_adj.mpr
      exact Or.inr rfl
  · intro hij
    rw [SimpleGraph.pathGraph_adj] at hij
    rcases hij with hij | hij
    · have hadj := p.adj_getVert_succ (i := i.val) (by omega)
      change H.Adj (e i) (e j)
      rw [he_apply i, he_apply j]
      simpa only [hij] using hadj
    · have hadj := p.adj_getVert_succ (i := j.val) (by omega)
      change H.Adj (e i) (e j)
      rw [he_apply i, he_apply j]
      simpa only [hij] using hadj.symm

/-- Each actual connected component of the induced degree-two forest is
a finite tree of maximum degree two.  This packages the two facts needed
to put a canonical path coordinate system on the component. -/
theorem degreeTwo_component_isTree_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    C.toSimpleGraph.IsTree ∧
      (∀ x : C, C.toSimpleGraph.degree x ≤ 2) := by
  let H := G.induce {v | G.degree v = 2}
  have htree : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph, hacyc.induce C.supp⟩
  have hdeg : ∀ x : C, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    let f : SimpleGraph.Copy C.toSimpleGraph H :=
      ⟨C.toSimpleGraph_hom, Subtype.val_injective⟩
    have hle : C.toSimpleGraph.degree x ≤ H.degree x.val :=
      f.degree_le x
    exact hle.trans (degreeTwo_induced_degree_le_two G x.val)
  exact ⟨htree, hdeg⟩

/-- Every actual connected component of the induced degree-two forest is
isomorphic to the standard path graph on exactly its number of vertices.
This rules out hidden chords and supplies the coordinate reordering used
before the componentwise path-kernel integral. -/
theorem degreeTwo_component_pathGraphIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    Nonempty
      (SimpleGraph.pathGraph (Fintype.card C) ≃g C.toSimpleGraph) := by
  obtain ⟨htree, hdeg⟩ :=
    degreeTwo_component_isTree_degree_le_two G hacyc C
  obtain ⟨u, v, p, hp⟩ :=
    exists_hamiltonianPath_of_isTree_degree_le_two C.toSimpleGraph htree hdeg
  have hn : p.length + 1 = Fintype.card C := by
    calc
      p.length + 1 = p.support.length := p.length_support.symm
      _ = Fintype.card C := hp.length_support
  let e := hamiltonianPathGraphIso C.toSimpleGraph htree p hp
  exact ⟨hn ▸ e⟩

#print axioms PerronWright.GraphCore.exists_hamiltonianPath_of_isTree_degree_le_two
#print axioms PerronWright.GraphCore.hamiltonianPath_edges_toFinset_eq_edgeFinset
#print axioms PerronWright.GraphCore.hamiltonianPathGraphIso
#print axioms PerronWright.GraphCore.degreeTwo_component_isTree_degree_le_two
#print axioms PerronWright.GraphCore.degreeTwo_component_pathGraphIso

end PerronWright.GraphCore
