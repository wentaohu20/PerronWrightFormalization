import PerronWright.Enumeration.GraphCore
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

noncomputable section

namespace PerronWright.GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restrict a two-core to an induced graph containing all its vertices. -/
theorem isTwoCore_induce_of_subset {s t : Set V}
    (hs : IsTwoCore G s) (hst : s ⊆ t) :
    IsTwoCore (G.induce t) {x : t | (x : V) ∈ s} := by
  intro x hx
  obtain ⟨w, hws, z, hzs, hwz, hxw, hxz⟩ := hs x.val hx
  refine ⟨⟨w, hst hws⟩, hws, ⟨z, hst hzs⟩, hzs, ?_, hxw, hxz⟩
  intro h
  exact hwz (congrArg Subtype.val h)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Forgetting the subtype labels of an induced core preserves its
two-neighbor certificate. -/
theorem isTwoCore_image_subtype {t : Set V} {s : Set t}
    (hs : IsTwoCore (G.induce t) s) :
    IsTwoCore G (Subtype.val '' s) := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨w, hws, z, hzs, hwz, hxw, hxz⟩ := hs x hx
  refine ⟨w.val, ⟨w, hws, rfl⟩, z.val, ⟨z, hzs, rfl⟩, ?_, hxw, hxz⟩
  intro h
  exact hwz (Subtype.ext h)

omit [DecidableEq V] in
/-- The unique maximal two-core is literally invariant under peeling a
degree-one vertex; the left side views the surviving subtype in `V`. -/
theorem greatestTwoCore_prune_leaf {v : V} (hv : G.degree v = 1) :
    Subtype.val '' greatestTwoCore (G.induce ({v}ᶜ : Set V)) =
      greatestTwoCore G := by
  apply Set.Subset.antisymm
  · exact isTwoCore_subset_greatest G
      (isTwoCore_image_subtype G (isTwoCore_greatest _))
  · intro x hx
    have hxne : x ≠ v := by
      intro h
      subst x
      exact leaf_not_mem_greatestTwoCore G hv hx
    let x' : ({v}ᶜ : Set V) := ⟨x, by simpa using hxne⟩
    have hsubset : greatestTwoCore G ⊆ ({v}ᶜ : Set V) := by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      subst y
      exact leaf_not_mem_greatestTwoCore G hv hy
    have hcore : IsTwoCore (G.induce ({v}ᶜ : Set V))
        {y : ({v}ᶜ : Set V) | (y : V) ∈ greatestTwoCore G} :=
      isTwoCore_induce_of_subset G (isTwoCore_greatest G) hsubset
    exact ⟨x', isTwoCore_subset_greatest _ hcore hx, rfl⟩

/-- A finite cycle has internal minimum degree two. -/
theorem cycleGraph_isTwoCore (n : ℕ) (hn : 3 ≤ n) :
    IsTwoCore (SimpleGraph.cycleGraph n) Set.univ := by
  intro v _
  have hdeg : (SimpleGraph.cycleGraph n).degree v = 2 := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
    subst n
    exact SimpleGraph.cycleGraph_degree_three_le
  have hcard : 1 < ((SimpleGraph.cycleGraph n).neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    omega
  obtain ⟨w, z, hw, hz, hwz⟩ := Finset.one_lt_card_iff.mp hcard
  exact ⟨w, Set.mem_univ _, z, Set.mem_univ _, hwz,
    by simpa using hw, by simpa using hz⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Injective graph homomorphisms carry internal degree-two certificates
to their literal image, even when the copy is not induced. -/
theorem isTwoCore_copy_range {W : Type*} (A : SimpleGraph W)
    (f : SimpleGraph.Copy A G) (h : IsTwoCore A Set.univ) :
    IsTwoCore G (Set.range f) := by
  intro v hv
  obtain ⟨x, rfl⟩ := hv
  obtain ⟨w, -, z, -, hwz, hxw, hxz⟩ := h x (Set.mem_univ x)
  exact ⟨f w, ⟨w, rfl⟩, f z, ⟨z, rfl⟩,
    fun he => hwz (f.injective he), f.toHom.map_adj hxw,
    f.toHom.map_adj hxz⟩

omit [DecidableEq V] in
/-- A connected finite graph with strictly positive surplus has a nonempty
2-core.  This is the substantive base case ensuring that leaf pruning does
not end at the empty graph in the complex-component range. -/
theorem greatestTwoCore_nonempty_of_positive_surplus
    (hc : G.Connected) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    (greatestTwoCore G).Nonempty := by
  have hnotacy : ¬ G.IsAcyclic := by
    intro ha
    have ht : G.IsTree := ⟨hc, ha⟩
    have he := ht.card_edgeFinset
    omega
  have hcyc : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
    by_contra h
    apply hnotacy
    intro v c hc'
    exact h ⟨v, c, hc'⟩
  obtain ⟨v, c, hcycle⟩ := hcyc
  let n := c.length
  have hn : 3 ≤ n := hcycle.three_le_length
  have hcopy : SimpleGraph.IsContained (SimpleGraph.cycleGraph n) G :=
    (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨v, c, hcycle, rfl⟩
  obtain ⟨f⟩ := hcopy
  have hcore : IsTwoCore G (Set.range f) :=
    isTwoCore_copy_range G (SimpleGraph.cycleGraph n) f (cycleGraph_isTwoCore n hn)
  let x : Fin n := ⟨0, by omega⟩
  exact ⟨f x, isTwoCore_subset_greatest G hcore ⟨x, rfl⟩⟩

end PerronWright.GraphCore
