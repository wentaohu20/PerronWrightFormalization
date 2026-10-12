import PerronWright.Enumeration.KernelEndpointValence

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The endpoint-multiset count is exactly the multigraph incidence
multiplicity; in particular, a loop contributes two. -/
theorem finiteMultiGraph_incidence_eq_count
    {v : ℕ} (edge : Sym2 (Fin v)) (x : Fin v) :
    PerronWright.FiniteMultiGraph.incidence edge x =
      edge.toMultiset.count x := by
  induction edge using Sym2.inductionOn with
  | _ i j =>
      rw [PerronWright.FiniteMultiGraph.incidence_mk]
      have h : s(i, j).toMultiset = (↑[i, j] : Multiset (Fin v)) := by
        rfl
      rw [h, Multiset.coe_count]
      change ((if i = x then 1 else 0) + (if j = x then 1 else 0)) =
        List.count x [i, j]
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      omega

theorem sym2_toMultiset_map
    {A B : Type*} (f : A → B) (z : Sym2 A) :
    (Sym2.map f z).toMultiset = z.toMultiset.map f := by
  induction z using Sym2.inductionOn with
  | _ x y => rfl

theorem sym2_map_injective_count
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f)
    (z : Sym2 A) (a : A) :
    (Sym2.map f z).toMultiset.count (f a) =
      z.toMultiset.count a := by
  rw [sym2_toMultiset_map]
  exact Multiset.count_map_eq_count' f z.toMultiset hf a

theorem kernelBranchEndpoints_count_eq_original
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (e : KernelEdgeLabel G)
    (b : V) (hb : b ∈ branchingVertices G) :
    (kernelBranchEndpoints G hmin hacyc e).toMultiset.count
      (⟨b, hb⟩ : (branchingVertices G : Set V)) =
    (kernelEdgeEndpoints G hacyc e).toMultiset.count b := by
  have h := sym2_map_injective_count
    (f := (Subtype.val : {x : V // x ∈ branchingVertices G} → V))
    Subtype.val_injective
    (kernelBranchEndpoints G hmin hacyc e)
    (⟨b, hb⟩ : (branchingVertices G : Set V))
  calc
    _ = (Sym2.map Subtype.val
          (kernelBranchEndpoints G hmin hacyc e)).toMultiset.count b := h.symm
    _ = _ := by rw [kernelBranchEndpoints_map_val]

set_option linter.style.haveILetI false in
/-- The finite, edge-labelled endpoint table obtained from an actual
cubic two-core has degree exactly three at every relabelled vertex. -/
theorem normalizedCubicKernelShape_valence_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3)
    (j : Fin (2 * ell)) :
    (∑ i : Fin (3 * ell),
      ((normalizedCubicKernelShape G hconn hmin hell hs hcubic i).toMultiset.count j)) = 3 := by
  let B := branchingVertices G
  let hacyc := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hB : B.card = 2 * ell :=
    (branchingVertices_card_eq_two_surplus_iff_cubic G hmin hs).mpr hcubic
  have hE : Nat.card (KernelEdgeLabel G) = 3 * ell :=
    (kernelEdgeLabel_card_eq_three_surplus_iff_cubic G hconn hmin hell hs).mpr hcubic
  letI : Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent :=
    Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  let eB : B ≃ Fin (2 * ell) := Finset.equivFinOfCardEq hB
  let eE : KernelEdgeLabel G ≃ Fin (3 * ell) := by
    apply Fintype.equivFinOfCardEq
    simpa only [Nat.card_eq_fintype_card] using hE
  let b : B := eB.symm j
  have hnorm : normalizedCubicKernelShape G hconn hmin hell hs hcubic =
      fun i => Sym2.map eB
        (kernelBranchEndpoints G hmin hacyc (eE.symm i)) := by
    rfl
  have hcount (e : KernelEdgeLabel G) :
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc e)).toMultiset.count j =
      (kernelEdgeEndpoints G hacyc e).toMultiset.count b.val := by
    have hm := sym2_map_injective_count
      (f := eB) eB.injective
      (kernelBranchEndpoints G hmin hacyc e) b
    rw [eB.apply_symm_apply] at hm
    calc
      _ = (kernelBranchEndpoints G hmin hacyc e).toMultiset.count b := hm
      _ = _ := kernelBranchEndpoints_count_eq_original G hmin hacyc e b.val b.property
  calc
    (∑ i : Fin (3 * ell),
      (normalizedCubicKernelShape G hconn hmin hell hs hcubic i).toMultiset.count j) =
        ∑ i : Fin (3 * ell),
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc (eE.symm i))).toMultiset.count j := by
      simp only [hnorm]
    _ = ∑ e : KernelEdgeLabel G,
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc e)).toMultiset.count j := by
      exact Fintype.sum_equiv eE.symm _ _ (by intro i; simp)
    _ = ∑ e : KernelEdgeLabel G,
          (kernelEdgeEndpoints G hacyc e).toMultiset.count b.val := by
      apply Finset.sum_congr rfl
      intro e _
      exact hcount e
    _ = kernelEndpointValence G hacyc b.val := by
      exact (kernelEndpointValence_eq_sum_edgeLabels G hacyc b.val).symm
    _ = 3 := by
      rw [kernelEndpointValence_eq_original_degree G hmin hacyc b.val b.property]
      exact hcubic b.val b.property

/-- The relabelled endpoint table, regarded as the project's literal finite
multigraph structure. -/
def normalizedCubicFiniteMultiGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3) :
    PerronWright.FiniteMultiGraph (2 * ell) (3 * ell) :=
  ⟨normalizedCubicKernelShape G hconn hmin hell hs hcubic⟩

/-- Consequently the actual normalized finite multigraph is cubic in the
literal `FiniteMultiGraph.degree` sense used by the finite kernel library. -/
theorem normalizedCubicFiniteMultiGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3)
    (j : Fin (2 * ell)) :
    (normalizedCubicFiniteMultiGraph G hconn hmin hell hs hcubic).degree j = 3 := by
  unfold normalizedCubicFiniteMultiGraph PerronWright.FiniteMultiGraph.degree
  simpa only [finiteMultiGraph_incidence_eq_count] using
    normalizedCubicKernelShape_valence_three G hconn hmin hell hs hcubic j

end PerronWright.GraphCore
