import PerronWright.Enumeration.CubicKernelReconstruction

/-!
# Simultaneous coordinate relabelling of cubic subdivisions

This file supplies the coordinate action which is needed before an exact
reconstruction-fibre mass formula can be stated.  Vertex and edge coordinates
are relabelled simultaneously.  In particular, an edge permutation is never
applied while keeping the endpoint table fixed.

The present first layer transports the finite multigraph, the connected cubic
kernel, and every admissible length profile.  The subdivision-slot and label
transport is built below from these definitions; no automorphism factor or
fibre-cardinality assertion is used here.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Independent permutations of the normalized branch and kernel-edge
coordinates at surplus `ell`. -/
abbrev CubicKernelCoordinatePerm (ell : ℕ) :=
  Equiv.Perm (Fin (2 * ell)) × Equiv.Perm (Fin (3 * ell))

namespace CubicKernelCoordinatePerm

/-- The identity pair of normalized coordinate permutations. -/
def refl (ell : ℕ) : CubicKernelCoordinatePerm ell :=
  (Equiv.refl _, Equiv.refl _)

/-- First apply `γ`, then apply `η`. -/
def trans {ell : ℕ}
    (γ η : CubicKernelCoordinatePerm ell) :
    CubicKernelCoordinatePerm ell :=
  (γ.1.trans η.1, γ.2.trans η.2)

@[simp]
theorem refl_fst (ell : ℕ) : (refl ell).1 = Equiv.refl _ := rfl

@[simp]
theorem refl_snd (ell : ℕ) : (refl ell).2 = Equiv.refl _ := rfl

@[simp]
theorem trans_fst {ell : ℕ}
    (γ η : CubicKernelCoordinatePerm ell) :
    (trans γ η).1 = γ.1.trans η.1 := rfl

@[simp]
theorem trans_snd {ell : ℕ}
    (γ η : CubicKernelCoordinatePerm ell) :
    (trans γ η).2 = γ.2.trans η.2 := rfl

end CubicKernelCoordinatePerm

/-- Relabel both coordinates of an edge-labelled finite multigraph.  The
inverse edge permutation occurs because the displayed argument is a target
edge coordinate. -/
def finiteMultiGraphCoordinateRelabel {ell : ℕ}
    (γ : CubicKernelCoordinatePerm ell)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    PerronWright.FiniteMultiGraph (2 * ell) (3 * ell) where
  endpoints e := Sym2.map γ.1 (H.endpoints (γ.2.symm e))

@[simp]
theorem finiteMultiGraphCoordinateRelabel_endpoints {ell : ℕ}
    (γ : CubicKernelCoordinatePerm ell)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) :
    (finiteMultiGraphCoordinateRelabel γ H).endpoints e =
      Sym2.map γ.1 (H.endpoints (γ.2.symm e)) :=
  rfl

/-- Incidence is unchanged when an endpoint pair and the queried vertex are
transported by the same coordinate equivalence. -/
theorem finiteMultiGraph_incidence_map_equiv
    {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Sym2 (Fin n)) (v : Fin n) :
    PerronWright.FiniteMultiGraph.incidence (Sym2.map e p) (e v) =
      PerronWright.FiniteMultiGraph.incidence p v := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp [PerronWright.FiniteMultiGraph.incidence_mk]

/-- Multigraph degree is transported exactly by a simultaneous coordinate
relabeling. -/
theorem finiteMultiGraphCoordinateRelabel_degree {ell : ℕ}
    (γ : CubicKernelCoordinatePerm ell)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (v : Fin (2 * ell)) :
    (finiteMultiGraphCoordinateRelabel γ H).degree (γ.1 v) =
      H.degree v := by
  unfold PerronWright.FiniteMultiGraph.degree
  change
    (∑ e : Fin (3 * ell),
      PerronWright.FiniteMultiGraph.incidence
        (Sym2.map γ.1 (H.endpoints (γ.2.symm e))) (γ.1 v)) = _
  calc
    _ = ∑ e : Fin (3 * ell),
        PerronWright.FiniteMultiGraph.incidence
          (H.endpoints (γ.2.symm e)) v := by
      apply Finset.sum_congr rfl
      intro e _
      exact finiteMultiGraph_incidence_map_equiv
        γ.1 (H.endpoints (γ.2.symm e)) v
    _ = _ := (γ.2.symm).sum_comp
      (fun e => PerronWright.FiniteMultiGraph.incidence (H.endpoints e) v)

/-- The simple supports before and after coordinate relabelling are
canonically graph-isomorphic. -/
def finiteMultiGraphSupportGraphCoordinateRelabelIso {ell : ℕ}
    (γ : CubicKernelCoordinatePerm ell)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    finiteMultiGraphSupportGraph H ≃g
      finiteMultiGraphSupportGraph (finiteMultiGraphCoordinateRelabel γ H) where
  __ := γ.1
  map_rel_iff' := by
    intro u v
    simp only [finiteMultiGraphSupportGraph,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨⟨e, he⟩, huv⟩
      refine ⟨⟨γ.2.symm e, ?_⟩, ?_⟩
      · apply Sym2.map.injective γ.1.injective
        simpa only [finiteMultiGraphCoordinateRelabel_endpoints,
          Sym2.map_mk] using he
      · intro h
        exact huv (congrArg γ.1 h)
    · rintro ⟨⟨e, he⟩, huv⟩
      refine ⟨⟨γ.2 e, ?_⟩, γ.1.injective.ne huv⟩
      simp only [finiteMultiGraphCoordinateRelabel_endpoints,
        Equiv.symm_apply_apply, he, Sym2.map_mk]

/-- Coordinate relabelling preserves connectedness of the non-loop support. -/
theorem finiteMultiGraphSupportGraph_coordinateRelabel_connected_iff
    {ell : ℕ} (γ : CubicKernelCoordinatePerm ell)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    (finiteMultiGraphSupportGraph
        (finiteMultiGraphCoordinateRelabel γ H)).Connected ↔
      (finiteMultiGraphSupportGraph H).Connected := by
  exact (finiteMultiGraphSupportGraphCoordinateRelabelIso γ H).connected_iff.symm

/-- Relabel a connected edge-labelled cubic kernel, transporting both proof
fields from the exact degree and support-isomorphism lemmas. -/
def LabelledConnectedCubicKernel.coordinateRelabel {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (γ : CubicKernelCoordinatePerm ell) :
    LabelledConnectedCubicKernel ell where
  graph := finiteMultiGraphCoordinateRelabel γ K.graph
  cubic := by
    intro v
    obtain ⟨u, rfl⟩ := γ.1.surjective v
    rw [finiteMultiGraphCoordinateRelabel_degree]
    exact K.cubic u
  connected :=
    (finiteMultiGraphSupportGraph_coordinateRelabel_connected_iff
      γ K.graph).2 K.connected

@[simp]
theorem LabelledConnectedCubicKernel.coordinateRelabel_graph {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (γ : CubicKernelCoordinatePerm ell) :
    (K.coordinateRelabel γ).graph =
      finiteMultiGraphCoordinateRelabel γ K.graph :=
  rfl

/-- The identity coordinate pair leaves an endpoint table unchanged. -/
@[simp]
theorem finiteMultiGraphCoordinateRelabel_refl {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    finiteMultiGraphCoordinateRelabel (CubicKernelCoordinatePerm.refl ell) H = H := by
  cases H
  simp [finiteMultiGraphCoordinateRelabel,
    CubicKernelCoordinatePerm.refl]

/-- Successive coordinate relabellings compose in the expected order. -/
theorem finiteMultiGraphCoordinateRelabel_trans {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ η : CubicKernelCoordinatePerm ell) :
    finiteMultiGraphCoordinateRelabel η
        (finiteMultiGraphCoordinateRelabel γ H) =
      finiteMultiGraphCoordinateRelabel
        (CubicKernelCoordinatePerm.trans γ η) H := by
  cases H
  simp [finiteMultiGraphCoordinateRelabel,
    CubicKernelCoordinatePerm.trans, Sym2.map_map,
    Function.comp_def, Equiv.trans_apply]

/-- Transport an admissible length profile along simultaneous kernel
coordinates.  All admissibility clauses are preserved, including the
injectivity condition on zero-length parallel edges. -/
def CubicKernelLengthProfile.coordinateRelabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell) :
    CubicKernelLengthProfile k ell
      (finiteMultiGraphCoordinateRelabel γ H) where
  length e := L.length (γ.2.symm e)
  totalLength := by
    rw [(γ.2.symm).sum_comp (fun e => (L.length e).val)]
    exact L.totalLength
  loopLength := by
    intro e he
    apply L.loopLength (γ.2.symm e)
    apply (Sym2.isDiag_map γ.1.injective).mp
    simpa only [finiteMultiGraphCoordinateRelabel_endpoints] using he
  directEndpointsInjective := by
    intro e f hef
    let e' : {a : Fin (3 * ell) // (L.length a).val = 0} :=
      ⟨γ.2.symm e.1, e.2⟩
    let f' : {a : Fin (3 * ell) // (L.length a).val = 0} :=
      ⟨γ.2.symm f.1, f.2⟩
    have hsource : H.endpoints e'.1 = H.endpoints f'.1 := by
      apply Sym2.map.injective γ.1.injective
      simpa only [finiteMultiGraphCoordinateRelabel_endpoints] using hef
    have hsub : e' = f' := L.directEndpointsInjective hsource
    apply Subtype.ext
    have hval : γ.2.symm e.1 = γ.2.symm f.1 :=
      congrArg Subtype.val hsub
    exact γ.2.symm.injective hval

@[simp]
theorem CubicKernelLengthProfile.coordinateRelabel_length
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    (L.coordinateRelabel γ).length e = L.length (γ.2.symm e) :=
  rfl

@[simp]
theorem CubicKernelLengthProfile.coordinateRelabel_length_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    (L.coordinateRelabel γ).length (γ.2 e) = L.length e := by
  simp

/-- Coordinate relabelling induces an equivalence of loop-edge labels. -/
def cubicKernelLoopEdgeCoordinateRelabelEquiv
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell) :
    CubicKernelLoopEdge H ≃
      CubicKernelLoopEdge (finiteMultiGraphCoordinateRelabel γ H) where
  toFun e := ⟨γ.2 e.1, by
    rw [finiteMultiGraphCoordinateRelabel_endpoints]
    simp only [Equiv.symm_apply_apply]
    exact (Sym2.isDiag_map γ.1.injective).2 e.2⟩
  invFun e := ⟨γ.2.symm e.1, by
    apply (Sym2.isDiag_map γ.1.injective).mp
    simpa only [finiteMultiGraphCoordinateRelabel_endpoints] using e.2⟩
  left_inv e := Subtype.ext (γ.2.symm_apply_apply e.1)
  right_inv e := Subtype.ext (γ.2.apply_symm_apply e.1)

/-- In particular, coordinate relabelling preserves the number of loop-edge
labels exactly. -/
theorem cubicKernelLoopEdge_card_coordinateRelabel
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell) :
    Fintype.card
        (CubicKernelLoopEdge (finiteMultiGraphCoordinateRelabel γ H)) =
      Fintype.card (CubicKernelLoopEdge H) := by
  exact Fintype.card_congr
    (cubicKernelLoopEdgeCoordinateRelabelEquiv H γ).symm

/-- The canonically ordered endpoints of an edge and its relabelled edge
agree either directly or after swapping the two entries.  The latter choice
is the forced path reversal on a non-loop edge. -/
theorem cubicKernelOrderedEndpoints_coordinateRelabel
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    let H' := finiteMultiGraphCoordinateRelabel γ H
    let o := cubicKernelOrderedEndpoints H e
    let o' := cubicKernelOrderedEndpoints H' (γ.2 e)
    (γ.1 o.1 = o'.1 ∧ γ.1 o.2 = o'.2) ∨
      (γ.1 o.1 = o'.2 ∧ γ.1 o.2 = o'.1) := by
  dsimp only
  apply Sym2.eq_iff.mp
  calc
    s(γ.1 (cubicKernelOrderedEndpoints H e).1,
        γ.1 (cubicKernelOrderedEndpoints H e).2) =
        Sym2.map γ.1 (H.endpoints e) := by
      rw [← cubicKernelOrderedEndpoints_mk H e, Sym2.map_mk]
    _ = (finiteMultiGraphCoordinateRelabel γ H).endpoints (γ.2 e) := by
      simp
    _ = s((cubicKernelOrderedEndpoints
            (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).1,
          (cubicKernelOrderedEndpoints
            (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).2) :=
      (cubicKernelOrderedEndpoints_mk
        (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).symm

/-- Internal path coordinates transported along one relabelled edge.  The
path is kept in its original direction when the first ordered endpoint is
preserved, and reversed otherwise.  Thus non-loop orientation is not an
independent bit. -/
noncomputable def CubicKernelLengthProfile.coordinatePathIndexEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    Fin (L.length e).val ≃
      Fin ((L.coordinateRelabel γ).length (γ.2 e)).val :=
  let hlen : (L.length e).val =
      ((L.coordinateRelabel γ).length (γ.2 e)).val := by simp
  if _hfirst :
      γ.1 (cubicKernelOrderedEndpoints H e).1 =
        (cubicKernelOrderedEndpoints
          (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).1 then
    finCongr hlen
  else
    (Fin.revPerm : Equiv.Perm (Fin (L.length e).val)).trans
      (finCongr hlen)

/-- The complete equivalence of branch and internal subdivision slots
induced by simultaneous kernel-coordinate relabelling. -/
noncomputable def CubicKernelLengthProfile.coordinateRelabelSlotEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell) :
    CubicKernelSubdivisionSlot L ≃
      CubicKernelSubdivisionSlot (L.coordinateRelabel γ) :=
  Equiv.sumCongr γ.1
    (Equiv.sigmaCongr γ.2 (L.coordinatePathIndexEquiv γ))

@[simp]
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_inl
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (v : Fin (2 * ell)) :
    L.coordinateRelabelSlotEquiv γ (.inl v) = .inl (γ.1 v) :=
  rfl

@[simp]
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_inr
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) (i : Fin (L.length e).val) :
    L.coordinateRelabelSlotEquiv γ (.inr ⟨e, i⟩) =
      .inr ⟨γ.2 e, L.coordinatePathIndexEquiv γ e i⟩ :=
  rfl

/-- Transport a fully labelled subdivision datum.  Target slots are pulled
back through `coordinateRelabelSlotEquiv`, so all original labels in `Fin k`
remain literally unchanged. -/
noncomputable def CubicKernelSubdivisionDatum.coordinateRelabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ : CubicKernelCoordinatePerm ell) :
    CubicKernelSubdivisionDatum k ell
      (finiteMultiGraphCoordinateRelabel γ H) where
  profile := D.profile.coordinateRelabel γ
  labels := (D.profile.coordinateRelabelSlotEquiv γ).symm.trans D.labels

@[simp]
theorem CubicKernelSubdivisionDatum.coordinateRelabel_profile
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ : CubicKernelCoordinatePerm ell) :
    (D.coordinateRelabel γ).profile = D.profile.coordinateRelabel γ :=
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.coordinateRelabel_branchLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (v : Fin (2 * ell)) :
    (D.coordinateRelabel γ).branchLabel (γ.1 v) = D.branchLabel v := by
  change D.labels
      ((D.profile.coordinateRelabelSlotEquiv γ).symm (.inl (γ.1 v))) =
    D.labels (.inl v)
  apply congrArg D.labels
  apply (D.profile.coordinateRelabelSlotEquiv γ).injective
  exact (D.profile.coordinateRelabelSlotEquiv γ).apply_symm_apply _

@[simp]
theorem CubicKernelSubdivisionDatum.coordinateRelabel_pathLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) :
    (D.coordinateRelabel γ).pathLabel (γ.2 e)
        (D.profile.coordinatePathIndexEquiv γ e i) =
      D.pathLabel e i := by
  change D.labels
      ((D.profile.coordinateRelabelSlotEquiv γ).symm
        (.inr ⟨γ.2 e, D.profile.coordinatePathIndexEquiv γ e i⟩)) =
    D.labels (.inr ⟨e, i⟩)
  apply congrArg D.labels
  apply (D.profile.coordinateRelabelSlotEquiv γ).injective
  exact (D.profile.coordinateRelabelSlotEquiv γ).apply_symm_apply _

end PerronWright.GraphCore
