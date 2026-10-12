import PerronWright.Enumeration.VariableKernelCoordinateMultiplicity
import PerronWright.Enumeration.VariableKernelReconstruction
import Mathlib.Data.Fin.Rev

/-!
# Coordinate relabelling for variable-valence bounded kernels

This module supplies the exact simultaneous branch- and edge-coordinate
action for a bounded kernel.  Although the numbers of coordinates vary with
the kernel, relabelling preserves those numbers definitionally.  It therefore
acts inside one cardinality stratum and transports the kernel, every
admissible length profile, and every labelled subdivision datum together.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

namespace BoundedKernelCoordinatePerm

def refl {ell : ℕ} (K : LabelledBoundedKernel ell) :
    BoundedKernelCoordinatePerm K :=
  (Equiv.refl _, Equiv.refl _)

/-- First apply `gamma`, then `eta`, inside one cardinality stratum. -/
def trans {ell : ℕ} {K : LabelledBoundedKernel ell}
    (gamma eta : BoundedKernelCoordinatePerm K) :
    BoundedKernelCoordinatePerm K :=
  (gamma.1.trans eta.1, gamma.2.trans eta.2)

end BoundedKernelCoordinatePerm

/-- Relabel both coordinates of a finite multigraph of fixed displayed
sizes. -/
def boundedFiniteMultiGraphCoordinateRelabel
    {nv ne : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (H : PerronWright.FiniteMultiGraph nv ne) :
    PerronWright.FiniteMultiGraph nv ne where
  endpoints e := Sym2.map gamma.1 (H.endpoints (gamma.2.symm e))

@[simp] theorem boundedFiniteMultiGraphCoordinateRelabel_endpoints
    {nv ne : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (H : PerronWright.FiniteMultiGraph nv ne)
    (e : Fin ne) :
    (boundedFiniteMultiGraphCoordinateRelabel gamma H).endpoints e =
      Sym2.map gamma.1 (H.endpoints (gamma.2.symm e)) :=
  rfl

theorem boundedFiniteMultiGraph_incidence_map_equiv
    {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Sym2 (Fin n)) (v : Fin n) :
    PerronWright.FiniteMultiGraph.incidence (Sym2.map e p) (e v) =
      PerronWright.FiniteMultiGraph.incidence p v := by
  induction p using Sym2.inductionOn with
  | _ x y =>
      simp [PerronWright.FiniteMultiGraph.incidence_mk]

theorem boundedFiniteMultiGraphCoordinateRelabel_degree
    {nv ne : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (H : PerronWright.FiniteMultiGraph nv ne)
    (v : Fin nv) :
    (boundedFiniteMultiGraphCoordinateRelabel gamma H).degree (gamma.1 v) =
      H.degree v := by
  unfold PerronWright.FiniteMultiGraph.degree
  change
    (∑ e : Fin ne,
      PerronWright.FiniteMultiGraph.incidence
        (Sym2.map gamma.1 (H.endpoints (gamma.2.symm e)))
        (gamma.1 v)) = _
  calc
    _ = ∑ e : Fin ne,
        PerronWright.FiniteMultiGraph.incidence
          (H.endpoints (gamma.2.symm e)) v := by
      apply Finset.sum_congr rfl
      intro e _
      exact boundedFiniteMultiGraph_incidence_map_equiv
        gamma.1 (H.endpoints (gamma.2.symm e)) v
    _ = _ := (gamma.2.symm).sum_comp
      (fun e => PerronWright.FiniteMultiGraph.incidence (H.endpoints e) v)

def boundedFiniteMultiGraphSupportCoordinateRelabelIso
    {nv ne : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (H : PerronWright.FiniteMultiGraph nv ne) :
    finiteMultiGraphSupportGraph H ≃g
      finiteMultiGraphSupportGraph
        (boundedFiniteMultiGraphCoordinateRelabel gamma H) where
  __ := gamma.1
  map_rel_iff' := by
    intro u v
    simp only [finiteMultiGraphSupportGraph,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨⟨e, he⟩, huv⟩
      refine ⟨⟨gamma.2.symm e, ?_⟩, ?_⟩
      · apply Sym2.map.injective gamma.1.injective
        simpa only [boundedFiniteMultiGraphCoordinateRelabel_endpoints,
          Sym2.map_mk] using he
      · intro h
        exact huv (congrArg gamma.1 h)
    · rintro ⟨⟨e, he⟩, huv⟩
      refine ⟨⟨gamma.2 e, ?_⟩, gamma.1.injective.ne huv⟩
      simp only [boundedFiniteMultiGraphCoordinateRelabel_endpoints,
        Equiv.symm_apply_apply, he, Sym2.map_mk]

theorem boundedFiniteMultiGraphSupport_coordinateRelabel_connected_iff
    {nv ne : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (H : PerronWright.FiniteMultiGraph nv ne) :
    (finiteMultiGraphSupportGraph
        (boundedFiniteMultiGraphCoordinateRelabel gamma H)).Connected ↔
      (finiteMultiGraphSupportGraph H).Connected := by
  exact
    (boundedFiniteMultiGraphSupportCoordinateRelabelIso gamma H).connected_iff.symm

/-- Simultaneous relabelling of the endpoint table of a bounded kernel. -/
def LabelledBoundedKernel.coordinateRelabel
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    LabelledBoundedKernel ell where
  shape := ⟨K.shape.1, K.shape.2.1,
    fun e ↦ Sym2.map gamma.1
      (K.shape.2.2 (gamma.2.symm e))⟩
  minDegree := by
    intro v
    obtain ⟨u, rfl⟩ := gamma.1.surjective v
    change 3 ≤
      (boundedFiniteMultiGraphCoordinateRelabel gamma
        (boundedKernelFiniteMultiGraph K.shape)).degree (gamma.1 u)
    rw [boundedFiniteMultiGraphCoordinateRelabel_degree]
    exact K.minDegree u
  excess := K.excess

@[simp] theorem LabelledBoundedKernel.coordinateRelabel_vertexCount
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    (K.coordinateRelabel gamma).shape.1 = K.shape.1 :=
  rfl

@[simp] theorem LabelledBoundedKernel.coordinateRelabel_edgeCount
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    (K.coordinateRelabel gamma).shape.2.1 = K.shape.2.1 :=
  rfl

@[simp] theorem LabelledBoundedKernel.coordinateRelabel_endpoints
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    (K.coordinateRelabel gamma).shape.2.2 e =
      Sym2.map gamma.1 (K.shape.2.2 (gamma.2.symm e)) :=
  rfl

/-- Connected bounded kernels remain connected under coordinate relabelling. -/
def LabelledConnectedBoundedKernel.coordinateRelabel
    {ell : ℕ} (K : LabelledConnectedBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K.toLabelledBoundedKernel) :
    LabelledConnectedBoundedKernel ell where
  toLabelledBoundedKernel :=
    K.toLabelledBoundedKernel.coordinateRelabel gamma
  connected := by
    apply (boundedFiniteMultiGraphSupport_coordinateRelabel_connected_iff
      gamma
      (boundedKernelFiniteMultiGraph
        K.toLabelledBoundedKernel.shape)).2
    exact K.connected

/-- Transport an admissible length profile along simultaneous bounded-kernel
coordinates. -/
def BoundedKernelLengthProfile.coordinateRelabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    BoundedKernelLengthProfile k (K.coordinateRelabel gamma) where
  length e := L.length (gamma.2.symm e)
  totalLength := by
    change K.shape.1.val +
      ∑ e : Fin K.shape.2.1.val, (L.length (gamma.2.symm e)).val = k
    rw [(gamma.2.symm).sum_comp (fun e => (L.length e).val)]
    exact L.totalLength
  loopLength := by
    intro e he
    apply L.loopLength (gamma.2.symm e)
    apply (Sym2.isDiag_map gamma.1.injective).mp
    change (Sym2.map gamma.1
      (K.shape.2.2 (gamma.2.symm e))).IsDiag at he
    exact he
  directEndpointsInjective := by
    intro e f hef
    let e' : {a : Fin K.shape.2.1.val // (L.length a).val = 0} :=
      ⟨gamma.2.symm e.1, e.2⟩
    let f' : {a : Fin K.shape.2.1.val // (L.length a).val = 0} :=
      ⟨gamma.2.symm f.1, f.2⟩
    have hsource : K.shape.2.2 e'.1 = K.shape.2.2 f'.1 := by
      apply Sym2.map.injective gamma.1.injective
      change Sym2.map gamma.1 (K.shape.2.2 (gamma.2.symm e.1)) =
        Sym2.map gamma.1 (K.shape.2.2 (gamma.2.symm f.1)) at hef
      exact hef
    have hsub : e' = f' := L.directEndpointsInjective hsource
    apply Subtype.ext
    exact gamma.2.symm.injective (congrArg Subtype.val hsub)

@[simp] theorem BoundedKernelLengthProfile.coordinateRelabel_length
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    (L.coordinateRelabel gamma).length e = L.length (gamma.2.symm e) :=
  rfl

@[simp] theorem BoundedKernelLengthProfile.coordinateRelabel_length_apply
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    (L.coordinateRelabel gamma).length (gamma.2 e) = L.length e := by
  simp

def boundedKernelLoopEdgeCoordinateRelabelEquiv
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    BoundedKernelLoopEdge K ≃
      BoundedKernelLoopEdge (K.coordinateRelabel gamma) where
  toFun e := ⟨gamma.2 e.1, by
    rw [LabelledBoundedKernel.coordinateRelabel_endpoints]
    simp only [Equiv.symm_apply_apply]
    exact (Sym2.isDiag_map gamma.1.injective).2 e.2⟩
  invFun e := ⟨gamma.2.symm e.1, by
    apply (Sym2.isDiag_map gamma.1.injective).mp
    have he := e.2
    change (Sym2.map gamma.1
      (K.shape.2.2 (gamma.2.symm e.1))).IsDiag at he
    exact he⟩
  left_inv e := Subtype.ext (gamma.2.symm_apply_apply e.1)
  right_inv e := Subtype.ext (gamma.2.apply_symm_apply e.1)

theorem boundedKernelLoopEdge_card_coordinateRelabel
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    Fintype.card (BoundedKernelLoopEdge (K.coordinateRelabel gamma)) =
      Fintype.card (BoundedKernelLoopEdge K) := by
  exact Fintype.card_congr
    (boundedKernelLoopEdgeCoordinateRelabelEquiv K gamma).symm

/-- Canonical endpoint order is transported either directly or after the
single forced reversal. -/
theorem boundedKernelOrderedEndpoints_coordinateRelabel
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    let o := boundedKernelOrderedEndpoints K.shape e
    let o' := boundedKernelOrderedEndpoints
      (K.coordinateRelabel gamma).shape (gamma.2 e)
    (gamma.1 o.1 = o'.1 ∧ gamma.1 o.2 = o'.2) ∨
      (gamma.1 o.1 = o'.2 ∧ gamma.1 o.2 = o'.1) := by
  dsimp only
  apply Sym2.eq_iff.mp
  change
    Sym2.map gamma.1
        s((boundedKernelOrderedEndpoints K.shape e).1,
          (boundedKernelOrderedEndpoints K.shape e).2) =
      s((boundedKernelOrderedEndpoints
          (K.coordinateRelabel gamma).shape
          (gamma.2 e)).1,
        (boundedKernelOrderedEndpoints
          (K.coordinateRelabel gamma).shape
          (gamma.2 e)).2)
  rw [boundedKernelOrderedEndpoints_mk K e,
    boundedKernelOrderedEndpoints_mk (K.coordinateRelabel gamma) (gamma.2 e),
    LabelledBoundedKernel.coordinateRelabel_endpoints,
    Equiv.symm_apply_apply]

noncomputable def BoundedKernelLengthProfile.coordinatePathIndexEquiv
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    Fin (L.length e).val ≃
      Fin ((L.coordinateRelabel gamma).length (gamma.2 e)).val :=
  let hlen : (L.length e).val =
      ((L.coordinateRelabel gamma).length (gamma.2 e)).val := by simp
  if _hfirst :
      gamma.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          (K.coordinateRelabel gamma).shape (gamma.2 e)).1 then
    finCongr hlen
  else
    (Fin.revPerm : Equiv.Perm (Fin (L.length e).val)).trans
      (finCongr hlen)

noncomputable def BoundedKernelLengthProfile.coordinateRelabelSlotEquiv
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    BoundedKernelSubdivisionSlot L ≃
      BoundedKernelSubdivisionSlot (L.coordinateRelabel gamma) :=
  Equiv.sumCongr gamma.1
    (Equiv.sigmaCongr gamma.2 (L.coordinatePathIndexEquiv gamma))

@[simp] theorem BoundedKernelLengthProfile.coordinateRelabelSlotEquiv_inl
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (v : Fin K.shape.1.val) :
    L.coordinateRelabelSlotEquiv gamma (.inl v) = .inl (gamma.1 v) :=
  rfl

@[simp] theorem BoundedKernelLengthProfile.coordinateRelabelSlotEquiv_inr
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) (i : Fin (L.length e).val) :
    L.coordinateRelabelSlotEquiv gamma (.inr ⟨e, i⟩) =
      .inr ⟨gamma.2 e, L.coordinatePathIndexEquiv gamma e i⟩ :=
  rfl

/-- Relabel a complete subdivision datum while leaving its actual vertex
labels in `Fin k` fixed. -/
noncomputable def BoundedKernelSubdivisionDatum.coordinateRelabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    BoundedKernelSubdivisionDatum k (K.coordinateRelabel gamma) where
  profile := D.profile.coordinateRelabel gamma
  labels := (D.profile.coordinateRelabelSlotEquiv gamma).symm.trans D.labels

@[simp] theorem BoundedKernelSubdivisionDatum.coordinateRelabel_profile
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    (D.coordinateRelabel gamma).profile =
      D.profile.coordinateRelabel gamma :=
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.coordinateRelabel_branchLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (v : Fin K.shape.1.val) :
    (D.coordinateRelabel gamma).branchLabel (gamma.1 v) =
      D.branchLabel v := by
  change D.labels
      ((D.profile.coordinateRelabelSlotEquiv gamma).symm
        (.inl (gamma.1 v))) = D.labels (.inl v)
  apply congrArg D.labels
  apply (D.profile.coordinateRelabelSlotEquiv gamma).injective
  exact (D.profile.coordinateRelabelSlotEquiv gamma).apply_symm_apply _

@[simp] theorem BoundedKernelSubdivisionDatum.coordinateRelabel_pathLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) (i : Fin (D.profile.length e).val) :
    (D.coordinateRelabel gamma).pathLabel (gamma.2 e)
        (D.profile.coordinatePathIndexEquiv gamma e i) =
      D.pathLabel e i := by
  change D.labels
      ((D.profile.coordinateRelabelSlotEquiv gamma).symm
        (.inr ⟨gamma.2 e,
          D.profile.coordinatePathIndexEquiv gamma e i⟩)) =
    D.labels (.inr ⟨e, i⟩)
  apply congrArg D.labels
  apply (D.profile.coordinateRelabelSlotEquiv gamma).injective
  exact (D.profile.coordinateRelabelSlotEquiv gamma).apply_symm_apply _

end PerronWright.GraphCore
