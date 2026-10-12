import PerronWright.Enumeration.CubicKernelSubdivision
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Reconstruction from cubic-kernel subdivision data

This file constructs the labelled graph determined by admissible cubic-kernel
subdivision data.  A subdivision datum determines

* an ordered vertex sequence on every labelled kernel edge;
* one edge slot for every consecutive pair in those sequences;
* exactly `k + ell` edge slots;
* hence an edge-labelled `FiniteMultiGraph k (k + ell)`; and
* its ordinary simple support graph on the original labels `Fin k`.

Admissibility of the length profile makes the emitted endpoints loopless and
injective, so the reconstructed support has exactly `k + ell` edges.  The
subsequent inverse-classification layer supplies connectivity and the
minimum-degree-two characterization.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The vertex slot at position `i` along a subdivided kernel edge.  Position
zero is the first normalized branch endpoint, the final position is the
second endpoint, and the intermediate positions are the ordered internal
slots of the edge. -/
def CubicKernelSubdivisionDatum.pathSlot
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    Fin ((D.profile.length e).val + 2) →
      CubicKernelSubdivisionSlot D.profile :=
  fun i ↦
    if hzero : i.val = 0 then
      (.inl (cubicKernelOrderedEndpoints H e).1 :
        CubicKernelSubdivisionSlot D.profile)
    else if hlast : i.val = (D.profile.length e).val + 1 then
      (.inl (cubicKernelOrderedEndpoints H e).2 :
        CubicKernelSubdivisionSlot D.profile)
    else
      (.inr ⟨e, ⟨i.val - 1, by omega⟩⟩ :
        CubicKernelSubdivisionSlot D.profile)

/-- The original vertex label at one position of a subdivided kernel edge. -/
def CubicKernelSubdivisionDatum.pathVertex
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin ((D.profile.length e).val + 2)) : Fin k :=
  D.labels (D.pathSlot e i)

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_zero
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathSlot e 0 =
      (.inl (cubicKernelOrderedEndpoints H e).1 :
        CubicKernelSubdivisionSlot D.profile) := by
  simp [CubicKernelSubdivisionDatum.pathSlot]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_internal
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin (D.profile.length e).val) :
    D.pathSlot e (Fin.succ i.castSucc) =
      (.inr ⟨e, i⟩ : CubicKernelSubdivisionSlot D.profile) := by
  have hi : i.val ≠ (D.profile.length e).val :=
    Nat.ne_of_lt i.isLt
  simp [CubicKernelSubdivisionDatum.pathSlot, hi]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_last
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathSlot e (Fin.succ (Fin.last (D.profile.length e).val)) =
      (.inl (cubicKernelOrderedEndpoints H e).2 :
        CubicKernelSubdivisionSlot D.profile) := by
  simp [CubicKernelSubdivisionDatum.pathSlot]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_edgeZero_castSucc
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathSlot e
        (0 : Fin ((D.profile.length e).val + 1)).castSucc =
      (.inl (cubicKernelOrderedEndpoints H e).1 :
        CubicKernelSubdivisionSlot D.profile) := by
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).castSucc =
        (0 : Fin ((D.profile.length e).val + 2)) := rfl
  rw [hidx, D.pathSlot_zero]

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_edgeZero_succ_of_pos
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val) :
    D.pathSlot e (0 : Fin ((D.profile.length e).val + 1)).succ =
      (.inr ⟨e, (⟨0, he⟩ : Fin (D.profile.length e).val)⟩ :
        CubicKernelSubdivisionSlot D.profile) := by
  let i : Fin (D.profile.length e).val := ⟨0, he⟩
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).succ =
        Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx, D.pathSlot_internal]

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_edgeLast_castSucc_of_pos
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val) :
    D.pathSlot e (Fin.last (D.profile.length e).val).castSucc =
      (.inr ⟨e, (⟨(D.profile.length e).val - 1, by omega⟩ :
        Fin (D.profile.length e).val)⟩ :
        CubicKernelSubdivisionSlot D.profile) := by
  let i : Fin (D.profile.length e).val :=
    ⟨(D.profile.length e).val - 1, by omega⟩
  have hidx :
      (Fin.last (D.profile.length e).val).castSucc =
        Fin.succ i.castSucc := by
    apply Fin.ext
    simp [i]
    omega
  rw [hidx, D.pathSlot_internal]

@[simp]
theorem CubicKernelSubdivisionDatum.pathSlot_edgeLast_succ
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathSlot e (Fin.last (D.profile.length e).val).succ =
      (.inl (cubicKernelOrderedEndpoints H e).2 :
        CubicKernelSubdivisionSlot D.profile) := by
  exact D.pathSlot_last e

@[simp]
theorem CubicKernelSubdivisionDatum.pathVertex_zero
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathVertex e 0 =
      D.branchLabel (cubicKernelOrderedEndpoints H e).1 := by
  simp [CubicKernelSubdivisionDatum.pathVertex,
    CubicKernelSubdivisionDatum.branchLabel]

@[simp]
theorem CubicKernelSubdivisionDatum.pathVertex_internal
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin (D.profile.length e).val) :
    D.pathVertex e (Fin.succ i.castSucc) = D.pathLabel e i := by
  simp [CubicKernelSubdivisionDatum.pathVertex,
    CubicKernelSubdivisionDatum.pathLabel]

@[simp]
theorem CubicKernelSubdivisionDatum.pathVertex_last
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.pathVertex e (Fin.succ (Fin.last (D.profile.length e).val)) =
      D.branchLabel (cubicKernelOrderedEndpoints H e).2 := by
  unfold CubicKernelSubdivisionDatum.pathVertex
  rw [D.pathSlot_last e]
  rfl

/-- Equality of reconstructed path vertices is reduced exactly to equality
of their source subdivision slots.  This is the key local reduction for the
later looplessness and no-parallel-edge proofs. -/
theorem CubicKernelSubdivisionDatum.pathVertex_eq_iff_pathSlot_eq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {e f : Fin (3 * ell)}
    {i : Fin ((D.profile.length e).val + 2)}
    {j : Fin ((D.profile.length f).val + 2)} :
    D.pathVertex e i = D.pathVertex f j ↔
      D.pathSlot e i = D.pathSlot f j := by
  exact D.labels.injective.eq_iff

/-- Sorting and then forgetting the order recovers the original unordered
kernel endpoint pair. -/
@[simp]
theorem cubicKernelOrderedEndpoints_mk
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) :
    s((cubicKernelOrderedEndpoints H e).1,
      (cubicKernelOrderedEndpoints H e).2) = H.endpoints e := by
  change (Sym2.sortEquiv (α := Fin (2 * ell))).symm
      ((Sym2.sortEquiv (α := Fin (2 * ell))) (H.endpoints e)) =
    H.endpoints e
  exact (Sym2.sortEquiv (α := Fin (2 * ell))).symm_apply_apply
    (H.endpoints e)

/-- In the normalized endpoint order, a kernel edge is a loop exactly when
its two displayed endpoints agree. -/
theorem cubicKernelOrderedEndpoints_eq_iff_isDiag
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) :
    (cubicKernelOrderedEndpoints H e).1 =
        (cubicKernelOrderedEndpoints H e).2 ↔
      (H.endpoints e).IsDiag := by
  rw [← cubicKernelOrderedEndpoints_mk H e,
    Sym2.mk_isDiag_iff]

/-- One edge slot for every consecutive pair in every subdivided kernel
edge.  A kernel edge with `n` internal vertices contributes `n + 1` slots. -/
def CubicKernelSubdivisionEdgeSlot
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :=
  Σ e : Fin (3 * ell), Fin ((D.profile.length e).val + 1)

noncomputable instance cubicKernelSubdivisionEdgeSlotFintype
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Fintype (CubicKernelSubdivisionEdgeSlot D) := by
  unfold CubicKernelSubdivisionEdgeSlot
  infer_instance

/-- The unordered endpoint pair emitted by one consecutive path slot. -/
def CubicKernelSubdivisionDatum.subdivisionEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) : Sym2 (Fin k) :=
  s(D.pathVertex q.1 q.2.castSucc, D.pathVertex q.1 q.2.succ)

/-- The same reconstructed edge before the final relabelling by `D.labels`.
Keeping this source-slot edge visible separates the finite path combinatorics
from the (automatic) injectivity of the original-vertex labelling. -/
def CubicKernelSubdivisionDatum.subdivisionSlotEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    Sym2 (CubicKernelSubdivisionSlot D.profile) :=
  s(D.pathSlot q.1 q.2.castSucc, D.pathSlot q.1 q.2.succ)

theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_direct
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : (D.profile.length e).val = 0) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ =
      s((.inl (cubicKernelOrderedEndpoints H e).1 :
          CubicKernelSubdivisionSlot D.profile),
        (.inl (cubicKernelOrderedEndpoints H e).2 :
          CubicKernelSubdivisionSlot D.profile)) := by
  unfold CubicKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeZero_castSucc]
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).succ =
        (Fin.last (D.profile.length e).val).succ := by
    apply Fin.ext
    simp [he]
  rw [hidx, D.pathSlot_edgeLast_succ]
  rfl

theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_start
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ =
      s((.inl (cubicKernelOrderedEndpoints H e).1 :
          CubicKernelSubdivisionSlot D.profile),
        (.inr ⟨e, (⟨0, he⟩ : Fin (D.profile.length e).val)⟩ :
          CubicKernelSubdivisionSlot D.profile)) := by
  unfold CubicKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeZero_castSucc, D.pathSlot_edgeZero_succ_of_pos e he]
  rfl

theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionSlotEdge
        ⟨e, Fin.last (D.profile.length e).val⟩ =
      s((.inr ⟨e, (⟨(D.profile.length e).val - 1, by omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          CubicKernelSubdivisionSlot D.profile),
        (.inl (cubicKernelOrderedEndpoints H e).2 :
          CubicKernelSubdivisionSlot D.profile)) := by
  unfold CubicKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeLast_castSucc_of_pos e he,
    D.pathSlot_edgeLast_succ]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.subdivisionEdge_eq_map_slotEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    D.subdivisionEdge q = Sym2.map D.labels (D.subdivisionSlotEdge q) := by
  rfl

/-- Relabelling cannot create or remove a diagonal edge.  Thus looplessness
of the reconstructed graph is exactly the elementary assertion that two
consecutive source slots along a subdivided kernel edge are distinct. -/
theorem CubicKernelSubdivisionDatum.subdivisionEdge_not_isDiag_iff
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    ¬(D.subdivisionEdge q).IsDiag ↔
      D.pathSlot q.1 q.2.castSucc ≠ D.pathSlot q.1 q.2.succ := by
  rw [D.subdivisionEdge_eq_map_slotEdge,
    Sym2.isDiag_map D.labels.injective]
  rfl

/-- Likewise, injectivity of the emitted edge table is exactly injectivity
before applying the global slot labelling equivalence. -/
theorem CubicKernelSubdivisionDatum.subdivisionEdge_injective_iff_slotEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective D.subdivisionEdge ↔
      Function.Injective D.subdivisionSlotEdge := by
  constructor
  · intro hinj q r hqr
    apply hinj
    simpa only [D.subdivisionEdge_eq_map_slotEdge] using congrArg (Sym2.map D.labels) hqr
  · intro hinj q r hqr
    apply hinj
    apply Sym2.map.injective D.labels.injective
    simpa only [D.subdivisionEdge_eq_map_slotEdge] using hqr

/-- The source-slot edge map is already injective on the zero-length kernel
edges.  This is exactly the `directEndpointsInjective` clause of an
admissible profile, transported through the canonical ordered endpoints. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_direct
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective
      (fun e : {e : Fin (3 * ell) // (D.profile.length e).val = 0} ↦
        D.subdivisionSlotEdge
          ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) := by
  intro e f hef
  change D.subdivisionSlotEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, (0 : Fin ((D.profile.length f.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_direct e.1 e.2,
    D.subdivisionSlotEdge_direct f.1 f.2] at hef
  have hordered :
      s((cubicKernelOrderedEndpoints H e.1).1,
          (cubicKernelOrderedEndpoints H e.1).2) =
        s((cubicKernelOrderedEndpoints H f.1).1,
          (cubicKernelOrderedEndpoints H f.1).2) := by
    rcases Sym2.eq_iff.mp hef with hdir | hswap
    · exact Sym2.eq_iff.mpr (Or.inl
        ⟨Sum.inl.inj hdir.1, Sum.inl.inj hdir.2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr
        ⟨Sum.inl.inj hswap.1, Sum.inl.inj hswap.2⟩)
  exact D.profile.directEndpointsInjective (by
    simpa only [cubicKernelOrderedEndpoints_mk] using hordered)

/-- Start slots of positive-length kernel paths are distinguished by their
first internal slot. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_start
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective
      (fun e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val} ↦
        D.subdivisionSlotEdge
          ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) := by
  intro e f hef
  let ie : Fin (D.profile.length e.1).val := ⟨0, e.2⟩
  let jf : Fin (D.profile.length f.1).val := ⟨0, f.2⟩
  change D.subdivisionSlotEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, (0 : Fin ((D.profile.length f.1).val + 1))⟩ :
        CubicKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_start e.1 e.2,
    D.subdivisionSlotEdge_start f.1 f.2] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr.inj hdir.2)
  · cases hswap.1

/-- A start slot can never equal an end slot.  Equality would force the two
internal slots to belong to the same kernel edge and simultaneously force
that edge to have exactly one internal vertex and coincident branch
endpoints.  This is precisely the forbidden length-one loop. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_start_ne_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e f : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val)
    (hf : 0 < (D.profile.length f).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge
        ⟨f, Fin.last (D.profile.length f).val⟩ := by
  let ie : Fin (D.profile.length e).val := ⟨0, he⟩
  let jf : Fin (D.profile.length f).val :=
    ⟨(D.profile.length f).val - 1, by omega⟩
  intro hef
  rw [D.subdivisionSlotEdge_start e he,
    D.subdivisionSlotEdge_end f hf] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · have hbranch :
        (cubicKernelOrderedEndpoints H e).1 =
          (cubicKernelOrderedEndpoints H f).2 :=
        Sum.inl.inj hswap.1
    have hinternal :
        (⟨e, ie⟩ : Σ a, Fin (D.profile.length a).val) = ⟨f, jf⟩ :=
      Sum.inr.inj hswap.2
    have hef' : e = f := congrArg Sigma.fst hinternal
    subst f
    have hij : ie = jf :=
      eq_of_heq (Sigma.mk.inj_iff.mp hinternal).2
    have hlength : (D.profile.length e).val = 1 := by
      have hval := congrArg Fin.val hij
      simp [ie, jf] at hval
      omega
    have hloop : (H.endpoints e).IsDiag :=
      (cubicKernelOrderedEndpoints_eq_iff_isDiag H e).1 hbranch
    have hge := D.profile.loopLength e hloop
    omega

/-- End slots of positive-length kernel paths are distinguished by their
last internal slot. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective
      (fun e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val} ↦
        D.subdivisionSlotEdge
          ⟨e.1, Fin.last (D.profile.length e.1).val⟩) := by
  intro e f hef
  let ie : Fin (D.profile.length e.1).val :=
    ⟨(D.profile.length e.1).val - 1, by omega⟩
  let jf : Fin (D.profile.length f.1).val :=
    ⟨(D.profile.length f.1).val - 1, by omega⟩
  change D.subdivisionSlotEdge
      (⟨e.1, Fin.last (D.profile.length e.1).val⟩ :
        CubicKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, Fin.last (D.profile.length f.1).val⟩ :
        CubicKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_end e.1 e.2,
    D.subdivisionSlotEdge_end f.1 f.2] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr.inj hdir.1)
  · cases hswap.1

/-- Parameters for the genuinely internal consecutive pairs on all kernel
paths.  An edge with `n` internal vertices has `n - 1` such pairs. -/
def CubicKernelSubdivisionMiddleSlot
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :=
  Σ e : Fin (3 * ell), Fin ((D.profile.length e).val - 1)

/-- The edge slot represented by an internal-pair parameter. -/
def CubicKernelSubdivisionDatum.middleEdgeSlot
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (p : CubicKernelSubdivisionMiddleSlot D) :
    CubicKernelSubdivisionEdgeSlot D :=
  ⟨p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩⟩

theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin ((D.profile.length e).val - 1)) :
    D.subdivisionSlotEdge
        (D.middleEdgeSlot (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)) =
      s((.inr ⟨e, (⟨i.val, by have hi := i.isLt; omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          CubicKernelSubdivisionSlot D.profile),
        (.inr ⟨e, (⟨i.val + 1, by have hi := i.isLt; omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          CubicKernelSubdivisionSlot D.profile)) := by
  let i₀ : Fin (D.profile.length e).val :=
    ⟨i.val, by have hi := i.isLt; omega⟩
  let i₁ : Fin (D.profile.length e).val :=
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have hcast :
      (D.middleEdgeSlot
        (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)).2.castSucc =
        Fin.succ i₀.castSucc := by
    apply Fin.ext
    rfl
  have hsucc :
      (D.middleEdgeSlot
        (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)).2.succ =
        Fin.succ i₁.castSucc := by
    apply Fin.ext
    rfl
  unfold CubicKernelSubdivisionDatum.subdivisionSlotEdge
  simp only [CubicKernelSubdivisionDatum.middleEdgeSlot] at hcast hsucc ⊢
  rw [hcast, hsucc, D.pathSlot_internal e i₀,
    D.pathSlot_internal e i₁]
  rfl

/-- Internal consecutive pairs are injectively indexed: in the forward
orientation equality identifies both the kernel edge and the lower internal
index, while the reversed orientation would force simultaneously
`i = j + 1` and `i + 1 = j`. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective
      (fun p : CubicKernelSubdivisionMiddleSlot D ↦
        D.subdivisionSlotEdge (D.middleEdgeSlot p)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ hij
  let ie₀ : Fin (D.profile.length e).val :=
    ⟨i.val, by have := i.isLt; omega⟩
  let ie₁ : Fin (D.profile.length e).val :=
    ⟨i.val + 1, by have := i.isLt; omega⟩
  let jf₀ : Fin (D.profile.length f).val :=
    ⟨j.val, by have := j.isLt; omega⟩
  let jf₁ : Fin (D.profile.length f).val :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  change D.subdivisionSlotEdge
      (D.middleEdgeSlot
        (⟨e, i⟩ : CubicKernelSubdivisionMiddleSlot D)) =
    D.subdivisionSlotEdge
      (D.middleEdgeSlot
        (⟨f, j⟩ : CubicKernelSubdivisionMiddleSlot D)) at hij
  rw [D.subdivisionSlotEdge_middle e i,
    D.subdivisionSlotEdge_middle f j] at hij
  rcases Sym2.eq_iff.mp hij with hdir | hrev
  · have h₀ := Sum.inr.inj hdir.1
    have hef : e = f := congrArg Sigma.fst h₀
    subst f
    have hii : ie₀ = jf₀ :=
      eq_of_heq (Sigma.mk.inj_iff.mp h₀).2
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      simpa only [ie₀, jf₀] using congrArg Fin.val hii
  · have h₀ := Sum.inr.inj hrev.1
    have h₁ := Sum.inr.inj hrev.2
    have hef : e = f := congrArg Sigma.fst h₀
    subst f
    have hi₀ : ie₀ = jf₁ :=
      eq_of_heq (Sigma.mk.inj_iff.mp h₀).2
    have hi₁ : ie₁ = jf₀ :=
      eq_of_heq (Sigma.mk.inj_iff.mp h₁).2
    have hv₀ := congrArg Fin.val hi₀
    have hv₁ := congrArg Fin.val hi₁
    simp [ie₀, ie₁, jf₀, jf₁] at hv₀ hv₁
    omega

/-- Every reconstructed edge slot is uniquely of one of the four geometric
types used above: a direct kernel edge, the first or last edge of a
positive-length path, or a genuinely internal consecutive pair.  The
statement only asserts exhaustiveness; pairwise disjointness is supplied by
the source-slot constructors and `subdivisionSlotEdge_start_ne_end`. -/
theorem CubicKernelSubdivisionDatum.edgeSlot_classification
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    (∃ e : {e : Fin (3 * ell) // (D.profile.length e).val = 0},
      q = ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) ∨
    (∃ e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val},
      q = ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) ∨
    (∃ e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val},
      q = ⟨e.1, Fin.last (D.profile.length e.1).val⟩) ∨
    ∃ p : CubicKernelSubdivisionMiddleSlot D,
      q = D.middleEdgeSlot p := by
  rcases q with ⟨e, i⟩
  by_cases hzero : (D.profile.length e).val = 0
  · left
    refine ⟨⟨e, hzero⟩, ?_⟩
    have hiVal : i.val = 0 := by
      have hi := i.isLt
      omega
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      exact hiVal
  · have hpos : 0 < (D.profile.length e).val := Nat.pos_of_ne_zero hzero
    by_cases hi_zero : i.val = 0
    · right; left
      refine ⟨⟨e, hpos⟩, ?_⟩
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        simpa using hi_zero
    · by_cases hi_last : i.val = (D.profile.length e).val
      · right; right; left
        refine ⟨⟨e, hpos⟩, ?_⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          simpa using hi_last
      · right; right; right
        let p : Fin ((D.profile.length e).val - 1) :=
          ⟨i.val - 1, by omega⟩
        refine ⟨⟨e, p⟩, ?_⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          simp [CubicKernelSubdivisionDatum.middleEdgeSlot, p]
          omega

/-- A zero-length (branch--branch) edge cannot coincide with the first edge
of a positive-length subdivided path. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_start
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e f : Fin (3 * ell))
    (he : (D.profile.length e).val = 0)
    (hf : 0 < (D.profile.length f).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge
        ⟨f, (0 : Fin ((D.profile.length f).val + 1))⟩ := by
  let jf : Fin (D.profile.length f).val := ⟨0, hf⟩
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_start f hf] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.2
  · cases hswap.1

/-- A zero-length (branch--branch) edge cannot coincide with the last edge
of a positive-length subdivided path. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e f : Fin (3 * ell))
    (he : (D.profile.length e).val = 0)
    (hf : 0 < (D.profile.length f).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge
        ⟨f, Fin.last (D.profile.length f).val⟩ := by
  let jf : Fin (D.profile.length f).val :=
    ⟨(D.profile.length f).val - 1, by omega⟩
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_end f hf] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.2

/-- A zero-length (branch--branch) edge cannot coincide with an internal
edge (internal--internal) of a subdivided path. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : (D.profile.length e).val = 0)
    (p : CubicKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  let jf₀ : Fin (D.profile.length f).val :=
    ⟨j.val, by have := j.isLt; omega⟩
  let jf₁ : Fin (D.profile.length f).val :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.1

/-- The first edge (branch--internal) of a positive-length path cannot
coincide with a genuinely internal edge. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_start_ne_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val)
    (p : CubicKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  let ie : Fin (D.profile.length e).val := ⟨0, he⟩
  let jf₀ : Fin (D.profile.length f).val :=
    ⟨j.val, by have := j.isLt; omega⟩
  let jf₁ : Fin (D.profile.length f).val :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  intro hef
  rw [D.subdivisionSlotEdge_start e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.1

/-- The last edge (internal--branch) of a positive-length path cannot
coincide with a genuinely internal edge. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_end_ne_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (he : 0 < (D.profile.length e).val)
    (p : CubicKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, Fin.last (D.profile.length e).val⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  let ie : Fin (D.profile.length e).val :=
    ⟨(D.profile.length e).val - 1, by omega⟩
  let jf₀ : Fin (D.profile.length f).val :=
    ⟨j.val, by have := j.isLt; omega⟩
  let jf₁ : Fin (D.profile.length f).val :=
    ⟨j.val + 1, by have := j.isLt; omega⟩
  intro hef
  rw [D.subdivisionSlotEdge_end e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.2
  · cases hswap.2

/-- The complete source-slot endpoint table is injective.  The proof is a
finite case split over the four exhaustive geometric slot types. -/
theorem CubicKernelSubdivisionDatum.subdivisionSlotEdge_injective
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective D.subdivisionSlotEdge := by
  intro q r hqr
  rcases D.edgeSlot_classification q with hq | hq | hq | hq <;>
    rcases D.edgeSlot_classification r with hr | hr | hr | hr
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    have hef := D.subdivisionSlotEdge_injective_on_direct hqr
    cases hef
    rfl
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_start e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_end e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨p, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_middle e.1 e.2 p hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_start f.1 e.1 f.2 e.2 hqr.symm)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    have hef := D.subdivisionSlotEdge_injective_on_start hqr
    cases hef
    rfl
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_start_ne_end e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨p, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_start_ne_middle e.1 e.2 p hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_end f.1 e.1 f.2 e.2 hqr.symm)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_start_ne_end f.1 e.1 f.2 e.2 hqr.symm)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    have hef := D.subdivisionSlotEdge_injective_on_end hqr
    cases hef
    rfl
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨p, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_end_ne_middle e.1 e.2 p hqr)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_start_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_end_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨q, rfl⟩
    have hpq := D.subdivisionSlotEdge_injective_on_middle hqr
    cases hpq
    rfl

/-- Relabelling all source slots by the global slot equivalence preserves
the preceding injectivity. -/
theorem CubicKernelSubdivisionDatum.subdivisionEdge_injective
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective D.subdivisionEdge :=
  (D.subdivisionEdge_injective_iff_slotEdge).2
    D.subdivisionSlotEdge_injective

/-- Consecutive positions on every admissibly subdivided kernel edge are
distinct.  The only endpoint-endpoint case is a zero-length kernel edge;
`loopLength` rules out its being a loop.  Every other consecutive pair
contains an internal slot, and the two sum constructors (or two consecutive
internal indices) separate its endpoints. -/
theorem CubicKernelSubdivisionDatum.pathSlot_castSucc_ne_succ
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin ((D.profile.length e).val + 1)) :
    D.pathSlot e i.castSucc ≠ D.pathSlot e i.succ := by
  by_cases hi0 : i.val = 0
  · have hi : i = (0 : Fin ((D.profile.length e).val + 1)) :=
      Fin.ext hi0
    subst i
    by_cases he : (D.profile.length e).val = 0
    · rw [D.pathSlot_edgeZero_castSucc]
      have hlast :
          (0 : Fin ((D.profile.length e).val + 1)).succ =
            (Fin.last (D.profile.length e).val).succ := by
        apply Fin.ext
        simp [he]
      rw [hlast, D.pathSlot_edgeLast_succ]
      intro h
      have hendpoints :
          (cubicKernelOrderedEndpoints H e).1 =
            (cubicKernelOrderedEndpoints H e).2 :=
        Sum.inl.inj h
      have hloop : (H.endpoints e).IsDiag :=
        (cubicKernelOrderedEndpoints_eq_iff_isDiag H e).1 hendpoints
      have hlength := D.profile.loopLength e hloop
      omega
    · have hepos : 0 < (D.profile.length e).val := by omega
      rw [D.pathSlot_edgeZero_castSucc,
        D.pathSlot_edgeZero_succ_of_pos e hepos]
      intro h
      injection h
  · by_cases hilast : i.val = (D.profile.length e).val
    · have hepos : 0 < (D.profile.length e).val := by omega
      have hi : i = Fin.last (D.profile.length e).val := by
        apply Fin.ext
        simpa using hilast
      subst i
      rw [D.pathSlot_edgeLast_castSucc_of_pos e hepos,
        D.pathSlot_edgeLast_succ]
      intro h
      injection h
    · have hilt : i.val < (D.profile.length e).val := by
        have hiLt := i.isLt
        omega
      let i₀ : Fin (D.profile.length e).val :=
        ⟨i.val - 1, by omega⟩
      let i₁ : Fin (D.profile.length e).val :=
        ⟨i.val, hilt⟩
      have hcast : i.castSucc = Fin.succ i₀.castSucc := by
        apply Fin.ext
        simp [i₀]
        omega
      have hsucc : i.succ = Fin.succ i₁.castSucc := by
        apply Fin.ext
        simp [i₁]
      rw [hcast, hsucc, D.pathSlot_internal e i₀,
        D.pathSlot_internal e i₁]
      intro h
      have hsig := Sum.inr.inj h
      have hfin : i₀ = i₁ :=
        eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
      have hval := congrArg Fin.val hfin
      simp [i₀, i₁] at hval
      omega

/-- No reconstructed edge is diagonal. -/
theorem CubicKernelSubdivisionDatum.subdivisionEdge_not_isDiag
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    ¬(D.subdivisionEdge q).IsDiag :=
  (D.subdivisionEdge_not_isDiag_iff q).2
    (D.pathSlot_castSucc_ne_succ q.1 q.2)

/-- The edge-slot count has the exact fixed-surplus value.  This uses only
the total-length equation in the profile; no graph quotient or injectivity
argument is hidden in the count. -/
theorem cubicKernelSubdivisionEdgeSlot_card
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Fintype.card (CubicKernelSubdivisionEdgeSlot D) = k + ell := by
  change Fintype.card
      (Σ e : Fin (3 * ell), Fin ((D.profile.length e).val + 1)) =
    k + ell
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have htotal := D.profile.totalLength
  omega

/-- A canonical enumeration of all reconstructed edge slots by the desired
edge-label type `Fin (k + ell)`. -/
noncomputable def CubicKernelSubdivisionDatum.edgeSlotEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    CubicKernelSubdivisionEdgeSlot D ≃ Fin (k + ell) :=
  Fintype.equivFinOfCardEq (cubicKernelSubdivisionEdgeSlot_card D)

/-- The edge-labelled multigraph reconstructed in one direction from a
fixed cubic kernel, an admissible length profile, and a labelling of every
subdivision slot. -/
noncomputable def CubicKernelSubdivisionDatum.reconstructedMultiGraph
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    PerronWright.FiniteMultiGraph k (k + ell) where
  endpoints j := D.subdivisionEdge (D.edgeSlotEquiv.symm j)

@[simp]
theorem CubicKernelSubdivisionDatum.reconstructedMultiGraph_endpoints
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    D.reconstructedMultiGraph.endpoints (D.edgeSlotEquiv q) =
      D.subdivisionEdge q := by
  simp [CubicKernelSubdivisionDatum.reconstructedMultiGraph]

/-- Forget edge labels, loops, and parallel multiplicity to obtain the
ordinary labelled graph supported by the reconstructed endpoint table. -/
noncomputable def CubicKernelSubdivisionDatum.reconstructedGraph
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) : SimpleGraph (Fin k) :=
  finiteMultiGraphSupportGraph D.reconstructedMultiGraph

/-- Exact adjacency interface for the one-way reconstruction.  The explicit
inequality is precisely the diagonal deletion performed by
`SimpleGraph.fromEdgeSet`; `subdivisionEdge_not_isDiag` below proves it
automatically for every emitted consecutive pair. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_adj_iff
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (x y : Fin k) :
    D.reconstructedGraph.Adj x y ↔
      (∃ q : CubicKernelSubdivisionEdgeSlot D,
        D.subdivisionEdge q = s(x, y)) ∧ x ≠ y := by
  rw [CubicKernelSubdivisionDatum.reconstructedGraph,
    finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨j, hj⟩, hxy⟩
    refine ⟨⟨D.edgeSlotEquiv.symm j, ?_⟩, hxy⟩
    simpa [CubicKernelSubdivisionDatum.reconstructedMultiGraph] using hj
  · rintro ⟨⟨q, hq⟩, hxy⟩
    refine ⟨⟨D.edgeSlotEquiv q, ?_⟩, hxy⟩
    simpa [CubicKernelSubdivisionDatum.reconstructedMultiGraph] using hq

/-- Every non-diagonal emitted consecutive pair is an actual edge of the
reconstructed simple graph. -/
theorem CubicKernelSubdivisionDatum.pathEdge_adj
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D)
    (hne : D.pathVertex q.1 q.2.castSucc ≠
      D.pathVertex q.1 q.2.succ) :
    D.reconstructedGraph.Adj
      (D.pathVertex q.1 q.2.castSucc)
      (D.pathVertex q.1 q.2.succ) := by
  apply (D.reconstructedGraph_adj_iff _ _).2
  exact ⟨⟨q, rfl⟩, hne⟩

/-- Once consecutive source slots are known to be distinct, the edge finset
is literally the image of the finite edge-slot type.  This is the exact
bridge from the local path argument to ordinary simple-graph counting. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_edgeFinset_eq_image
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hdiag : ∀ q : CubicKernelSubdivisionEdgeSlot D,
      ¬(D.subdivisionEdge q).IsDiag) :
    D.reconstructedGraph.edgeFinset =
      Finset.univ.image D.subdivisionEdge := by
  ext z
  induction z using Sym2.ind with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        D.reconstructedGraph_adj_iff]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨q, hq⟩, _⟩
        exact ⟨q, hq⟩
      · rintro ⟨q, hq⟩
        refine ⟨⟨q, hq⟩, ?_⟩
        intro hxy
        apply hdiag q
        rw [hq, Sym2.mk_isDiag_iff]
        exact hxy

/-- The preceding image description is unconditional for an admissible
length profile, because `loopLength` already rules out every diagonal
consecutive pair. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_edgeFinset_eq_image'
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    D.reconstructedGraph.edgeFinset =
      Finset.univ.image D.subdivisionEdge :=
  D.reconstructedGraph_edgeFinset_eq_image D.subdivisionEdge_not_isDiag

/-- The desired exact support-edge count follows formally from the two local
facts: no emitted edge is diagonal and no two edge slots emit the same
unordered pair.  In particular, no further graph-enumeration argument is
needed after those path facts have been established. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_edgeFinset_card
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hdiag : ∀ q : CubicKernelSubdivisionEdgeSlot D,
      ¬(D.subdivisionEdge q).IsDiag)
    (hinj : Function.Injective D.subdivisionEdge) :
    D.reconstructedGraph.edgeFinset.card = k + ell := by
  rw [D.reconstructedGraph_edgeFinset_eq_image hdiag,
    Finset.card_image_of_injective _ hinj, Finset.card_univ,
    cubicKernelSubdivisionEdgeSlot_card D]

/-- An admissible cubic-kernel subdivision always has exactly `k + ell`
distinct support edges.  Both hypotheses of the preceding counting lemma
are consequences of the length-profile admissibility clauses. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_edgeFinset_card_eq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    D.reconstructedGraph.edgeFinset.card = k + ell :=
  D.reconstructedGraph_edgeFinset_card
    D.subdivisionEdge_not_isDiag D.subdivisionEdge_injective


end PerronWright.GraphCore

