import PerronWright.Enumeration.VariableKernelSubdivisionData
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Reconstruction of variable-valence kernel subdivisions

This file begins the genuine inverse construction for bounded noncubic
kernels.  It is the variable-valence counterpart of
`CubicKernelReconstruction`: every kernel edge is expanded into its ordered
chain of internal slots, and the resulting consecutive pairs are transported
by the original-label equivalence.
-/

open PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

/-- Position `i` on one subdivided bounded-kernel edge. -/
def BoundedKernelSubdivisionDatum.pathSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    Fin ((D.profile.length e).val + 2) →
      BoundedKernelSubdivisionSlot D.profile :=
  fun i ↦
    if hzero : i.val = 0 then
      (.inl (boundedKernelOrderedEndpoints K.shape e).1 :
        BoundedKernelSubdivisionSlot D.profile)
    else if hlast : i.val = (D.profile.length e).val + 1 then
      (.inl (boundedKernelOrderedEndpoints K.shape e).2 :
        BoundedKernelSubdivisionSlot D.profile)
    else
      (.inr ⟨e, ⟨i.val - 1, by omega⟩⟩ :
        BoundedKernelSubdivisionSlot D.profile)

/-- Original vertex label at one position of a subdivided edge. -/
def BoundedKernelSubdivisionDatum.pathVertex
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin ((D.profile.length e).val + 2)) : Fin k :=
  D.labels (D.pathSlot e i)

/-- The original label attached to a branch slot. -/
def BoundedKernelSubdivisionDatum.branchLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (v : Fin K.shape.1.val) : Fin k :=
  D.labels (.inl v)

/-- The original label attached to an internal path slot. -/
def BoundedKernelSubdivisionDatum.pathLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) (i : Fin (D.profile.length e).val) : Fin k :=
  D.labels (.inr ⟨e, i⟩)

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_zero
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathSlot e 0 =
      (.inl (boundedKernelOrderedEndpoints K.shape e).1 :
        BoundedKernelSubdivisionSlot D.profile) := by
  simp [BoundedKernelSubdivisionDatum.pathSlot]
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_internal
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    D.pathSlot e (Fin.succ i.castSucc) =
      (.inr ⟨e, i⟩ : BoundedKernelSubdivisionSlot D.profile) := by
  have hi : i.val ≠ (D.profile.length e).val := Nat.ne_of_lt i.isLt
  simp [BoundedKernelSubdivisionDatum.pathSlot, hi]
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_last
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathSlot e (Fin.succ (Fin.last (D.profile.length e).val)) =
      (.inl (boundedKernelOrderedEndpoints K.shape e).2 :
        BoundedKernelSubdivisionSlot D.profile) := by
  simp [BoundedKernelSubdivisionDatum.pathSlot]
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_edgeZero_castSucc
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathSlot e
        (0 : Fin ((D.profile.length e).val + 1)).castSucc =
      (.inl (boundedKernelOrderedEndpoints K.shape e).1 :
        BoundedKernelSubdivisionSlot D.profile) := by
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).castSucc =
        (0 : Fin ((D.profile.length e).val + 2)) := rfl
  rw [hidx, D.pathSlot_zero]

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_edgeZero_succ_of_pos
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.pathSlot e (0 : Fin ((D.profile.length e).val + 1)).succ =
      (.inr ⟨e, (⟨0, he⟩ : Fin (D.profile.length e).val)⟩ :
        BoundedKernelSubdivisionSlot D.profile) := by
  let i : Fin (D.profile.length e).val := ⟨0, he⟩
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).succ =
        Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx, D.pathSlot_internal]

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_edgeLast_castSucc_of_pos
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.pathSlot e (Fin.last (D.profile.length e).val).castSucc =
      (.inr ⟨e, (⟨(D.profile.length e).val - 1, by omega⟩ :
        Fin (D.profile.length e).val)⟩ :
          BoundedKernelSubdivisionSlot D.profile) := by
  let i : Fin (D.profile.length e).val :=
    ⟨(D.profile.length e).val - 1, by omega⟩
  have hidx :
      (Fin.last (D.profile.length e).val).castSucc =
        Fin.succ i.castSucc := by
    apply Fin.ext
    simp [i]
    omega
  rw [hidx, D.pathSlot_internal]

@[simp] theorem BoundedKernelSubdivisionDatum.pathSlot_edgeLast_succ
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathSlot e (Fin.last (D.profile.length e).val).succ =
      (.inl (boundedKernelOrderedEndpoints K.shape e).2 :
        BoundedKernelSubdivisionSlot D.profile) := by
  exact D.pathSlot_last e

@[simp] theorem BoundedKernelSubdivisionDatum.pathVertex_zero
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathVertex e 0 =
      D.labels (.inl (boundedKernelOrderedEndpoints K.shape e).1) := by
  simp [BoundedKernelSubdivisionDatum.pathVertex]

@[simp] theorem BoundedKernelSubdivisionDatum.pathVertex_internal
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    D.pathVertex e (Fin.succ i.castSucc) = D.labels (.inr ⟨e, i⟩) := by
  simp [BoundedKernelSubdivisionDatum.pathVertex]

@[simp] theorem BoundedKernelSubdivisionDatum.pathVertex_last
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val) :
    D.pathVertex e (Fin.succ (Fin.last (D.profile.length e).val)) =
      D.labels (.inl (boundedKernelOrderedEndpoints K.shape e).2) := by
  unfold BoundedKernelSubdivisionDatum.pathVertex
  rw [D.pathSlot_last]

theorem BoundedKernelSubdivisionDatum.pathVertex_eq_iff_pathSlot_eq
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {e f : Fin K.shape.2.1.val}
    {i : Fin ((D.profile.length e).val + 2)}
    {j : Fin ((D.profile.length f).val + 2)} :
    D.pathVertex e i = D.pathVertex f j ↔
      D.pathSlot e i = D.pathSlot f j :=
  D.labels.injective.eq_iff

/-- Sorting and forgetting the order recovers the bounded table endpoint. -/
@[simp] theorem boundedKernelOrderedEndpoints_mk
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    s((boundedKernelOrderedEndpoints K.shape e).1,
      (boundedKernelOrderedEndpoints K.shape e).2) = K.shape.2.2 e := by
  change (Sym2.sortEquiv (α := Fin K.shape.1.val)).symm
      ((Sym2.sortEquiv (α := Fin K.shape.1.val)) (K.shape.2.2 e)) =
    K.shape.2.2 e
  exact (Sym2.sortEquiv (α := Fin K.shape.1.val)).symm_apply_apply
    (K.shape.2.2 e)

/-- The displayed bounded endpoints agree exactly for loop labels. -/
theorem boundedKernelOrderedEndpoints_eq_iff_isDiag
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints K.shape e).2 ↔
      (K.shape.2.2 e).IsDiag := by
  rw [← boundedKernelOrderedEndpoints_mk K e, Sym2.mk_isDiag_iff]

/-- One edge slot for every consecutive pair on every subdivided kernel
edge. -/
def BoundedKernelSubdivisionEdgeSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :=
  Σ e : Fin K.shape.2.1.val, Fin ((D.profile.length e).val + 1)

noncomputable instance boundedKernelSubdivisionEdgeSlotFintype
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Fintype (BoundedKernelSubdivisionEdgeSlot D) := by
  unfold BoundedKernelSubdivisionEdgeSlot
  infer_instance

/-- Unordered original-label pair emitted by one consecutive slot. -/
def BoundedKernelSubdivisionDatum.subdivisionEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) : Sym2 (Fin k) :=
  s(D.pathVertex q.1 q.2.castSucc, D.pathVertex q.1 q.2.succ)

/-- The same emitted edge before applying the original-label equivalence. -/
def BoundedKernelSubdivisionDatum.subdivisionSlotEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    Sym2 (BoundedKernelSubdivisionSlot D.profile) :=
  s(D.pathSlot q.1 q.2.castSucc, D.pathSlot q.1 q.2.succ)

@[simp] theorem BoundedKernelSubdivisionDatum.subdivisionEdge_eq_map_slotEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    D.subdivisionEdge q = Sym2.map D.labels (D.subdivisionSlotEdge q) := by
  rfl

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_direct
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : (D.profile.length e).val = 0) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ =
      s((.inl (boundedKernelOrderedEndpoints K.shape e).1 :
          BoundedKernelSubdivisionSlot D.profile),
        (.inl (boundedKernelOrderedEndpoints K.shape e).2 :
          BoundedKernelSubdivisionSlot D.profile)) := by
  unfold BoundedKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeZero_castSucc]
  have hidx :
      (0 : Fin ((D.profile.length e).val + 1)).succ =
        (Fin.last (D.profile.length e).val).succ := by
    apply Fin.ext
    simp [he]
  rw [hidx, D.pathSlot_edgeLast_succ]
  rfl

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_start
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ =
      s((.inl (boundedKernelOrderedEndpoints K.shape e).1 :
          BoundedKernelSubdivisionSlot D.profile),
        (.inr ⟨e, (⟨0, he⟩ : Fin (D.profile.length e).val)⟩ :
          BoundedKernelSubdivisionSlot D.profile)) := by
  unfold BoundedKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeZero_castSucc,
    D.pathSlot_edgeZero_succ_of_pos e he]
  rfl

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_end
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionSlotEdge
        ⟨e, Fin.last (D.profile.length e).val⟩ =
      s((.inr ⟨e, (⟨(D.profile.length e).val - 1, by omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          BoundedKernelSubdivisionSlot D.profile),
        (.inl (boundedKernelOrderedEndpoints K.shape e).2 :
          BoundedKernelSubdivisionSlot D.profile)) := by
  unfold BoundedKernelSubdivisionDatum.subdivisionSlotEdge
  rw [D.pathSlot_edgeLast_castSucc_of_pos e he,
    D.pathSlot_edgeLast_succ]
  rfl

/-- Relabelling preserves both non-diagonality and injectivity of the
source-slot edge table. -/
theorem BoundedKernelSubdivisionDatum.subdivisionEdge_not_isDiag_iff
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    ¬(D.subdivisionEdge q).IsDiag ↔
      D.pathSlot q.1 q.2.castSucc ≠ D.pathSlot q.1 q.2.succ := by
  rw [D.subdivisionEdge_eq_map_slotEdge,
    Sym2.isDiag_map D.labels.injective]
  rfl

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_injective_iff_slotEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective D.subdivisionEdge ↔
      Function.Injective D.subdivisionSlotEdge := by
  constructor
  · intro hinj q r hqr
    apply hinj
    simpa only [D.subdivisionEdge_eq_map_slotEdge] using
      congrArg (Sym2.map D.labels) hqr
  · intro hinj q r hqr
    apply hinj
    apply Sym2.map.injective D.labels.injective
    simpa only [D.subdivisionEdge_eq_map_slotEdge] using hqr

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_direct
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective
      (fun e : {e : Fin K.shape.2.1.val //
          (D.profile.length e).val = 0} ↦
        D.subdivisionSlotEdge
          ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) := by
  intro e f hef
  change D.subdivisionSlotEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, (0 : Fin ((D.profile.length f.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_direct e.1 e.2,
    D.subdivisionSlotEdge_direct f.1 f.2] at hef
  have hordered :
      s((boundedKernelOrderedEndpoints K.shape e.1).1,
          (boundedKernelOrderedEndpoints K.shape e.1).2) =
        s((boundedKernelOrderedEndpoints K.shape f.1).1,
          (boundedKernelOrderedEndpoints K.shape f.1).2) := by
    rcases Sym2.eq_iff.mp hef with hdir | hswap
    · exact Sym2.eq_iff.mpr (Or.inl
        ⟨Sum.inl.inj hdir.1, Sum.inl.inj hdir.2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr
        ⟨Sum.inl.inj hswap.1, Sum.inl.inj hswap.2⟩)
  exact D.profile.directEndpointsInjective (by
    simpa only [boundedKernelOrderedEndpoints_mk] using hordered)

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_start
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective
      (fun e : {e : Fin K.shape.2.1.val //
          0 < (D.profile.length e).val} ↦
        D.subdivisionSlotEdge
          ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) := by
  intro e f hef
  change D.subdivisionSlotEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, (0 : Fin ((D.profile.length f.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_start e.1 e.2,
    D.subdivisionSlotEdge_start f.1 f.2] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr.inj hdir.2)
  · cases hswap.1

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_start_ne_end
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e f : Fin K.shape.2.1.val)
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
        (boundedKernelOrderedEndpoints K.shape e).1 =
          (boundedKernelOrderedEndpoints K.shape f).2 :=
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
    have hloop : (K.shape.2.2 e).IsDiag :=
      (boundedKernelOrderedEndpoints_eq_iff_isDiag K e).1 hbranch
    have hge := D.profile.loopLength e hloop
    omega

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_end
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective
      (fun e : {e : Fin K.shape.2.1.val //
          0 < (D.profile.length e).val} ↦
        D.subdivisionSlotEdge
          ⟨e.1, Fin.last (D.profile.length e.1).val⟩) := by
  intro e f hef
  change D.subdivisionSlotEdge
      (⟨e.1, Fin.last (D.profile.length e.1).val⟩ :
        BoundedKernelSubdivisionEdgeSlot D) =
    D.subdivisionSlotEdge
      (⟨f.1, Fin.last (D.profile.length f.1).val⟩ :
        BoundedKernelSubdivisionEdgeSlot D) at hef
  rw [D.subdivisionSlotEdge_end e.1 e.2,
    D.subdivisionSlotEdge_end f.1 f.2] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr.inj hdir.1)
  · cases hswap.1

/-- Parameters for genuinely internal consecutive pairs. -/
def BoundedKernelSubdivisionMiddleSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :=
  Σ e : Fin K.shape.2.1.val,
    Fin ((D.profile.length e).val - 1)

def BoundedKernelSubdivisionDatum.middleEdgeSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (p : BoundedKernelSubdivisionMiddleSlot D) :
    BoundedKernelSubdivisionEdgeSlot D :=
  ⟨p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩⟩

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_middle
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin ((D.profile.length e).val - 1)) :
    D.subdivisionSlotEdge
        (D.middleEdgeSlot (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)) =
      s((.inr ⟨e, (⟨i.val, by have hi := i.isLt; omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          BoundedKernelSubdivisionSlot D.profile),
        (.inr ⟨e, (⟨i.val + 1, by have hi := i.isLt; omega⟩ :
            Fin (D.profile.length e).val)⟩ :
          BoundedKernelSubdivisionSlot D.profile)) := by
  let i₀ : Fin (D.profile.length e).val :=
    ⟨i.val, by have hi := i.isLt; omega⟩
  let i₁ : Fin (D.profile.length e).val :=
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have hcast :
      (D.middleEdgeSlot
        (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)).2.castSucc =
        Fin.succ i₀.castSucc := by
    apply Fin.ext
    rfl
  have hsucc :
      (D.middleEdgeSlot
        (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)).2.succ =
        Fin.succ i₁.castSucc := by
    apply Fin.ext
    rfl
  unfold BoundedKernelSubdivisionDatum.subdivisionSlotEdge
  simp only [BoundedKernelSubdivisionDatum.middleEdgeSlot] at hcast hsucc ⊢
  rw [hcast, hsucc, D.pathSlot_internal e i₀,
    D.pathSlot_internal e i₁]
  rfl

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_injective_on_middle
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective
      (fun p : BoundedKernelSubdivisionMiddleSlot D ↦
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
        (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)) =
    D.subdivisionSlotEdge
      (D.middleEdgeSlot
        (⟨f, j⟩ : BoundedKernelSubdivisionMiddleSlot D)) at hij
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

theorem BoundedKernelSubdivisionDatum.edgeSlot_classification
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    (∃ e : {e : Fin K.shape.2.1.val //
        (D.profile.length e).val = 0},
      q = ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) ∨
    (∃ e : {e : Fin K.shape.2.1.val //
        0 < (D.profile.length e).val},
      q = ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩) ∨
    (∃ e : {e : Fin K.shape.2.1.val //
        0 < (D.profile.length e).val},
      q = ⟨e.1, Fin.last (D.profile.length e.1).val⟩) ∨
    ∃ p : BoundedKernelSubdivisionMiddleSlot D,
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
          simp [BoundedKernelSubdivisionDatum.middleEdgeSlot, p]
          omega

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_start
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e f : Fin K.shape.2.1.val)
    (he : (D.profile.length e).val = 0)
    (hf : 0 < (D.profile.length f).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge
        ⟨f, (0 : Fin ((D.profile.length f).val + 1))⟩ := by
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_start f hf] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.2
  · cases hswap.1

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_end
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e f : Fin K.shape.2.1.val)
    (he : (D.profile.length e).val = 0)
    (hf : 0 < (D.profile.length f).val) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge
        ⟨f, Fin.last (D.profile.length f).val⟩ := by
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_end f hf] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.2

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_direct_ne_middle
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : (D.profile.length e).val = 0)
    (p : BoundedKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  intro hef
  rw [D.subdivisionSlotEdge_direct e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.1

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_start_ne_middle
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val)
    (p : BoundedKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  intro hef
  rw [D.subdivisionSlotEdge_start e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.1
  · cases hswap.1

theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_end_ne_middle
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val)
    (p : BoundedKernelSubdivisionMiddleSlot D) :
    D.subdivisionSlotEdge
        ⟨e, Fin.last (D.profile.length e).val⟩ ≠
      D.subdivisionSlotEdge (D.middleEdgeSlot p) := by
  rcases p with ⟨f, j⟩
  intro hef
  rw [D.subdivisionSlotEdge_end e he,
    D.subdivisionSlotEdge_middle f j] at hef
  rcases Sym2.eq_iff.mp hef with hdir | hswap
  · cases hdir.2
  · cases hswap.2

/-- The complete source-slot endpoint table is injective. -/
theorem BoundedKernelSubdivisionDatum.subdivisionSlotEdge_injective
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
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
    exact False.elim
      (D.subdivisionSlotEdge_direct_ne_start e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_direct_ne_end e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨p, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_direct_ne_middle e.1 e.2 p hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_direct_ne_start f.1 e.1 f.2 e.2 hqr.symm)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    have hef := D.subdivisionSlotEdge_injective_on_start hqr
    cases hef
    rfl
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_start_ne_end e.1 f.1 e.2 f.2 hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨p, rfl⟩
    exact False.elim (D.subdivisionSlotEdge_start_ne_middle e.1 e.2 p hqr)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_direct_ne_end f.1 e.1 f.2 e.2 hqr.symm)
  · rcases hq with ⟨e, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_start_ne_end f.1 e.1 f.2 e.2 hqr.symm)
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
    exact False.elim
      (D.subdivisionSlotEdge_direct_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_start_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨f, rfl⟩
    exact False.elim
      (D.subdivisionSlotEdge_end_ne_middle f.1 f.2 p hqr.symm)
  · rcases hq with ⟨p, rfl⟩
    rcases hr with ⟨q, rfl⟩
    have hpq := D.subdivisionSlotEdge_injective_on_middle hqr
    cases hpq
    rfl

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_injective
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective D.subdivisionEdge :=
  (D.subdivisionEdge_injective_iff_slotEdge).2
    D.subdivisionSlotEdge_injective

/-- Consecutive positions on every admissibly subdivided bounded-kernel edge
are distinct. -/
theorem BoundedKernelSubdivisionDatum.pathSlot_castSucc_ne_succ
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin ((D.profile.length e).val + 1)) :
    D.pathSlot e i.castSucc ≠ D.pathSlot e i.succ := by
  by_cases hi0 : i.val = 0
  · have hi : i = (0 : Fin ((D.profile.length e).val + 1)) := Fin.ext hi0
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
          (boundedKernelOrderedEndpoints K.shape e).1 =
            (boundedKernelOrderedEndpoints K.shape e).2 :=
        Sum.inl.inj h
      have hloop : (K.shape.2.2 e).IsDiag :=
        (boundedKernelOrderedEndpoints_eq_iff_isDiag K e).1 hendpoints
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
      let i₀ : Fin (D.profile.length e).val := ⟨i.val - 1, by omega⟩
      let i₁ : Fin (D.profile.length e).val := ⟨i.val, hilt⟩
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

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_not_isDiag
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    ¬(D.subdivisionEdge q).IsDiag :=
  (D.subdivisionEdge_not_isDiag_iff q).2
    (D.pathSlot_castSucc_ne_succ q.1 q.2)

/-- The variable-valence edge-slot count is still exactly `k + ell`; only
the excess identity of the bounded kernel replaces the cubic counts. -/
theorem boundedKernelSubdivisionEdgeSlot_card
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Fintype.card (BoundedKernelSubdivisionEdgeSlot D) = k + ell := by
  change Fintype.card
      (Σ e : Fin K.shape.2.1.val,
        Fin ((D.profile.length e).val + 1)) = k + ell
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have htotal := D.profile.totalLength
  have hexcess := K.excess
  omega

/-- Canonical enumeration of reconstructed edge slots. -/
def BoundedKernelSubdivisionDatum.edgeSlotEquiv
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    BoundedKernelSubdivisionEdgeSlot D ≃ Fin (k + ell) :=
  Fintype.equivFinOfCardEq (boundedKernelSubdivisionEdgeSlot_card D)

/-- Edge-labelled multigraph emitted by the variable-valence subdivision. -/
def BoundedKernelSubdivisionDatum.reconstructedMultiGraph
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    PerronWright.FiniteMultiGraph k (k + ell) where
  endpoints j := D.subdivisionEdge (D.edgeSlotEquiv.symm j)

@[simp] theorem BoundedKernelSubdivisionDatum.reconstructedMultiGraph_endpoints
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    D.reconstructedMultiGraph.endpoints (D.edgeSlotEquiv q) =
      D.subdivisionEdge q := by
  simp [BoundedKernelSubdivisionDatum.reconstructedMultiGraph]

/-- Ordinary simple support of the reconstructed edge table. -/
def BoundedKernelSubdivisionDatum.reconstructedGraph
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) : SimpleGraph (Fin k) :=
  finiteMultiGraphSupportGraph D.reconstructedMultiGraph

/-- Exact adjacency interface for the reconstruction. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_adj_iff
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) (x y : Fin k) :
    D.reconstructedGraph.Adj x y ↔
      (∃ q : BoundedKernelSubdivisionEdgeSlot D,
        D.subdivisionEdge q = s(x,y)) ∧ x ≠ y := by
  rw [BoundedKernelSubdivisionDatum.reconstructedGraph,
    finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨j, hj⟩, hxy⟩
    refine ⟨⟨D.edgeSlotEquiv.symm j, ?_⟩, hxy⟩
    simpa [BoundedKernelSubdivisionDatum.reconstructedMultiGraph] using hj
  · rintro ⟨⟨q, hq⟩, hxy⟩
    refine ⟨⟨D.edgeSlotEquiv q, ?_⟩, hxy⟩
    simpa [BoundedKernelSubdivisionDatum.reconstructedMultiGraph] using hq

theorem BoundedKernelSubdivisionDatum.pathEdge_adj
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    D.reconstructedGraph.Adj
      (D.pathVertex q.1 q.2.castSucc)
      (D.pathVertex q.1 q.2.succ) := by
  apply (D.reconstructedGraph_adj_iff _ _).2
  refine ⟨⟨q, rfl⟩, ?_⟩
  exact D.labels.injective.ne (D.pathSlot_castSucc_ne_succ q.1 q.2)

theorem BoundedKernelSubdivisionDatum.reconstructedGraph_edgeFinset_eq_image
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
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
        apply D.subdivisionEdge_not_isDiag q
        rw [hq, Sym2.mk_isDiag_iff]
        exact hxy

/-- Every admissible variable-valence subdivision has exactly `k + ell`
distinct support edges. -/
theorem BoundedKernelSubdivisionDatum.reconstructedGraph_edgeFinset_card
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    D.reconstructedGraph.edgeFinset.card = k + ell := by
  rw [D.reconstructedGraph_edgeFinset_eq_image,
    Finset.card_image_of_injective _ D.subdivisionEdge_injective,
    Finset.card_univ, boundedKernelSubdivisionEdgeSlot_card D]

end PerronWright.GraphCore
