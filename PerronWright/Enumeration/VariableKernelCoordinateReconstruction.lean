import PerronWright.Enumeration.VariableKernelCoordinateRelabel

/-!
# Reconstruction under bounded-kernel coordinate relabelling

This module continues `VariableKernelCoordinateRelabel`.  It relabels the edge
slots of a subdivision, proves that the emitted unordered edge is unchanged,
and hence proves literal preservation of the reconstructed labelled simple
graph.  No quotient cardinality or automorphism factor is used.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Coordinate transport on the complete vertex sequence of one subdivided
kernel edge, including its two branch endpoints. -/
noncomputable def BoundedKernelLengthProfile.coordinatePathVertexEquiv
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    Fin ((L.length e).val + 2) ≃
      Fin (((L.coordinateRelabel γ).length (γ.2 e)).val + 2) :=
  let hlen : (L.length e).val + 2 =
      ((L.coordinateRelabel γ).length (γ.2 e)).val + 2 := by simp
  if _hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1 then
    finCongr hlen
  else
    (Fin.revPerm : Equiv.Perm (Fin ((L.length e).val + 2))).trans
      (finCongr hlen)

/-- Coordinate transport on the consecutive-edge positions of one
subdivided kernel edge. -/
noncomputable def BoundedKernelLengthProfile.coordinatePathEdgeEquiv
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) :
    Fin ((L.length e).val + 1) ≃
      Fin (((L.coordinateRelabel γ).length (γ.2 e)).val + 1) :=
  let hlen : (L.length e).val + 1 =
      ((L.coordinateRelabel γ).length (γ.2 e)).val + 1 := by simp
  if _hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1 then
    finCongr hlen
  else
    (Fin.revPerm : Equiv.Perm (Fin ((L.length e).val + 1))).trans
      (finCongr hlen)

/-- On a directly transported kernel edge, complete path coordinates keep
their numerical position. -/
theorem BoundedKernelLengthProfile.coordinatePathVertexEquiv_val_of_direct
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (i : Fin ((L.length e).val + 2)) :
    (L.coordinatePathVertexEquiv γ e i).val = i.val := by
  unfold BoundedKernelLengthProfile.coordinatePathVertexEquiv
  simp only [dif_pos hfirst]
  rfl

/-- On a reversed kernel edge, complete path coordinates are reflected. -/
theorem BoundedKernelLengthProfile.coordinatePathVertexEquiv_val_of_reversed
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (i : Fin ((L.length e).val + 2)) :
    (L.coordinatePathVertexEquiv γ e i).val =
      (L.length e).val + 2 - (i.val + 1) := by
  unfold BoundedKernelLengthProfile.coordinatePathVertexEquiv
  simp only [dif_neg hfirst, Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Fin.val_rev]

/-- On a directly transported kernel edge, consecutive-edge coordinates
keep their numerical position. -/
theorem BoundedKernelLengthProfile.coordinatePathEdgeEquiv_val_of_direct
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (j : Fin ((L.length e).val + 1)) :
    (L.coordinatePathEdgeEquiv γ e j).val = j.val := by
  unfold BoundedKernelLengthProfile.coordinatePathEdgeEquiv
  simp only [dif_pos hfirst]
  rfl

/-- On a reversed kernel edge, consecutive-edge coordinates are reflected. -/
theorem BoundedKernelLengthProfile.coordinatePathEdgeEquiv_val_of_reversed
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (j : Fin ((L.length e).val + 1)) :
    (L.coordinatePathEdgeEquiv γ e j).val =
      (L.length e).val + 1 - (j.val + 1) := by
  unfold BoundedKernelLengthProfile.coordinatePathEdgeEquiv
  simp only [dif_neg hfirst, Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Fin.val_rev]

/-- The analogous value formula for internal path coordinates in the direct
orientation. -/
theorem BoundedKernelLengthProfile.coordinatePathIndexEquiv_val_of_direct
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (i : Fin (L.length e).val) :
    (L.coordinatePathIndexEquiv γ e i).val = i.val := by
  unfold BoundedKernelLengthProfile.coordinatePathIndexEquiv
  simp only [dif_pos hfirst]
  rfl

/-- The analogous value formula for internal path coordinates in the
reversed orientation. -/
theorem BoundedKernelLengthProfile.coordinatePathIndexEquiv_val_of_reversed
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1)
    (i : Fin (L.length e).val) :
    (L.coordinatePathIndexEquiv γ e i).val =
      (L.length e).val - (i.val + 1) := by
  unfold BoundedKernelLengthProfile.coordinatePathIndexEquiv
  simp only [dif_neg hfirst, Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Fin.val_rev]

/-- The induced equivalence of all subdivision edge slots. -/
noncomputable def BoundedKernelSubdivisionDatum.coordinateRelabelEdgeSlotEquiv
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K) :
    BoundedKernelSubdivisionEdgeSlot D ≃
      BoundedKernelSubdivisionEdgeSlot (D.coordinateRelabel γ) :=
  Equiv.sigmaCongr γ.2 (D.profile.coordinatePathEdgeEquiv γ)

@[simp]
theorem BoundedKernelSubdivisionDatum.coordinateRelabelEdgeSlotEquiv_apply
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val) (i : Fin ((D.profile.length e).val + 1)) :
    D.coordinateRelabelEdgeSlotEquiv γ ⟨e, i⟩ =
      ⟨γ.2 e, D.profile.coordinatePathEdgeEquiv γ e i⟩ :=
  rfl

/-- If the first ordered endpoint is transported directly, then so is the
second endpoint.  This also covers loops, where both target entries agree. -/
theorem boundedKernelOrderedEndpoints_coordinateRelabel_second_of_first
    {ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1) :
    γ.1 (boundedKernelOrderedEndpoints K.shape e).2 =
      (boundedKernelOrderedEndpoints
        ((K.coordinateRelabel γ).shape) (γ.2 e)).2 := by
  rcases boundedKernelOrderedEndpoints_coordinateRelabel K γ e with
    hdirect | hreversed
  · exact hdirect.2
  · have htarget :
        (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) (γ.2 e)).1 =
          (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) (γ.2 e)).2 :=
      hfirst.symm.trans hreversed.1
    exact hreversed.2.trans htarget

/-- Failure of direct first-endpoint transport forces the reversed ordered
endpoint alternative. -/
theorem boundedKernelOrderedEndpoints_coordinateRelabel_reversed
    {ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (hfirst :
      γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1) :
    γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).2 ∧
      γ.1 (boundedKernelOrderedEndpoints K.shape e).2 =
        (boundedKernelOrderedEndpoints
          ((K.coordinateRelabel γ).shape) (γ.2 e)).1 := by
  rcases boundedKernelOrderedEndpoints_coordinateRelabel K γ e with
    hdirect | hreversed
  · exact False.elim (hfirst hdirect.1)
  · exact hreversed

/-- Relabelling a path coordinate and then reading its original vertex label
gives exactly the source path vertex. -/
theorem BoundedKernelSubdivisionDatum.coordinateRelabel_pathVertex
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K)
    (e : Fin K.shape.2.1.val)
    (i : Fin ((D.profile.length e).val + 2)) :
    (D.coordinateRelabel γ).pathVertex (γ.2 e)
        (D.profile.coordinatePathVertexEquiv γ e i) =
      D.pathVertex e i := by
  let D' := D.coordinateRelabel γ
  let e' : Fin (K.coordinateRelabel γ).shape.2.1.val :=
    ⟨(γ.2 e).val, by
      simpa only [LabelledBoundedKernel.coordinateRelabel_edgeCount] using
        (γ.2 e).isLt⟩
  have he' : e' = γ.2 e := by
    apply Fin.ext
    rfl
  let φ : Fin ((D.profile.length e).val + 2) ≃
      Fin ((D'.profile.length e').val + 2) :=
    D.profile.coordinatePathVertexEquiv γ e
  let ψ : Fin (D.profile.length e).val ≃
      Fin (D'.profile.length e').val :=
    D.profile.coordinatePathIndexEquiv γ e
  change D'.pathVertex e' (φ i) = D.pathVertex e i
  let o := boundedKernelOrderedEndpoints K.shape e
  let o' := boundedKernelOrderedEndpoints
    ((K.coordinateRelabel γ).shape) e'
  have hlen : D'.profile.length e' = D.profile.length e := by
    dsimp only [D', e']
    exact D.profile.coordinateRelabel_length_apply γ e
  by_cases hfirst : γ.1 o.1 = o'.1
  · have hfirst' :
        γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
          (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) e').1 := by
      simpa only [o, o'] using hfirst
    have hsecond : γ.1 o.2 = o'.2 :=
      boundedKernelOrderedEndpoints_coordinateRelabel_second_of_first
        K γ e hfirst
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst i
      have hmap : φ 0 = 0 := by
        apply Fin.ext
        change (D.profile.coordinatePathVertexEquiv γ e 0).val = 0
        exact D.profile.coordinatePathVertexEquiv_val_of_direct
          γ e hfirst' (0 : Fin ((D.profile.length e).val + 2))
      rw [hmap]
      change D'.branchLabel
          (boundedKernelOrderedEndpoints
            (K.coordinateRelabel γ).shape e').1 =
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1
      dsimp only [D']
      rw [← hfirst, D.coordinateRelabel_branchLabel]
    · by_cases hilast : i.val = (D.profile.length e).val + 1
      · have hi : i = Fin.succ (Fin.last (D.profile.length e).val) := by
          apply Fin.ext
          simpa using hilast
        rw [hi]
        have hmap : φ
                (Fin.succ (Fin.last (D.profile.length e).val)) =
              Fin.succ (Fin.last
                (D'.profile.length e').val) := by
          have hv : (φ
              (Fin.succ (Fin.last (D.profile.length e).val))).val =
              (Fin.succ (Fin.last (D.profile.length e).val)).val := by
            dsimp only [φ]
            exact D.profile.coordinatePathVertexEquiv_val_of_direct γ e hfirst'
              (Fin.succ (Fin.last (D.profile.length e).val))
          apply Fin.ext
          rw [hv, hlen]
        rw [hmap]
        change D'.labels
              (D'.pathSlot e'
              (Fin.succ (Fin.last (D'.profile.length e').val))) =
          D.labels
            (D.pathSlot e
              (Fin.succ (Fin.last (D.profile.length e).val)))
        rw [D'.pathSlot_last, D.pathSlot_last]
        change D'.branchLabel
            (boundedKernelOrderedEndpoints
              (K.coordinateRelabel γ).shape e').2 =
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2
        dsimp only [D']
        rw [← hsecond, D.coordinateRelabel_branchLabel]
      · let j : Fin (D.profile.length e).val :=
          ⟨i.val - 1, by have hi := i.isLt; omega⟩
        have hi : i = Fin.succ j.castSucc := by
          apply Fin.ext
          simp [j]
          omega
        rw [hi]
        have hmap : φ (Fin.succ j.castSucc) =
              Fin.succ (ψ j).castSucc := by
          have hv : (φ (Fin.succ j.castSucc)).val =
              (Fin.succ j.castSucc).val := by
            dsimp only [φ]
            exact D.profile.coordinatePathVertexEquiv_val_of_direct γ e hfirst'
              (Fin.succ j.castSucc)
          have hp : (ψ j).val = j.val := by
            dsimp only [ψ]
            exact D.profile.coordinatePathIndexEquiv_val_of_direct γ e hfirst' j
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc] at hv hp ⊢
          omega
        rw [hmap]
        change D'.labels
            (D'.pathSlot e' (Fin.succ (ψ j).castSucc)) =
          D.labels (D.pathSlot e (Fin.succ j.castSucc))
        rw [D'.pathSlot_internal, D.pathSlot_internal]
        change D'.pathLabel e' (ψ j) = D.pathLabel e j
        dsimp only [D', e']
        dsimp only [ψ]
        exact D.coordinateRelabel_pathLabel γ e j
  · have hfirst' :
        γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
          (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) e').1 := by
      simpa only [o, o'] using hfirst
    have hreversed :=
      boundedKernelOrderedEndpoints_coordinateRelabel_reversed K γ e hfirst
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      subst i
      have hmap : φ 0 =
            Fin.succ (Fin.last
              (D'.profile.length e').val) := by
        have hv : (φ 0).val =
            (D.profile.length e).val + 2 - ((0 : Fin
              ((D.profile.length e).val + 2)).val + 1) := by
          dsimp only [φ]
          exact D.profile.coordinatePathVertexEquiv_val_of_reversed γ e hfirst'
            (0 : Fin ((D.profile.length e).val + 2))
        apply Fin.ext
        rw [hv, hlen]
        simp only [Fin.val_zero, Fin.val_succ, Fin.val_last]
        omega
      rw [hmap]
      change D'.labels
          (D'.pathSlot e'
            (Fin.succ (Fin.last (D'.profile.length e').val))) =
        D.labels (D.pathSlot e 0)
      rw [D'.pathSlot_last, D.pathSlot_zero]
      change D'.branchLabel
          (boundedKernelOrderedEndpoints
            (K.coordinateRelabel γ).shape e').2 =
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1
      dsimp only [D']
      rw [he', ← hreversed.1, D.coordinateRelabel_branchLabel]
    · by_cases hilast : i.val = (D.profile.length e).val + 1
      · have hi : i = Fin.succ (Fin.last (D.profile.length e).val) := by
          apply Fin.ext
          simpa using hilast
        subst i
        have hmap : φ
                (Fin.succ (Fin.last (D.profile.length e).val)) = 0 := by
          have hv : (φ
              (Fin.succ (Fin.last (D.profile.length e).val))).val =
              (D.profile.length e).val + 2 -
                ((Fin.succ (Fin.last (D.profile.length e).val)).val + 1) := by
            dsimp only [φ]
            exact D.profile.coordinatePathVertexEquiv_val_of_reversed γ e hfirst'
              (Fin.succ (Fin.last (D.profile.length e).val))
          apply Fin.ext
          rw [hv]
          simp only [Fin.val_zero, Fin.val_succ, Fin.val_last]
          omega
        rw [hmap]
        change D'.labels (D'.pathSlot e' 0) =
          D.labels
            (D.pathSlot e
              (Fin.succ (Fin.last (D.profile.length e).val)))
        rw [D'.pathSlot_zero, D.pathSlot_last]
        change D'.branchLabel
            (boundedKernelOrderedEndpoints
              (K.coordinateRelabel γ).shape e').1 =
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2
        dsimp only [D']
        rw [he', ← hreversed.2, D.coordinateRelabel_branchLabel]
      · let j : Fin (D.profile.length e).val :=
          ⟨i.val - 1, by have hi := i.isLt; omega⟩
        have hi : i = Fin.succ j.castSucc := by
          apply Fin.ext
          simp [j]
          omega
        rw [hi]
        have hmap : φ (Fin.succ j.castSucc) =
              Fin.succ (ψ j).castSucc := by
          have hv : (φ (Fin.succ j.castSucc)).val =
              (D.profile.length e).val + 2 -
                ((Fin.succ j.castSucc).val + 1) := by
            dsimp only [φ]
            exact D.profile.coordinatePathVertexEquiv_val_of_reversed γ e hfirst'
              (Fin.succ j.castSucc)
          have hp : (ψ j).val =
              (D.profile.length e).val - (j.val + 1) := by
            dsimp only [ψ]
            exact D.profile.coordinatePathIndexEquiv_val_of_reversed γ e hfirst' j
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc] at hv hp ⊢
          omega
        rw [hmap]
        change D'.labels
            (D'.pathSlot e' (Fin.succ (ψ j).castSucc)) =
          D.labels (D.pathSlot e (Fin.succ j.castSucc))
        rw [D'.pathSlot_internal, D.pathSlot_internal]
        change D'.pathLabel e' (ψ j) = D.pathLabel e j
        dsimp only [D', e']
        dsimp only [ψ]
        exact D.coordinateRelabel_pathLabel γ e j

/-- Coordinate relabelling only permutes subdivision edge slots.  On a
directly transported path the edge position is preserved; on a reversed
path its two endpoint positions are exchanged, which does not change the
emitted unordered edge. -/
theorem BoundedKernelSubdivisionDatum.coordinateRelabel_subdivisionEdge
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    (D.coordinateRelabel γ).subdivisionEdge
        (D.coordinateRelabelEdgeSlotEquiv γ q) =
      D.subdivisionEdge q := by
  rcases q with ⟨e, j⟩
  let D' := D.coordinateRelabel γ
  let φ : Fin ((D.profile.length e).val + 2) ≃
      Fin ((D'.profile.length (γ.2 e)).val + 2) :=
    D.profile.coordinatePathVertexEquiv γ e
  let ε : Fin ((D.profile.length e).val + 1) ≃
      Fin ((D'.profile.length (γ.2 e)).val + 1) :=
    D.profile.coordinatePathEdgeEquiv γ e
  change D'.subdivisionEdge
      (⟨γ.2 e, ε j⟩ : BoundedKernelSubdivisionEdgeSlot D') =
    D.subdivisionEdge (⟨e, j⟩ : BoundedKernelSubdivisionEdgeSlot D)
  let o := boundedKernelOrderedEndpoints K.shape e
  let o' := boundedKernelOrderedEndpoints
    ((K.coordinateRelabel γ).shape) (γ.2 e)
  by_cases hfirst : γ.1 o.1 = o'.1
  · have hfirst' :
        γ.1 (boundedKernelOrderedEndpoints K.shape e).1 =
          (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) (γ.2 e)).1 := by
      simpa only [o, o'] using hfirst
    have hleft : φ j.castSucc = (ε j).castSucc := by
      have hv : (φ j.castSucc).val = j.val := by
        dsimp only [φ]
        exact D.profile.coordinatePathVertexEquiv_val_of_direct γ e hfirst'
          j.castSucc
      have he : (ε j).val = j.val := by
        dsimp only [ε]
        exact D.profile.coordinatePathEdgeEquiv_val_of_direct γ e hfirst' j
      apply Fin.ext
      simp only [Fin.val_castSucc, hv, he]
    have hright : φ j.succ = (ε j).succ := by
      have hv : (φ j.succ).val = j.succ.val := by
        dsimp only [φ]
        exact D.profile.coordinatePathVertexEquiv_val_of_direct γ e hfirst'
          j.succ
      have he : (ε j).val = j.val := by
        dsimp only [ε]
        exact D.profile.coordinatePathEdgeEquiv_val_of_direct γ e hfirst' j
      apply Fin.ext
      simp only [Fin.val_succ] at hv ⊢
      omega
    have hvleft :
        D'.pathVertex (γ.2 e) (φ j.castSucc) =
          D.pathVertex e j.castSucc := by
      change (D.coordinateRelabel γ).pathVertex (γ.2 e)
          (D.profile.coordinatePathVertexEquiv γ e j.castSucc) =
        D.pathVertex e j.castSucc
      exact D.coordinateRelabel_pathVertex γ e j.castSucc
    have hvright :
        D'.pathVertex (γ.2 e) (φ j.succ) =
          D.pathVertex e j.succ := by
      change (D.coordinateRelabel γ).pathVertex (γ.2 e)
          (D.profile.coordinatePathVertexEquiv γ e j.succ) =
        D.pathVertex e j.succ
      exact D.coordinateRelabel_pathVertex γ e j.succ
    unfold BoundedKernelSubdivisionDatum.subdivisionEdge
    change s(D'.pathVertex (γ.2 e) (ε j).castSucc,
        D'.pathVertex (γ.2 e) (ε j).succ) =
      s(D.pathVertex e j.castSucc, D.pathVertex e j.succ)
    rw [← hleft, ← hright, hvleft, hvright]
  · have hfirst' :
        γ.1 (boundedKernelOrderedEndpoints K.shape e).1 ≠
          (boundedKernelOrderedEndpoints
            ((K.coordinateRelabel γ).shape) (γ.2 e)).1 := by
      simpa only [o, o'] using hfirst
    have hleft : φ j.succ = (ε j).castSucc := by
      have hv : (φ j.succ).val =
          (D.profile.length e).val + 2 - (j.succ.val + 1) := by
        dsimp only [φ]
        exact D.profile.coordinatePathVertexEquiv_val_of_reversed γ e hfirst'
          j.succ
      have he : (ε j).val =
          (D.profile.length e).val + 1 - (j.val + 1) := by
        dsimp only [ε]
        exact D.profile.coordinatePathEdgeEquiv_val_of_reversed γ e hfirst' j
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc] at hv ⊢
      omega
    have hright : φ j.castSucc = (ε j).succ := by
      have hv : (φ j.castSucc).val =
          (D.profile.length e).val + 2 - (j.castSucc.val + 1) := by
        dsimp only [φ]
        exact D.profile.coordinatePathVertexEquiv_val_of_reversed γ e hfirst'
          j.castSucc
      have he : (ε j).val =
          (D.profile.length e).val + 1 - (j.val + 1) := by
        dsimp only [ε]
        exact D.profile.coordinatePathEdgeEquiv_val_of_reversed γ e hfirst' j
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc] at hv ⊢
      omega
    have hvleft :
        D'.pathVertex (γ.2 e) (φ j.succ) =
          D.pathVertex e j.succ := by
      change (D.coordinateRelabel γ).pathVertex (γ.2 e)
          (D.profile.coordinatePathVertexEquiv γ e j.succ) =
        D.pathVertex e j.succ
      exact D.coordinateRelabel_pathVertex γ e j.succ
    have hvright :
        D'.pathVertex (γ.2 e) (φ j.castSucc) =
          D.pathVertex e j.castSucc := by
      change (D.coordinateRelabel γ).pathVertex (γ.2 e)
          (D.profile.coordinatePathVertexEquiv γ e j.castSucc) =
        D.pathVertex e j.castSucc
      exact D.coordinateRelabel_pathVertex γ e j.castSucc
    unfold BoundedKernelSubdivisionDatum.subdivisionEdge
    change s(D'.pathVertex (γ.2 e) (ε j).castSucc,
        D'.pathVertex (γ.2 e) (ε j).succ) =
      s(D.pathVertex e j.castSucc, D.pathVertex e j.succ)
    rw [← hleft, ← hright, hvleft, hvright]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

/-- Simultaneous branch/edge coordinate relabelling preserves the finite
edge set of the reconstructed labelled graph. -/
theorem BoundedKernelSubdivisionDatum.coordinateRelabel_reconstructedGraph_edgeFinset
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K) :
    (D.coordinateRelabel γ).reconstructedGraph.edgeFinset =
      D.reconstructedGraph.edgeFinset := by
  rw [(D.coordinateRelabel γ).reconstructedGraph_edgeFinset_eq_image,
    D.reconstructedGraph_edgeFinset_eq_image]
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    let E := D.coordinateRelabelEdgeSlotEquiv γ
    refine ⟨E.symm q, ?_⟩
    calc
      D.subdivisionEdge (E.symm q) =
          (D.coordinateRelabel γ).subdivisionEdge (E (E.symm q)) :=
        (D.coordinateRelabel_subdivisionEdge γ (E.symm q)).symm
      _ = (D.coordinateRelabel γ).subdivisionEdge q := by
        rw [E.apply_symm_apply]
      _ = z := hq
  · rintro ⟨q, hq⟩
    refine ⟨D.coordinateRelabelEdgeSlotEquiv γ q, ?_⟩
    rw [D.coordinateRelabel_subdivisionEdge γ q]
    exact hq

/-- Coordinate relabelling changes only the normalized kernel coordinates;
the reconstructed graph on the original vertex labels is literally the same
simple graph. -/
@[simp]
theorem BoundedKernelSubdivisionDatum.coordinateRelabel_reconstructedGraph
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (γ : BoundedKernelCoordinatePerm K) :
    (D.coordinateRelabel γ).reconstructedGraph = D.reconstructedGraph := by
  apply SimpleGraph.edgeFinset_inj.mp
  exact D.coordinateRelabel_reconstructedGraph_edgeFinset γ

end PerronWright.GraphCore
