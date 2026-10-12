import PerronWright.Enumeration.CubicGlobalPresentationSymmetry

/-!
# Action laws for cubic-kernel coordinate transport

The endpoint table carries an honest action of the branch/edge coordinate
permutations.  The only nontrivial point for subdivision data is path
orientation: after every vertex relabelling, the unordered endpoint pair is
sorted again.  The theorem
`cubicKernelCoordinateRelabelDirect_trans_iff` below is the resulting parity
cocycle.  It says that a composite transport is direct exactly when its two
successive transports have the same orientation.

This module deliberately stops short of asserting an equality between two
dependent subdivision data.  Such an equality must transport first across
`finiteMultiGraphCoordinateRelabel_trans` and then use the parity cocycle on
all sigma path slots.  The kernel-level action laws and the cocycle needed
for that final `HEq` argument are proved here; no unproved action-law
interface is introduced.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

private theorem labelledConnectedCubicKernel_eq_of_graph_eq
    {ell : ℕ} {K K' : LabelledConnectedCubicKernel ell}
    (hgraph : K.graph = K'.graph) : K = K' := by
  cases K with
  | mk graph cubic connected =>
      cases K' with
      | mk graph' cubic' connected' =>
          dsimp only at hgraph
          subst graph'
          rfl

private theorem cubicKernelLengthProfile_heq_of_graph_eq
    {k ell : ℕ}
    {H H' : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (hgraph : H = H')
    (L : CubicKernelLengthProfile k ell H)
    (L' : CubicKernelLengthProfile k ell H')
    (hlength : L.length = L'.length) : HEq L L' := by
  subst H'
  cases L with
  | mk length totalLength loopLength directEndpointsInjective =>
      cases L' with
      | mk length' totalLength' loopLength' directEndpointsInjective' =>
          dsimp only at hlength
          subst length'
          rfl

private theorem cubicKernelSubdivisionDatum_heq_of_graph_eq
    {k ell : ℕ}
    {H H' : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (hgraph : H = H')
    (D : CubicKernelSubdivisionDatum k ell H)
    (D' : CubicKernelSubdivisionDatum k ell H')
    (hprofile : HEq D.profile D'.profile)
    (hlabels : HEq D.labels D'.labels) : HEq D D' := by
  subst H'
  cases D with
  | mk profile labels =>
      cases D' with
      | mk profile' labels' =>
          dsimp only at hprofile hlabels
          have hp : profile = profile' := eq_of_heq hprofile
          subst profile'
          have hl : labels = labels' := eq_of_heq hlabels
          subst labels'
          rfl

/-- Relabelling a connected cubic kernel by the identity coordinate pair
returns the original kernel. -/
@[simp]
theorem LabelledConnectedCubicKernel.coordinateRelabel_refl
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    K.coordinateRelabel (CubicKernelCoordinatePerm.refl ell) = K := by
  apply labelledConnectedCubicKernel_eq_of_graph_eq
  exact finiteMultiGraphCoordinateRelabel_refl K.graph

/-- Successive coordinate relabellings of a connected cubic kernel compose
in the order fixed by `CubicKernelCoordinatePerm.trans`. -/
theorem LabelledConnectedCubicKernel.coordinateRelabel_trans
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (γ η : CubicKernelCoordinatePerm ell) :
    (K.coordinateRelabel γ).coordinateRelabel η =
      K.coordinateRelabel (CubicKernelCoordinatePerm.trans γ η) := by
  apply labelledConnectedCubicKernel_eq_of_graph_eq
  exact finiteMultiGraphCoordinateRelabel_trans K.graph γ η

/-- A path coordinate is transported directly when the first canonically
ordered endpoint remains the first canonically ordered endpoint after
relabeling.  Its negation is precisely the reversal branch used by
`coordinatePathIndexEquiv`. -/
def cubicKernelCoordinateRelabelDirect
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) : Prop :=
  γ.1 (cubicKernelOrderedEndpoints H e).1 =
    (cubicKernelOrderedEndpoints
      (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).1

instance cubicKernelCoordinateRelabelDirectDecidable
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    Decidable (cubicKernelCoordinateRelabelDirect H γ e) :=
  inferInstance

/-- Identity coordinate transport is direct on every edge, including every
loop edge. -/
@[simp]
theorem cubicKernelCoordinateRelabelDirect_refl
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) :
    cubicKernelCoordinateRelabelDirect H
      (CubicKernelCoordinatePerm.refl ell) e := by
  unfold cubicKernelCoordinateRelabelDirect
  rw [finiteMultiGraphCoordinateRelabel_refl]
  rfl

/-- If a transport is not direct, the ordered endpoint pair is transported
in the unique reversed order. -/
theorem cubicKernelOrderedEndpoints_coordinateRelabel_of_not_direct
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell))
    (h : ¬cubicKernelCoordinateRelabelDirect H γ e) :
    γ.1 (cubicKernelOrderedEndpoints H e).1 =
        (cubicKernelOrderedEndpoints
          (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).2 ∧
      γ.1 (cubicKernelOrderedEndpoints H e).2 =
        (cubicKernelOrderedEndpoints
          (finiteMultiGraphCoordinateRelabel γ H) (γ.2 e)).1 := by
  exact (cubicKernelOrderedEndpoints_coordinateRelabel H γ e).resolve_left
    (fun hdirect ↦ h hdirect.1)

/-- Orientation parity is a cocycle: the composite coordinate transport is
direct exactly when the two successive transports have equal parity.  This
is the endpoint-level fact needed to compose the path `Fin.rev` choices. -/
theorem cubicKernelCoordinateRelabelDirect_trans_iff
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ η : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell)) :
    cubicKernelCoordinateRelabelDirect H
        (CubicKernelCoordinatePerm.trans γ η) e ↔
      (cubicKernelCoordinateRelabelDirect H γ e ↔
        cubicKernelCoordinateRelabelDirect
          (finiteMultiGraphCoordinateRelabel γ H) η (γ.2 e)) := by
  unfold cubicKernelCoordinateRelabelDirect
  rw [← finiteMultiGraphCoordinateRelabel_trans H γ η]
  simp only [CubicKernelCoordinatePerm.trans_fst,
    CubicKernelCoordinatePerm.trans_snd, Equiv.trans_apply]
  let o₀ := cubicKernelOrderedEndpoints H e
  let H₁ := finiteMultiGraphCoordinateRelabel γ H
  let o₁ := cubicKernelOrderedEndpoints H₁ (γ.2 e)
  let H₂ := finiteMultiGraphCoordinateRelabel η H₁
  let o₂ := cubicKernelOrderedEndpoints H₂ (η.2 (γ.2 e))
  change
    η.1 (γ.1 o₀.1) = o₂.1 ↔
      (γ.1 o₀.1 = o₁.1 ↔ η.1 o₁.1 = o₂.1)
  have hγpair :
      (γ.1 o₀.1 = o₁.1 ∧ γ.1 o₀.2 = o₁.2) ∨
        (γ.1 o₀.1 = o₁.2 ∧ γ.1 o₀.2 = o₁.1) := by
    simpa only [o₀, o₁, H₁] using
      cubicKernelOrderedEndpoints_coordinateRelabel H γ e
  have hηpair :
      (η.1 o₁.1 = o₂.1 ∧ η.1 o₁.2 = o₂.2) ∨
        (η.1 o₁.1 = o₂.2 ∧ η.1 o₁.2 = o₂.1) := by
    simpa only [o₁, o₂, H₁, H₂] using
      cubicKernelOrderedEndpoints_coordinateRelabel H₁ η (γ.2 e)
  by_cases hγ : γ.1 o₀.1 = o₁.1
  · by_cases hη : η.1 o₁.1 = o₂.1
    · simp [hγ, hη]
    · simp [hγ, hη]
  · by_cases hη : η.1 o₁.1 = o₂.1
    · have hcomp : η.1 (γ.1 o₀.1) ≠ o₂.1 := by
        intro hcomp
        apply hγ
        apply η.1.injective
        exact hcomp.trans hη.symm
      simp [hcomp, hγ, hη]
    · have hγrev := hγpair.resolve_left (fun hdirect ↦ hγ hdirect.1)
      have hηrev := hηpair.resolve_left (fun hdirect ↦ hη hdirect.1)
      have hcomp : η.1 (γ.1 o₀.1) = o₂.1 := by
        rw [hγrev.1, hηrev.2]
      simp [hcomp, hγ, hη]

/-- In the direct case, coordinate transport preserves the numerical path
index.  The codomain `Fin` may be presented using a transported length
profile, so the statement is deliberately made on values. -/
theorem CubicKernelLengthProfile.coordinatePathIndexEquiv_apply_val_of_direct
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell))
    (h : cubicKernelCoordinateRelabelDirect H γ e)
    (i : Fin (L.length e).val) :
    (L.coordinatePathIndexEquiv γ e i).val = i.val := by
  exact L.coordinatePathIndexEquiv_val_of_direct γ e h i

/-- In the reversed case, coordinate transport applies the canonical
reversal of the finite path coordinate. -/
theorem CubicKernelLengthProfile.coordinatePathIndexEquiv_apply_val_of_not_direct
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell))
    (h : ¬cubicKernelCoordinateRelabelDirect H γ e)
    (i : Fin (L.length e).val) :
    (L.coordinatePathIndexEquiv γ e i).val =
      (L.length e).val - 1 - i.val := by
  have hval := L.coordinatePathIndexEquiv_val_of_reversed γ e h i
  omega

/-- The numerical path-coordinate transport composes.  This is the
cast-free core of the dependent slot-equivalence composition law: equality
of the relevant `Fin` terms follows from this value equality after the two
transported length indices have been identified. -/
theorem CubicKernelLengthProfile.coordinatePathIndexEquiv_trans_val
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ η : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell))
    (i : Fin (L.length e).val) :
    (((L.coordinateRelabel γ).coordinatePathIndexEquiv η (γ.2 e))
        (L.coordinatePathIndexEquiv γ e i)).val =
      (L.coordinatePathIndexEquiv
        (CubicKernelCoordinatePerm.trans γ η) e i).val := by
  have hparity :=
    cubicKernelCoordinateRelabelDirect_trans_iff H γ η e
  by_cases hγ : cubicKernelCoordinateRelabelDirect H γ e
  · by_cases hη : cubicKernelCoordinateRelabelDirect
        (finiteMultiGraphCoordinateRelabel γ H) η (γ.2 e)
    · have hcomp : cubicKernelCoordinateRelabelDirect H
          (CubicKernelCoordinatePerm.trans γ η) e :=
        hparity.mpr ⟨fun _ ↦ hη, fun _ ↦ hγ⟩
      rw [(L.coordinateRelabel γ).coordinatePathIndexEquiv_apply_val_of_direct
          η (γ.2 e) hη,
        L.coordinatePathIndexEquiv_apply_val_of_direct γ e hγ,
        L.coordinatePathIndexEquiv_apply_val_of_direct
          (CubicKernelCoordinatePerm.trans γ η) e hcomp]
    · have hcomp : ¬cubicKernelCoordinateRelabelDirect H
          (CubicKernelCoordinatePerm.trans γ η) e := by
        intro h
        exact hη ((hparity.mp h).mp hγ)
      rw [(L.coordinateRelabel γ).coordinatePathIndexEquiv_apply_val_of_not_direct
          η (γ.2 e) hη,
        L.coordinatePathIndexEquiv_apply_val_of_direct γ e hγ,
        L.coordinatePathIndexEquiv_apply_val_of_not_direct
          (CubicKernelCoordinatePerm.trans γ η) e hcomp]
      simp
  · by_cases hη : cubicKernelCoordinateRelabelDirect
        (finiteMultiGraphCoordinateRelabel γ H) η (γ.2 e)
    · have hcomp : ¬cubicKernelCoordinateRelabelDirect H
          (CubicKernelCoordinatePerm.trans γ η) e := by
        intro h
        exact hγ ((hparity.mp h).mpr hη)
      rw [(L.coordinateRelabel γ).coordinatePathIndexEquiv_apply_val_of_direct
          η (γ.2 e) hη,
        L.coordinatePathIndexEquiv_apply_val_of_not_direct γ e hγ,
        L.coordinatePathIndexEquiv_apply_val_of_not_direct
          (CubicKernelCoordinatePerm.trans γ η) e hcomp]
    · have hcomp : cubicKernelCoordinateRelabelDirect H
          (CubicKernelCoordinatePerm.trans γ η) e :=
        hparity.mpr
          ⟨fun h ↦ (hγ h).elim, fun h ↦ (hη h).elim⟩
      rw [(L.coordinateRelabel γ).coordinatePathIndexEquiv_apply_val_of_not_direct
          η (γ.2 e) hη,
        L.coordinatePathIndexEquiv_apply_val_of_not_direct γ e hγ,
        L.coordinatePathIndexEquiv_apply_val_of_direct
          (CubicKernelCoordinatePerm.trans γ η) e hcomp]
      simp
      omega

/-- The complete subdivision-slot equivalence is the identity under the
identity coordinate transport.  Its codomain slot type is definitionally
the same as the source slot type because the transported length function is
unchanged. -/
@[simp]
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_refl_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (z : CubicKernelSubdivisionSlot L) :
    L.coordinateRelabelSlotEquiv (CubicKernelCoordinatePerm.refl ell) z = z := by
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨e, i⟩
      rw [L.coordinateRelabelSlotEquiv_inr]
      apply congrArg Sum.inr
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        exact L.coordinatePathIndexEquiv_apply_val_of_direct
          (CubicKernelCoordinatePerm.refl ell) e
          (cubicKernelCoordinateRelabelDirect_refl H e) i

/-- The complete subdivision-slot equivalences compose.  This is an ordinary
equality rather than merely `HEq`: after unfolding the transported length
functions, the two codomain slot types are definitionally identical. -/
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_trans_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ η : CubicKernelCoordinatePerm ell)
    (z : CubicKernelSubdivisionSlot L) :
    (L.coordinateRelabel γ).coordinateRelabelSlotEquiv η
        (L.coordinateRelabelSlotEquiv γ z) =
      L.coordinateRelabelSlotEquiv
        (CubicKernelCoordinatePerm.trans γ η) z := by
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨e, i⟩
      rw [L.coordinateRelabelSlotEquiv_inr,
        (L.coordinateRelabel γ).coordinateRelabelSlotEquiv_inr,
        L.coordinateRelabelSlotEquiv_inr]
      apply congrArg Sum.inr
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        exact L.coordinatePathIndexEquiv_trans_val γ η e i

/-- Equivalence-level identity law for the complete subdivision slots. -/
@[simp]
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_refl
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :
    L.coordinateRelabelSlotEquiv (CubicKernelCoordinatePerm.refl ell) =
      Equiv.refl (CubicKernelSubdivisionSlot L) := by
  apply Equiv.ext
  exact L.coordinateRelabelSlotEquiv_refl_apply

/-- Equivalence-level composition law for the complete subdivision slots. -/
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_trans
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ η : CubicKernelCoordinatePerm ell) :
    (L.coordinateRelabelSlotEquiv γ).trans
        ((L.coordinateRelabel γ).coordinateRelabelSlotEquiv η) =
      L.coordinateRelabelSlotEquiv
        (CubicKernelCoordinatePerm.trans γ η) := by
  apply Equiv.ext
  exact L.coordinateRelabelSlotEquiv_trans_apply γ η

/-- The transported length profiles satisfy the identity law up to the
heterogeneous equality forced by the changed endpoint-table index. -/
theorem CubicKernelLengthProfile.coordinateRelabel_refl_heq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :
    HEq (L.coordinateRelabel (CubicKernelCoordinatePerm.refl ell)) L := by
  have hH := finiteMultiGraphCoordinateRelabel_refl H
  apply cubicKernelLengthProfile_heq_of_graph_eq hH
  funext e
  rfl

/-- The transported length profiles satisfy the composition law up to the
heterogeneous equality forced by the two propositionally equal endpoint
tables. -/
theorem CubicKernelLengthProfile.coordinateRelabel_trans_heq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ η : CubicKernelCoordinatePerm ell) :
    HEq ((L.coordinateRelabel γ).coordinateRelabel η)
      (L.coordinateRelabel (CubicKernelCoordinatePerm.trans γ η)) := by
  have hH := finiteMultiGraphCoordinateRelabel_trans H γ η
  apply cubicKernelLengthProfile_heq_of_graph_eq hH
  funext e
  simp [CubicKernelLengthProfile.coordinateRelabel,
    CubicKernelCoordinatePerm.trans, Equiv.trans_apply]

/-- The label equivalence itself is unchanged by identity coordinate
transport.  This is an ordinary equality because subdivision-slot types only
depend on the transported length function. -/
@[simp]
theorem CubicKernelSubdivisionDatum.coordinateRelabel_refl_labels
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    (D.coordinateRelabel
      (CubicKernelCoordinatePerm.refl ell)).labels = D.labels := by
  change
    (D.profile.coordinateRelabelSlotEquiv
      (CubicKernelCoordinatePerm.refl ell)).symm.trans D.labels = D.labels
  rw [D.profile.coordinateRelabelSlotEquiv_refl]
  rfl

/-- The label equivalences produced by two successive coordinate transports
and by the composite transport are equal.  The profile proof fields do not
enter their domain types; only the length functions do. -/
theorem CubicKernelSubdivisionDatum.coordinateRelabel_trans_labels
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ η : CubicKernelCoordinatePerm ell) :
    ((D.coordinateRelabel γ).coordinateRelabel η).labels =
      (D.coordinateRelabel
        (CubicKernelCoordinatePerm.trans γ η)).labels := by
  apply Equiv.ext
  intro y
  let E := D.profile.coordinateRelabelSlotEquiv
    (CubicKernelCoordinatePerm.trans γ η)
  obtain ⟨z, rfl⟩ := E.surjective y
  change
    D.labels
        ((D.profile.coordinateRelabelSlotEquiv γ).symm
          (((D.profile.coordinateRelabel γ).coordinateRelabelSlotEquiv η).symm
            (E z))) =
      D.labels (E.symm (E z))
  have hpreimage :
      ((D.profile.coordinateRelabel γ).coordinateRelabelSlotEquiv η).symm
          (E z) =
        D.profile.coordinateRelabelSlotEquiv γ z := by
    rw [← D.profile.coordinateRelabelSlotEquiv_trans_apply γ η z]
    exact ((D.profile.coordinateRelabel γ).coordinateRelabelSlotEquiv η).symm_apply_apply _
  rw [hpreimage,
    (D.profile.coordinateRelabelSlotEquiv γ).symm_apply_apply,
    E.symm_apply_apply]

/-- Identity coordinate transport preserves the entire dependent subdivision
datum up to the heterogeneous equality dictated by the endpoint-table
index. -/
theorem CubicKernelSubdivisionDatum.coordinateRelabel_refl_heq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    HEq (D.coordinateRelabel (CubicKernelCoordinatePerm.refl ell)) D := by
  have hH := finiteMultiGraphCoordinateRelabel_refl H
  apply cubicKernelSubdivisionDatum_heq_of_graph_eq hH
  · exact D.profile.coordinateRelabel_refl_heq
  · exact heq_of_eq D.coordinateRelabel_refl_labels

/-- Successive coordinate transports preserve the entire dependent
subdivision datum up to the heterogeneous equality dictated by the
endpoint-table composition law. -/
theorem CubicKernelSubdivisionDatum.coordinateRelabel_trans_heq
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ η : CubicKernelCoordinatePerm ell) :
    HEq ((D.coordinateRelabel γ).coordinateRelabel η)
      (D.coordinateRelabel (CubicKernelCoordinatePerm.trans γ η)) := by
  have hH := finiteMultiGraphCoordinateRelabel_trans H γ η
  apply cubicKernelSubdivisionDatum_heq_of_graph_eq hH
  · exact D.profile.coordinateRelabel_trans_heq γ η
  · exact heq_of_eq (D.coordinateRelabel_trans_labels γ η)

/-- Successive coordinate transports and the composite transport agree on
every original branch label.  Both sides are evaluated in their own
dependent datum types, so the conclusion lives in the common label type
`Fin k` and needs no cast. -/
theorem CubicKernelSubdivisionDatum.coordinateRelabel_trans_branchLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ η : CubicKernelCoordinatePerm ell)
    (v : Fin (2 * ell)) :
    ((D.coordinateRelabel γ).coordinateRelabel η).branchLabel
        (η.1 (γ.1 v)) =
      (D.coordinateRelabel
        (CubicKernelCoordinatePerm.trans γ η)).branchLabel
          ((CubicKernelCoordinatePerm.trans γ η).1 v) := by
  rw [(D.coordinateRelabel γ).coordinateRelabel_branchLabel,
    D.coordinateRelabel_branchLabel,
    D.coordinateRelabel_branchLabel]

/-- Successive coordinate transports and the composite transport agree on
every original internal path label when each side is evaluated at its
canonically transported path index.  The parity cocycle above identifies
the two numerical target indices needed for the eventual dependent `HEq`.
-/
theorem CubicKernelSubdivisionDatum.coordinateRelabel_trans_pathLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (γ η : CubicKernelCoordinatePerm ell)
    (e : Fin (3 * ell))
    (i : Fin (D.profile.length e).val) :
    ((D.coordinateRelabel γ).coordinateRelabel η).pathLabel
        (η.2 (γ.2 e))
        ((D.profile.coordinateRelabel γ).coordinatePathIndexEquiv
          η (γ.2 e) (D.profile.coordinatePathIndexEquiv γ e i)) =
      (D.coordinateRelabel
        (CubicKernelCoordinatePerm.trans γ η)).pathLabel
          ((CubicKernelCoordinatePerm.trans γ η).2 e)
          (D.profile.coordinatePathIndexEquiv
            (CubicKernelCoordinatePerm.trans γ η) e i) := by
  calc
    ((D.coordinateRelabel γ).coordinateRelabel η).pathLabel
          (η.2 (γ.2 e))
          ((D.profile.coordinateRelabel γ).coordinatePathIndexEquiv
            η (γ.2 e) (D.profile.coordinatePathIndexEquiv γ e i)) =
        (D.coordinateRelabel γ).pathLabel
          (γ.2 e) (D.profile.coordinatePathIndexEquiv γ e i) := by
      exact (D.coordinateRelabel γ).coordinateRelabel_pathLabel
        η (γ.2 e) (D.profile.coordinatePathIndexEquiv γ e i)
    _ = D.pathLabel e i := D.coordinateRelabel_pathLabel γ e i
    _ = (D.coordinateRelabel
          (CubicKernelCoordinatePerm.trans γ η)).pathLabel
            ((CubicKernelCoordinatePerm.trans γ η).2 e)
            (D.profile.coordinatePathIndexEquiv
              (CubicKernelCoordinatePerm.trans γ η) e i) :=
      (D.coordinateRelabel_pathLabel
        (CubicKernelCoordinatePerm.trans γ η) e i).symm

/-!
The dependent closure above uses the following four steps rather than
exposing an assumed action-law interface:

1. use `finiteMultiGraphCoordinateRelabel_refl` or
   `finiteMultiGraphCoordinateRelabel_trans` to identify the endpoint-table
   indices;
2. prove `HEq` of the transported length profiles from equality of their
   `length` fields (the other fields are propositions);
3. apply `Equiv.ext` to the label equivalences, using
   `coordinatePathIndexEquiv_trans_val` and `Fin.heq_ext_iff` on path slots;
4. finish with structure extensionality for the datum.

The global sigma action laws below are then immediate from `Sigma.ext`.
-/

/-- On the first projection, coordinate transport of a global presentation
satisfies the identity law.  The dependent datum equality is intentionally
not hidden in this statement. -/
@[simp]
theorem CubicKernelPresentation.coordinateRelabel_refl_kernel
    {k ell : ℕ} (P : CubicKernelPresentation k ell) :
    (P.coordinateRelabel (CubicKernelCoordinatePerm.refl ell)).1 = P.1 :=
  P.1.coordinateRelabel_refl

/-- On the first projection, coordinate transport of a global presentation
satisfies the composition law. -/
theorem CubicKernelPresentation.coordinateRelabel_trans_kernel
    {k ell : ℕ} (P : CubicKernelPresentation k ell)
    (γ η : CubicKernelCoordinatePerm ell) :
    ((P.coordinateRelabel γ).coordinateRelabel η).1 =
      (P.coordinateRelabel
        (CubicKernelCoordinatePerm.trans γ η)).1 :=
  P.1.coordinateRelabel_trans γ η

/-- Identity law for coordinate transport on global cubic presentations. -/
@[simp]
theorem CubicKernelPresentation.coordinateRelabel_refl
    {k ell : ℕ} (P : CubicKernelPresentation k ell) :
    P.coordinateRelabel (CubicKernelCoordinatePerm.refl ell) = P := by
  apply Sigma.ext P.1.coordinateRelabel_refl
  exact P.2.coordinateRelabel_refl_heq

/-- Composition law for coordinate transport on global cubic
presentations. -/
theorem CubicKernelPresentation.coordinateRelabel_trans
    {k ell : ℕ} (P : CubicKernelPresentation k ell)
    (γ η : CubicKernelCoordinatePerm ell) :
    (P.coordinateRelabel γ).coordinateRelabel η =
      P.coordinateRelabel (CubicKernelCoordinatePerm.trans γ η) := by
  apply Sigma.ext (P.1.coordinateRelabel_trans γ η)
  exact P.2.coordinateRelabel_trans_heq γ η

end PerronWright.GraphCore
