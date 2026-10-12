import PerronWright.Enumeration.CubicGlobalPresentationFibre

/-!
# Casting the globally aligned cubic presentation to one fixed kernel

The recovered coordinate pair carries the source kernel to the target
kernel propositionally, not definitionally.  This file performs the required
transport of the source subdivision datum and proves the parts of the
fixed-kernel alignment which are independent of suppressed-edge naturality:

* the cast datum reconstructs the same labelled graph;
* its branch labels agree with the target datum;
* its complete admissible length profile agrees with the target profile;
* hence its recovered branch-coordinate permutation to the target is the
  identity.

The remaining edge-coordinate naturality statement is isolated in the final
module comment.  No unique-loop conclusion is stated before that fact is
proved.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Transport a subdivision datum across an equality of endpoint tables. -/
def cubicKernelSubdivisionDatumCast
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E)
    (D : CubicKernelSubdivisionDatum k ell H) :
    CubicKernelSubdivisionDatum k ell E := by
  subst E
  exact D

@[simp]
theorem cubicKernelSubdivisionDatumCast_rfl
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    cubicKernelSubdivisionDatumCast rfl D = D :=
  rfl

/-- Casting the endpoint-table index does not change the reconstructed
labelled simple graph. -/
@[simp]
theorem cubicKernelSubdivisionDatumCast_reconstructedGraph
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E)
    (D : CubicKernelSubdivisionDatum k ell H) :
    (cubicKernelSubdivisionDatumCast h D).reconstructedGraph =
      D.reconstructedGraph := by
  subst E
  rfl

/-- Casting preserves every numerical length coordinate. -/
@[simp]
theorem cubicKernelSubdivisionDatumCast_profile_length
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E)
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    (cubicKernelSubdivisionDatumCast h D).profile.length e =
      D.profile.length e := by
  subst E
  rfl

/-- Casting preserves every branch label. -/
@[simp]
theorem cubicKernelSubdivisionDatumCast_branchLabel
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E)
    (D : CubicKernelSubdivisionDatum k ell H)
    (v : Fin (2 * ell)) :
    (cubicKernelSubdivisionDatumCast h D).branchLabel v =
      D.branchLabel v := by
  subst E
  rfl

namespace CubicKernelPresentation

/-- The source datum, first put in the globally recovered coordinates and
then explicitly cast along the resulting kernel equality to the target
kernel's endpoint-table index. -/
noncomputable def globalRecoveredAlignedCastDatum
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    CubicKernelSubdivisionDatum k ell Q.1.graph :=
  let γ := P.globalRecoveredCoordinatePerm Q hG
  let hK := P.kernel_coordinateRelabel_globalRecoveredCoordinatePerm Q hG
  let hGraph : finiteMultiGraphCoordinateRelabel γ P.1.graph = Q.1.graph := by
    change (P.1.coordinateRelabel γ).graph = Q.1.graph
    exact congrArg LabelledConnectedCubicKernel.graph hK
  cubicKernelSubdivisionDatumCast hGraph
    (P.2.coordinateRelabel γ)

/-- The cast datum still reconstructs the source graph. -/
@[simp]
theorem globalRecoveredAlignedCastDatum_reconstructedGraph
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum Q hG).reconstructedGraph =
      P.2.reconstructedGraph := by
  unfold globalRecoveredAlignedCastDatum
  rw [cubicKernelSubdivisionDatumCast_reconstructedGraph,
    CubicKernelSubdivisionDatum.coordinateRelabel_reconstructedGraph]

/-- Thus the cast datum and the target datum lie in one fixed-kernel
reconstruction fibre. -/
theorem globalRecoveredAlignedCastDatum_graph_eq_target
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum Q hG).reconstructedGraph =
      Q.2.reconstructedGraph := by
  rw [P.globalRecoveredAlignedCastDatum_reconstructedGraph Q hG]
  exact hG

/-- At a transported branch coordinate, the cast datum and target datum
carry exactly the same original label. -/
theorem globalRecoveredAlignedCastDatum_branchLabel_apply
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin (2 * ell)) :
    (P.globalRecoveredAlignedCastDatum Q hG).branchLabel
        (P.globalRecoveredBranchCoordinatePerm Q hG v) =
      Q.2.branchLabel (P.globalRecoveredBranchCoordinatePerm Q hG v) := by
  let γ := P.globalRecoveredCoordinatePerm Q hG
  calc
    (P.globalRecoveredAlignedCastDatum Q hG).branchLabel
        (P.globalRecoveredBranchCoordinatePerm Q hG v) =
        (P.2.coordinateRelabel γ).branchLabel (γ.1 v) := by
      unfold globalRecoveredAlignedCastDatum
      rw [cubicKernelSubdivisionDatumCast_branchLabel]
      rfl
    _ = P.2.branchLabel v :=
      P.2.coordinateRelabel_branchLabel γ v
    _ = Q.2.branchLabel
        (P.globalRecoveredBranchCoordinatePerm Q hG v) :=
      (P.branchLabel_globalRecoveredBranchCoordinatePerm Q hG v).symm

/-- The cast datum and target datum agree on every branch coordinate. -/
theorem globalRecoveredAlignedCastDatum_branchLabel
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin (2 * ell)) :
    (P.globalRecoveredAlignedCastDatum Q hG).branchLabel v =
      Q.2.branchLabel v := by
  let σ := P.globalRecoveredBranchCoordinatePerm Q hG
  let u := σ.symm v
  calc
    (P.globalRecoveredAlignedCastDatum Q hG).branchLabel v =
        (P.globalRecoveredAlignedCastDatum Q hG).branchLabel (σ u) := by
      rw [σ.apply_symm_apply]
    _ = Q.2.branchLabel (σ u) :=
      P.globalRecoveredAlignedCastDatum_branchLabel_apply Q hG u
    _ = Q.2.branchLabel v := by rw [σ.apply_symm_apply]

/-- At a transported edge coordinate, the cast datum and target datum have
the same internal path length. -/
theorem globalRecoveredAlignedCastDatum_profile_length_apply
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin (3 * ell)) :
    (P.globalRecoveredAlignedCastDatum Q hG).profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) =
      Q.2.profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) := by
  let γ := P.globalRecoveredCoordinatePerm Q hG
  apply Fin.ext
  calc
    ((P.globalRecoveredAlignedCastDatum Q hG).profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)).val =
        ((P.2.coordinateRelabel γ).profile.length (γ.2 e)).val := by
      unfold globalRecoveredAlignedCastDatum
      rw [cubicKernelSubdivisionDatumCast_profile_length]
      rfl
    _ = (P.2.profile.length e).val := by
      rw [CubicKernelSubdivisionDatum.coordinateRelabel_profile,
        CubicKernelLengthProfile.coordinateRelabel_length_apply]
    _ = (Q.2.profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)).val :=
      P.profile_length_globalRecoveredKernelEdgeCoordinatePerm Q hG e

/-- The entire admissible length profiles agree after the global coordinate
transport and kernel cast.  All non-length fields are propositions and are
therefore discarded by structure extensionality. -/
theorem globalRecoveredAlignedCastDatum_profile
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum Q hG).profile = Q.2.profile := by
  have hlength :
      (P.globalRecoveredAlignedCastDatum Q hG).profile.length =
        Q.2.profile.length := by
    funext f
    let σ := P.globalRecoveredKernelEdgeCoordinatePerm Q hG
    let e := σ.symm f
    calc
      (P.globalRecoveredAlignedCastDatum Q hG).profile.length f =
          (P.globalRecoveredAlignedCastDatum Q hG).profile.length (σ e) := by
        rw [σ.apply_symm_apply]
      _ = Q.2.profile.length (σ e) :=
        P.globalRecoveredAlignedCastDatum_profile_length_apply Q hG e
      _ = Q.2.profile.length f := by rw [σ.apply_symm_apply]
  cases hD : (P.globalRecoveredAlignedCastDatum Q hG).profile with
  | mk dlength dtotal dloop ddirect =>
      cases hQ : Q.2.profile with
      | mk qlength qtotal qloop qdirect =>
          simp only [hD, hQ] at hlength ⊢
          subst qlength
          rfl

/-- Because the branch labels already agree coordinatewise, the canonical
fixed-kernel recovered branch permutation from the cast datum to the target
datum is the identity. -/
theorem globalRecoveredAlignedCastDatum_recoveredBranchCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum Q hG).recoveredBranchCoordinatePerm Q.1 Q.2
          (P.globalRecoveredAlignedCastDatum_graph_eq_target Q hG) =
      Equiv.refl (Fin (2 * ell)) := by
  apply Equiv.ext
  intro v
  let D := P.globalRecoveredAlignedCastDatum Q hG
  let hDQ := P.globalRecoveredAlignedCastDatum_graph_eq_target Q hG
  have hlabel := D.branchLabel_recoveredBranchCoordinatePerm Q.1 Q.2 hDQ v
  have hsame :
      Q.2.branchLabel
          (D.recoveredBranchCoordinatePerm Q.1 Q.2 hDQ v) =
        Q.2.branchLabel v := by
    exact hlabel.trans (P.globalRecoveredAlignedCastDatum_branchLabel Q hG v)
  change Q.2.labels (.inl _) = Q.2.labels (.inl _) at hsame
  exact Sum.inl.inj (Q.2.labels.injective hsame)

/-!
## Exact remaining naturality lemma

Let `D := P.globalRecoveredAlignedCastDatum Q hG`.  We have now proved

* `D.reconstructedGraph = Q.2.reconstructedGraph`,
* `D.profile = Q.2.profile`, and
* `D.recoveredBranchCoordinatePerm Q.1 Q.2 ... = Equiv.refl _`.

To invoke `existsUnique_reverseLoops_eq_alignedDatum` and identify its
aligned datum with `Q.2`, the remaining fact is

`D.recoveredKernelEdgeCoordinatePerm Q.1 Q.2 ... = Equiv.refl _`.

At the intrinsic level this reduces to naturality of
`recoveredKernelEdgeEquiv` under `coordinateRelabel` followed by
`cubicKernelSubdivisionDatumCast`: the edge `γ e` of the cast datum must
recover the same `KernelEdgeLabel` as edge `γ e` of `Q`.  This naturality is
not supplied by the current library.  It is stronger than endpoint-table and
length equality because parallel positive-length kernel edges can share both
of those data while representing different degree-two components.

Once this single intrinsic-edge naturality statement is proved, the edge
permutation is the identity by injectivity; the recovered path-index
equivalences are identities (branch permutation and profiles already agree),
so the recovered aligned datum is literally `Q.2`.  The existing fixed-kernel
unique-loop theorem then gives the desired unique cast equality without any
new combinatorial assumption.
-/

end CubicKernelPresentation

end PerronWright.GraphCore
