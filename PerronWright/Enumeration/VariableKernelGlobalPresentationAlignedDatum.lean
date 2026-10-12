import PerronWright.Enumeration.VariableKernelGlobalPresentationEndpointAlignment

/-!
# The globally aligned variable-kernel subdivision datum

The recovered source coordinate permutation first relabels the source datum.
The endpoint-table theorem identifies the resulting bounded kernel with the
target kernel, so the datum can then be transported literally across that
kernel equality.  This is the datum on which the remaining intrinsic-edge
naturality and fixed-coordinate loop-orbit arguments operate.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

namespace BoundedKernelPresentation

/-- Relabel the source subdivision datum by the globally recovered source
permutation and cast it across the resulting exact bounded-kernel equality. -/
noncomputable def globalRecoveredAlignedCastDatum
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    BoundedKernelSubdivisionDatum k Q.1.toLabelledBoundedKernel :=
  let gamma := P.globalRecoveredCoordinatePerm Q hG
  let hK : P.1.coordinateRelabel gamma = Q.1 :=
    P.kernel_coordinateRelabel_globalRecoveredCoordinatePerm hell Q hG
  let hRaw :
      (P.1.toLabelledBoundedKernel.coordinateRelabel gamma) =
        Q.1.toLabelledBoundedKernel :=
    by
      change
        (P.1.coordinateRelabel gamma).toLabelledBoundedKernel =
          Q.1.toLabelledBoundedKernel
      exact congrArg
        LabelledConnectedBoundedKernel.toLabelledBoundedKernel hK
  boundedKernelSubdivisionDatumCast hRaw
    (P.2.coordinateRelabel gamma)

/-- The aligned cast datum still reconstructs the source labelled graph. -/
@[simp] theorem globalRecoveredAlignedCastDatum_reconstructedGraph
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).reconstructedGraph =
      P.2.reconstructedGraph := by
  unfold globalRecoveredAlignedCastDatum
  rw [boundedKernelSubdivisionDatumCast_reconstructedGraph,
    BoundedKernelSubdivisionDatum.coordinateRelabel_reconstructedGraph]

/-- Hence the aligned cast datum and the target datum lie over one fixed
kernel and reconstruct the same labelled graph. -/
theorem globalRecoveredAlignedCastDatum_graph_eq_target
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    (P.globalRecoveredAlignedCastDatum hell Q hG).reconstructedGraph =
      Q.2.reconstructedGraph := by
  rw [P.globalRecoveredAlignedCastDatum_reconstructedGraph hell Q hG]
  exact hG

end BoundedKernelPresentation

end PerronWright.GraphCore
