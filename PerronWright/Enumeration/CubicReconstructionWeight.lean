import PerronWright.Enumeration.CubicSubdivisionLengthRecovery
import PerronWright.Enumeration.CubicSubdivisionPositiveEndpointRecovery

/-!
# Exact weight of a reconstructed cubic subdivision

The cubic-subdivision datum already contains the two pieces of analytic data
which enter the positive-surplus kernel expansion: the endpoint table of the
fixed cubic kernel and the number of internal degree-two vertices on each
kernel edge.  This file identifies the weight of the literal reconstructed
simple graph with the corresponding path-kernel integral.

No multiplicity or automorphism factor occurs here.  This is a pointwise
identity for one labelled reconstruction datum; fibre counting is a separate
finite combinatorial step.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- The normalized path-kernel integral encoded by one cubic subdivision
datum.  The branch coordinates are the fixed kernel vertices, while the
length of edge `e` is the actual number of internal subdivision vertices
recorded by `D.profile.length e`. -/
def cubicSubdivisionKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) : ℝ :=
  ∫ x : Fin (2 * ell) → S,
    (∏ i : Fin (2 * ell),
        Real.exp (-t * M.degreeFunction (x i))) *
      ∏ e : Fin (3 * ell),
        pathKernelEdgeFactor M t (D.profile.length e).val x
          (K.graph.endpoints e)
    ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)

set_option linter.style.haveILetI false in
/-- The literal graph reconstructed from a cubic subdivision datum has
exactly the normalized kernel integral carried by that same datum.  Thus the
endpoint table and path lengths used analytically are not existentially
chosen replacements: they are `K.graph.endpoints` and `D.profile.length`
themselves. -/
theorem graphWeight_reconstructedGraph_eq_cubicSubdivisionKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (s₀ : S) :
    M.graphWeight t D.reconstructedGraph =
      cubicSubdivisionKernelIntegral M t K D := by
  classical
  let G : SimpleGraph (Fin k) := D.reconstructedGraph
  let hmin : ∀ v, 2 ≤ G.degree v :=
    D.reconstructedGraph_minDegree_two K.cubic K.connected
  let hacyc : (twoGraph G).IsAcyclic :=
    D.reconstructedTwoGraph_isAcyclic K
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin k) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  let eB : (branchingVertices G : Set (Fin k)) ≃ Fin (2 * ell) :=
    (D.branchLabelEquivBranching K).symm
  let eE : KernelEdgeLabel G ≃ Fin (3 * ell) :=
    D.recoveredKernelEdgeEquiv K
  obtain ⟨n, hn, qL, qR, hne, hweight⟩ :=
    exists_graphWeight_eq_integral_corePathKernels M t G hacyc s₀
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => n C + 1
    | Sum.inr _ => 0
  have hedgeLength (e : KernelEdgeLabel G) :
      edgeLength e = kernelEdgeInternalLength G e := by
    cases e with
    | inl C =>
        simp only [edgeLength, kernelEdgeInternalLength,
          Nat.card_eq_fintype_card]
        exact (hn C).symm
    | inr d => rfl
  have hlength (e : Fin (3 * ell)) :
      edgeLength (eE.symm e) = (D.profile.length e).val := by
    calc
      edgeLength (eE.symm e) =
          kernelEdgeInternalLength G (eE.symm e) :=
        hedgeLength (eE.symm e)
      _ = D.recoveredKernelEdgeLength K e := rfl
      _ = (D.profile.length e).val :=
        D.recoveredKernelEdgeLength_eq K e
  have hendpoint (e : Fin (3 * ell)) :
      Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc (eE.symm e)) =
        K.graph.endpoints e := by
    exact D.recoveredKernelBranchEndpoints_exact K hmin hacyc e
  change M.graphWeight t G = _
  unfold cubicSubdivisionKernelIntegral
  rw [hweight]
  rw [integral_coreBranch_relabel M G hmin eB]
  apply integral_congr_ae
  filter_upwards [] with x
  let b : coreBranchIndex G → S :=
    fun c ↦ x (eB (coreBranchEquivBranching G hmin c))
  change
    graphCoreBranchFactor M t G s₀ b *
        ∏ C : (twoGraph G).ConnectedComponent,
          pathKernel M t (n C + 1)
            (b (componentBoundaryStubBranchIndex G C (qL C)),
              b (componentBoundaryStubBranchIndex G C (qR C))) = _
  rw [graphCoreBranchFactor_relabel_eq_kernelFactors
    M t G hmin hacyc s₀ eB x]
  have hcomp :
      (∏ C : (twoGraph G).ConnectedComponent,
          pathKernel M t (n C + 1)
            (b (componentBoundaryStubBranchIndex G C (qL C)),
              b (componentBoundaryStubBranchIndex G C (qR C)))) =
        ∏ C : (twoGraph G).ConnectedComponent,
          pathKernelEdgeFactor M t (n C + 1) x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro C _
    simpa [b] using
      (pathKernelEdgeFactor_kernelBranchEndpoints_inl
        M t G hmin hacyc C (qL C) (qR C) (hne C) eB b).symm
  rw [hcomp]
  let actualFactor : KernelEdgeLabel G → ℝ := fun e ↦
    pathKernelEdgeFactor M t (edgeLength e) x
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc e))
  have hsplit :
      (∏ e : KernelEdgeLabel G, actualFactor e) =
        (∏ C : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C)) *
        ∏ d : {e // e ∈ directBranchEdges G},
          actualFactor (Sum.inr d) := by
    change
      (∏ e : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor e) = _
    exact Fintype.prod_sum_type actualFactor
  have hrelabel :
      (∏ e : KernelEdgeLabel G, actualFactor e) =
        ∏ j : Fin (3 * ell),
          pathKernelEdgeFactor M t (D.profile.length j).val x
            (K.graph.endpoints j) := by
    exact Fintype.prod_equiv eE
      actualFactor
      (fun j : Fin (3 * ell) ↦
        pathKernelEdgeFactor M t (D.profile.length j).val x
          (K.graph.endpoints j))
      (fun e ↦ by
        dsimp only [actualFactor]
        have hlen : edgeLength e =
            (D.profile.length (eE e)).val := by
          simpa only [Equiv.symm_apply_apply] using hlength (eE e)
        have hend :
            Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc e) =
              K.graph.endpoints (eE e) := by
          simpa only [Equiv.symm_apply_apply] using hendpoint (eE e)
        rw [hlen, hend])
  rw [← hrelabel, hsplit]
  dsimp only [actualFactor, edgeLength]
  ring

end PerronWright.GraphCore
