import PerronWright.Enumeration.VariableSubdivisionSuppressionRecovery
import PerronWright.Enumeration.KernelGraphWeight

/-!
# Recovering bounded-kernel subdivision endpoints after suppression

For a positive-length normalized kernel edge, the two boundary stubs of its
recovered degree-two component are the first internal vertex incident to the
first branch endpoint and the last internal vertex incident to the second
branch endpoint.  Consequently suppression recovers the original endpoint
table on positive edges as well as on direct zero-length edges.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

theorem BoundedKernelSubdivisionDatum.firstPathLabel_adj_firstBranch
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.reconstructedGraph.Adj
      (D.pathLabel e.1 ⟨0, e.2⟩)
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1) := by
  let i : Fin (D.profile.length e.1).val := ⟨0, e.2⟩
  let q : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩
  have h := D.pathEdge_adj q
  have hleft : q.2.castSucc =
      (0 : Fin ((D.profile.length e.1).val + 2)) := by
    apply Fin.ext
    rfl
  have hright : q.2.succ = Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  rw [hleft, D.pathVertex_zero, hright, D.pathVertex_internal] at h
  exact h.symm

theorem BoundedKernelSubdivisionDatum.lastPathLabel_adj_secondBranch
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.reconstructedGraph.Adj
      (D.pathLabel e.1
        ⟨(D.profile.length e.1).val - 1, by omega⟩)
      (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) := by
  let i : Fin (D.profile.length e.1).val :=
    ⟨(D.profile.length e.1).val - 1, by omega⟩
  let q : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e.1, Fin.last (D.profile.length e.1).val⟩
  have h := D.pathEdge_adj q
  have hleft : q.2.castSucc = Fin.succ i.castSucc := by
    apply Fin.ext
    simp [q, i]
    omega
  have hright : q.2.succ =
      Fin.succ (Fin.last (D.profile.length e.1).val) := by
    apply Fin.ext
    rfl
  rw [hleft, D.pathVertex_internal, hright, D.pathVertex_last] at h
  exact h

/-- The boundary stub at the first end of a positive-length normalized edge. -/
noncomputable def BoundedKernelSubdivisionDatum.positiveEdgeFirstBoundaryStub
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    {q // q ∈ componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e)} := by
  let i : Fin (D.profile.length e.1).val := ⟨0, e.2⟩
  let x : D.positiveEdgeComponent K e :=
    D.positiveEdgeIndexToComponent K e i
  let b : Fin k :=
    D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1
  refine ⟨⟨x, b⟩, ?_⟩
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_filter,
    D.reconstructedGraph.mem_neighborFinset]
  constructor
  · exact D.firstPathLabel_adj_firstBranch K e
  · change D.reconstructedGraph.degree
        (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1) ≠ 2
    rw [D.branchVertex_degree_eq_kernelDegree]
    have hmin := K.minDegree (boundedKernelOrderedEndpoints K.shape e.1).1
    omega

/-- The boundary stub at the second end of a positive-length normalized edge. -/
noncomputable def BoundedKernelSubdivisionDatum.positiveEdgeLastBoundaryStub
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    {q // q ∈ componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e)} := by
  let i : Fin (D.profile.length e.1).val :=
    ⟨(D.profile.length e.1).val - 1, by omega⟩
  let x : D.positiveEdgeComponent K e :=
    D.positiveEdgeIndexToComponent K e i
  let b : Fin k :=
    D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2
  refine ⟨⟨x, b⟩, ?_⟩
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_filter,
    D.reconstructedGraph.mem_neighborFinset]
  constructor
  · exact D.lastPathLabel_adj_secondBranch K e
  · change D.reconstructedGraph.degree
        (D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) ≠ 2
    rw [D.branchVertex_degree_eq_kernelDegree]
    have hmin := K.minDegree (boundedKernelOrderedEndpoints K.shape e.1).2
    omega

theorem BoundedKernelSubdivisionDatum.positiveEdgeBoundaryStubs_ne
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.positiveEdgeFirstBoundaryStub K e ≠
      D.positiveEdgeLastBoundaryStub K e := by
  intro hstubs
  have hval := congrArg Subtype.val hstubs
  have hinternal :
      D.pathLabel e.1 ⟨0, e.2⟩ =
        D.pathLabel e.1
          ⟨(D.profile.length e.1).val - 1, by omega⟩ := by
    have hx := congrArg (fun q ↦ q.1.1.1) hval
    simpa [BoundedKernelSubdivisionDatum.positiveEdgeFirstBoundaryStub,
      BoundedKernelSubdivisionDatum.positiveEdgeLastBoundaryStub,
      BoundedKernelSubdivisionDatum.positiveEdgeIndexToComponent] using hx
  have hbranch :
      D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1 =
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2 := by
    have hb := congrArg Sigma.snd hval
    simpa [BoundedKernelSubdivisionDatum.positiveEdgeFirstBoundaryStub,
      BoundedKernelSubdivisionDatum.positiveEdgeLastBoundaryStub] using hb
  let q₀ : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩
  let q₁ : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e.1, Fin.last (D.profile.length e.1).val⟩
  have hedges : D.subdivisionEdge q₀ = D.subdivisionEdge q₁ := by
    rw [show D.subdivisionEdge q₀ =
        s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1,
          D.pathLabel e.1 ⟨0, e.2⟩) from
      D.subdivisionEdge_start e.1 e.2,
      show D.subdivisionEdge q₁ =
        s(D.pathLabel e.1
            ⟨(D.profile.length e.1).val - 1, by omega⟩,
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) from
      D.subdivisionEdge_end e.1 e.2,
      hinternal, hbranch]
    exact Sym2.eq_swap
  have hslots := D.subdivisionEdge_injective hedges
  have hindex := congrArg
    (fun q : BoundedKernelSubdivisionEdgeSlot D ↦ q.2.val) hslots
  simp only [q₀, q₁, Fin.val_zero, Fin.val_last] at hindex
  omega

theorem BoundedKernelSubdivisionDatum.degreeTwoPathEndpoints_positive
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    degreeTwoPathEndpoints D.reconstructedGraph hacyc
        (D.positiveEdgeComponent K e) =
      Sym2.map D.branchLabel ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1) := by
  let qL := D.positiveEdgeFirstBoundaryStub K e
  let qR := D.positiveEdgeLastBoundaryStub K e
  calc
    degreeTwoPathEndpoints D.reconstructedGraph hacyc
        (D.positiveEdgeComponent K e) = s(qL.val.2, qR.val.2) :=
      degreeTwoPathEndpoints_eq_boundaryStubPair
        D.reconstructedGraph hacyc (D.positiveEdgeComponent K e)
        qL qR (D.positiveEdgeBoundaryStubs_ne K e)
    _ = s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1,
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) := rfl
    _ = Sym2.map D.branchLabel ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1) := by
      change
        s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1,
            D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) =
          Sym2.map D.branchLabel (K.shape.2.2 e.1)
      rw [← boundedKernelOrderedEndpoints_mk K e.1, Sym2.map_mk]

theorem BoundedKernelSubdivisionDatum.kernelEdgeEndpoints_positive
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    kernelEdgeEndpoints D.reconstructedGraph hacyc
        ((.inl (D.positiveEdgeComponent K e)) :
          KernelEdgeLabel D.reconstructedGraph) =
      Sym2.map D.branchLabel ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1) := by
  exact D.degreeTwoPathEndpoints_positive K hacyc e

theorem BoundedKernelSubdivisionDatum.kernelBranchEndpoints_positive
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hmin : ∀ v, 2 ≤ D.reconstructedGraph.degree v)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Sym2.map (D.branchLabelEquivBranching K).symm
        (kernelBranchEndpoints D.reconstructedGraph hmin hacyc
          ((.inl (D.positiveEdgeComponent K e)) :
            KernelEdgeLabel D.reconstructedGraph)) =
      (boundedKernelFiniteMultiGraph K.shape).endpoints e.1 := by
  let E := D.branchLabelEquivBranching K
  let z : KernelEdgeLabel D.reconstructedGraph :=
    (.inl (D.positiveEdgeComponent K e) :
      KernelEdgeLabel D.reconstructedGraph)
  change Sym2.map E.symm
      (kernelBranchEndpoints D.reconstructedGraph hmin hacyc z) = _
  apply Sym2.map.injective E.injective
  rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id]
  apply Sym2.map.injective Subtype.val_injective
  rw [Sym2.map_map]
  change Sym2.map Subtype.val
      (kernelBranchEndpoints D.reconstructedGraph hmin hacyc z) =
    Sym2.map (fun u ↦ D.branchLabel u) ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1)
  have hmap := kernelBranchEndpoints_map_val
    D.reconstructedGraph hmin hacyc z
  rw [hmap]
  simpa only [z] using D.kernelEdgeEndpoints_positive K hacyc e

/-- The degree-two graph of a positive-surplus subdivision of a connected
bounded kernel is automatically acyclic. -/
theorem BoundedKernelSubdivisionDatum.reconstructedTwoGraph_isAcyclic
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected)
    (hell : 0 < ell) :
    (twoGraph D.reconstructedGraph).IsAcyclic := by
  apply degreeTwo_induced_isAcyclic D.reconstructedGraph
    (D.reconstructedGraph_connected hconn)
    D.reconstructedGraph_minDegree_two
    hell
  simpa only [Fintype.card_fin] using
    D.reconstructedGraph_edgeFinset_card

/-- With any valid minimum-degree and acyclicity witnesses, the recovered
edge and branch relabellings transport every suppressed edge back to its
literal original endpoint pair. -/
theorem BoundedKernelSubdivisionDatum.recoveredKernelBranchEndpoints_exact
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hmin : ∀ v, 2 ≤ D.reconstructedGraph.degree v)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : Fin K.shape.2.1.val) :
    Sym2.map (D.branchLabelEquivBranching K).symm
        (kernelBranchEndpoints D.reconstructedGraph hmin hacyc
          ((D.recoveredKernelEdgeEquiv K).symm e)) =
      (boundedKernelFiniteMultiGraph K.shape).endpoints e := by
  by_cases hpos : 0 < (D.profile.length e).val
  · let ep : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val} :=
      ⟨e, hpos⟩
    have hedge : (D.recoveredKernelEdgeEquiv K).symm e =
        ((.inl (D.positiveEdgeComponent K ep)) :
          KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_positive K ep).symm
    rw [hedge]
    exact D.kernelBranchEndpoints_positive K hmin hacyc ep
  · have hzero : (D.profile.length e).val = 0 := Nat.eq_zero_of_not_pos hpos
    let ez : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0} :=
      ⟨e, hzero⟩
    have hedge : (D.recoveredKernelEdgeEquiv K).symm e =
        ((.inr (D.zeroLengthEdgeToDirectBranchEdge K ez)) :
          KernelEdgeLabel D.reconstructedGraph) := by
      apply (D.recoveredKernelEdgeEquiv K).injective
      rw [Equiv.apply_symm_apply]
      exact (D.recoveredKernelEdgeEquiv_zero K ez).symm
    rw [hedge]
    exact D.kernelBranchEndpoints_zero K hmin hacyc ez

/-- The recovered suppressed-kernel endpoint table is definitionally indexed
by the original `Fin K.shape.2.1.val` edge labels and equals the input kernel table
pointwise, with all graph-theoretic hypotheses discharged from the datum. -/
theorem BoundedKernelSubdivisionDatum.recoveredKernelBranchEndpointTable
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hconn : (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph K.shape)).Connected)
    (hell : 0 < ell) :
    (fun e : Fin K.shape.2.1.val ↦
      Sym2.map (D.branchLabelEquivBranching K).symm
        (kernelBranchEndpoints D.reconstructedGraph
          D.reconstructedGraph_minDegree_two
          (D.reconstructedTwoGraph_isAcyclic K hconn hell)
          ((D.recoveredKernelEdgeEquiv K).symm e))) =
      (boundedKernelFiniteMultiGraph K.shape).endpoints := by
  funext e
  exact D.recoveredKernelBranchEndpoints_exact K
    D.reconstructedGraph_minDegree_two
    (D.reconstructedTwoGraph_isAcyclic K hconn hell) e

end PerronWright.GraphCore
