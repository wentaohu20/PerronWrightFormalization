import PerronWright.Enumeration.CubicReconstructionWeight
import PerronWright.Enumeration.DecoratedKernelRegroup
import PerronWright.Enumeration.FieldWeight

/-!
# Field weight of a reconstructed cubic subdivision

This file decorates a fixed cubic subdivision with literal vertex marks.
Branch marks are read at `D.branchLabel`, and internal path marks are read in
the exact order `D.pathLabel`.  For a genuine external field the same
continuous mark occurs at every labelled vertex, so path orientation drops
out and the existing marked-core factorization gives an exact identity with
the canonical decorated datum.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- The canonical decorated datum attached to a fixed labelled cubic
subdivision.  Unlike the coarse existential regrouping, this retains the
literal branch and internal labels supplied by `D.labels`. -/
def CubicKernelSubdivisionDatum.decoratedKernelDatum
    {S : Type*} [MetricSpace S] {k ell : ℕ}
    {K : LabelledConnectedCubicKernel ell}
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (marks : Fin k → C(S, ℝ)) : DecoratedKernelDatum S k ell where
  nv := ⟨2 * ell, by omega⟩
  ne := ⟨3 * ell, by omega⟩
  length := D.profile.length
  orientedEndpoints := cubicKernelOrderedEndpoints K.graph
  branchMark := fun v ↦ marks (D.branchLabel v)
  pathMark := fun e i ↦ marks (D.pathLabel e i)

/-- A constant-mark path factor viewed as a function of an unordered pair
of normalized branch coordinates.  Symmetry is the already proved reversal
identity for a marked path, with its constant mark vector unchanged. -/
def constantMarkedPathEdgeFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    (n : ℕ) {v : ℕ} (x : Fin v → S) (e : Sym2 (Fin v)) : ℝ :=
  Sym2.lift ⟨fun i j ↦
    markedPathFactor M t n (fun _ ↦ mark) (x i) (x j), by
      intro i j
      simpa using
        (markedPathFactor_reverse M t n (fun _ ↦ mark) (x i) (x j))⟩ e

@[simp]
theorem constantMarkedPathEdgeFactor_mk
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    (n : ℕ) {v : ℕ} (x : Fin v → S) (i j : Fin v) :
    constantMarkedPathEdgeFactor M t mark n x s(i,j) =
      markedPathFactor M t n (fun _ ↦ mark) (x i) (x j) :=
  rfl

/-- At length zero there is no internal mark, so the constant-mark factor is
the ordinary direct-edge factor. -/
theorem constantMarkedPathEdgeFactor_zero
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {v : ℕ} (x : Fin v → S) (e : Sym2 (Fin v)) :
    constantMarkedPathEdgeFactor M t mark 0 x e =
      pathKernelEdgeFactor M t 0 x e := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- The constant-mark path-kernel integral encoded by one fixed cubic
subdivision. -/
def cubicSubdivisionConstantMarkedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) : ℝ :=
  ∫ x : Fin (2 * ell) → S,
    (∏ i : Fin (2 * ell),
        mark (x i) * Real.exp (-t * M.degreeFunction (x i))) *
      ∏ e : Fin (3 * ell),
        constantMarkedPathEdgeFactor M t mark
          (D.profile.length e).val x (K.graph.endpoints e)
    ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)

/-- If every original vertex receives the same mark, the canonical decorated
datum is exactly the preceding unordered constant-mark kernel integral. -/
theorem decoratedKernelIntegral_decoratedKernelDatum_const
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    decoratedKernelIntegral M t
        (D.decoratedKernelDatum (K := K) (fun _ ↦ mark)) =
      cubicSubdivisionConstantMarkedKernelIntegral M t mark K D := by
  unfold decoratedKernelIntegral
    cubicSubdivisionConstantMarkedKernelIntegral
    CubicKernelSubdivisionDatum.decoratedKernelDatum
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  rw [← cubicKernelOrderedEndpoints_mk K.graph e]
  rfl

set_option linter.style.haveILetI false in
/-- Exact fixed-subdivision factorization with one common continuous mark on
every labelled vertex.  This is the field-ready counterpart of
`graphWeight_reconstructedGraph_eq_cubicSubdivisionKernelIntegral`. -/
theorem markedGraphWeight_reconstructedGraph_eq_constantMarkedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (s₀ : S) :
    markedGraphWeight M t D.reconstructedGraph (fun _ ↦ mark) =
      cubicSubdivisionConstantMarkedKernelIntegral M t mark K D := by
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
  obtain ⟨n, e, qL, qR, hn, hne, _hL, _hR, hweight⟩ :=
    exists_markedGraphWeight_eq_integral_markedPathFactors
      M t G (fun _ ↦ mark) hacyc s₀
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => n C + 1
    | Sum.inr _ => 0
  have hedgeLength (a : KernelEdgeLabel G) :
      edgeLength a = kernelEdgeInternalLength G a := by
    cases a with
    | inl C =>
        simp only [edgeLength, kernelEdgeInternalLength,
          Nat.card_eq_fintype_card]
        exact (hn C).symm
    | inr d => rfl
  have hlength (a : Fin (3 * ell)) :
      edgeLength (eE.symm a) = (D.profile.length a).val := by
    calc
      edgeLength (eE.symm a) =
          kernelEdgeInternalLength G (eE.symm a) :=
        hedgeLength (eE.symm a)
      _ = D.recoveredKernelEdgeLength K a := rfl
      _ = (D.profile.length a).val :=
        D.recoveredKernelEdgeLength_eq K a
  have hendpoint (a : Fin (3 * ell)) :
      Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc (eE.symm a)) =
        K.graph.endpoints a := by
    exact D.recoveredKernelBranchEndpoints_exact K hmin hacyc a
  change markedGraphWeight M t G (fun _ ↦ mark) = _
  unfold cubicSubdivisionConstantMarkedKernelIntegral
  rw [hweight]
  rw [integral_coreBranch_relabel M G hmin eB]
  apply integral_congr_ae
  filter_upwards [] with x
  let b : coreBranchIndex G → S :=
    fun c ↦ x (eB (coreBranchEquivBranching G hmin c))
  change
    markedGraphCoreBranchFactor M t G (fun _ ↦ mark) s₀ b *
        ∏ C : (twoGraph G).ConnectedComponent,
          markedPathFactor M t (n C + 1) (fun _ ↦ mark)
            (b (componentBoundaryStubBranchIndex G C (qL C)))
            (b (componentBoundaryStubBranchIndex G C (qR C))) = _
  rw [markedGraphCoreBranchFactor_relabel_eq_kernelFactors
    M t G (fun _ ↦ mark) hmin hacyc s₀ eB x]
  have hcomp :
      (∏ C : (twoGraph G).ConnectedComponent,
          markedPathFactor M t (n C + 1) (fun _ ↦ mark)
            (b (componentBoundaryStubBranchIndex G C (qL C)))
            (b (componentBoundaryStubBranchIndex G C (qR C)))) =
        ∏ C : (twoGraph G).ConnectedComponent,
          constantMarkedPathEdgeFactor M t mark (n C + 1) x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro C _
    rw [kernelBranchEndpoints_eq_boundaryStubBranchPair
      G hmin hacyc C (qL C) (qR C) (hne C)]
    simp only [Sym2.map_mk, constantMarkedPathEdgeFactor_mk]
    rfl
  rw [hcomp]
  have hdirect :
      (∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G)))) =
        ∏ d : {e // e ∈ directBranchEdges G},
          constantMarkedPathEdgeFactor M t mark 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro d _
    exact (constantMarkedPathEdgeFactor_zero M t mark x _).symm
  rw [hdirect]
  let actualFactor : KernelEdgeLabel G → ℝ := fun a ↦
    constantMarkedPathEdgeFactor M t mark (edgeLength a) x
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc a))
  have hsplit :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        (∏ C : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C)) *
        ∏ d : {e // e ∈ directBranchEdges G},
          actualFactor (Sum.inr d) := by
    change
      (∏ a : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor a) = _
    exact Fintype.prod_sum_type actualFactor
  have hrelabel :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        ∏ j : Fin (3 * ell),
          constantMarkedPathEdgeFactor M t mark
            (D.profile.length j).val x (K.graph.endpoints j) := by
    exact Fintype.prod_equiv eE
      actualFactor
      (fun j : Fin (3 * ell) ↦
        constantMarkedPathEdgeFactor M t mark
          (D.profile.length j).val x (K.graph.endpoints j))
      (fun a ↦ by
        dsimp only [actualFactor]
        have hlen : edgeLength a =
            (D.profile.length (eE a)).val := by
          simpa only [Equiv.symm_apply_apply] using hlength (eE a)
        have hend :
            Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc a) =
              K.graph.endpoints (eE a) := by
          simpa only [Equiv.symm_apply_apply] using hendpoint (eE a)
        rw [hlen, hend])
  rw [← hrelabel, hsplit]
  dsimp only [actualFactor, edgeLength]
  ring

/-- The positive continuous mark corresponding to a real external field. -/
def externalFieldVertexMark
    {S : Type*} [TopologicalSpace S] (g : C(S, ℝ)) : C(S, ℝ) :=
  ⟨fun x ↦ Real.exp (g x), g.continuous.rexp⟩

@[simp]
theorem externalFieldVertexMark_apply
    {S : Type*} [TopologicalSpace S] (g : C(S, ℝ)) (x : S) :
    externalFieldVertexMark g x = Real.exp (g x) :=
  rfl

/-- A genuine real external-field graph weight is the marked zero-activity
graph weight at `t = 1`, with the common mark `exp g`. -/
theorem fieldGraphWeight_eq_markedGraphWeight_externalFieldVertexMark
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (g : C(S, ℝ))
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    M.fieldGraphWeight g G =
      markedGraphWeight M 1 G (fun _ ↦ externalFieldVertexMark g) := by
  unfold CompactBJRModel.fieldGraphWeight markedGraphWeight
  apply integral_congr_ae
  filter_upwards [] with x
  unfold CompactBJRModel.fieldGraphWeightIntegrand markedGraphIntegrand
    CompactBJRModel.graphWeightIntegrand
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [externalFieldVertexMark_apply]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The real external-field weight of the literal reconstructed graph is
the integral of its canonical decorated subdivision datum. -/
theorem fieldGraphWeight_reconstructedGraph_eq_decoratedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (g : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (s₀ : S) :
    M.fieldGraphWeight g D.reconstructedGraph =
      decoratedKernelIntegral M 1
        (D.decoratedKernelDatum (K := K)
          (fun _ ↦ externalFieldVertexMark g)) := by
  calc
    M.fieldGraphWeight g D.reconstructedGraph =
        markedGraphWeight M 1 D.reconstructedGraph
          (fun _ ↦ externalFieldVertexMark g) :=
      fieldGraphWeight_eq_markedGraphWeight_externalFieldVertexMark M g _
    _ = cubicSubdivisionConstantMarkedKernelIntegral M 1
          (externalFieldVertexMark g) K D :=
      markedGraphWeight_reconstructedGraph_eq_constantMarkedKernelIntegral
        M 1 (externalFieldVertexMark g) K D s₀
    _ = decoratedKernelIntegral M 1
          (D.decoratedKernelDatum (K := K)
            (fun _ ↦ externalFieldVertexMark g)) :=
      (decoratedKernelIntegral_decoratedKernelDatum_const
        M 1 (externalFieldVertexMark g) K D).symm

end PerronWright.GraphCore
