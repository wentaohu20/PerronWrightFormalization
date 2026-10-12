import PerronWright.Enumeration.CorePathAssembly
import PerronWright.Enumeration.FiniteKernelGeneral
import PerronWright.Enumeration.TreeCoefficientLowOrder

/-!
# Relabelling actual core-path factors as finite kernel factors

The literal branch-coordinate integral is transported to any finite
relabelling of the branch vertices.  Direct branch edges are identified with
length-zero path factors, and the two actual boundary stubs of every
degree-two component are proved to be exactly the unordered endpoint pair of
the corresponding suppressed kernel edge.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

private theorem equivMultiset_val_eq_toMultiset
    {A : Type*} (p : Sym2 A) :
    (Sym2.equivMultiset A p).val = p.toMultiset := by
  induction p using Sym2.inductionOn with
  | _ a b => rfl

/-- Direct branch-to-branch edges are the zero-internal-vertex case
of the same unordered analytic path-kernel factor. -/
theorem pathKernelEdgeFactor_zero_eq_edgeFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {v : ℕ}
    (x : Fin v → S) (e : Sym2 (Fin v)) :
    pathKernelEdgeFactor M t 0 x e = M.edgeFactor t x e := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- Direct branch edges are, in particular, actual edges of the original
finite graph. Keeping this lemma generic avoids committing to a specialized
decision procedure for quantified predicates on `Fin k`. -/
theorem directBranchEdges_subset_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    directBranchEdges G ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.mp he).1

/-- Under the minimum-degree-two hypothesis, the branch coordinates
used by the literal graph integral and the branch-vertex subtype used
by the normalized finite kernel are canonically equivalent. -/
def coreBranchEquivBranching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) :
    coreBranchIndex G ≃ (branchingVertices G : Set V) where
  toFun b := ⟨b.val, by
    simp only [branchingVertices, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hb := b.property
    have hm := hmin b.val
    omega⟩
  invFun b := ⟨b.val, by
    have hb := b.property
    simp only [branchingVertices, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and] at hb
    omega⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; rfl

@[simp] theorem coreBranchEquivBranching_apply_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) (b : coreBranchIndex G) :
    (coreBranchEquivBranching G hmin b).val = b.val := rfl

/-- The literal branch-coordinate product integral may be transported
exactly to any finite relabelling of the normalized kernel vertices. -/
theorem integral_coreBranch_relabel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {nv : ℕ}
    (eB : (branchingVertices G : Set V) ≃ Fin nv)
    (F : (coreBranchIndex G → S) → ℝ) :
    (∫ b : coreBranchIndex G → S, F b
        ∂Measure.pi (fun _ : coreBranchIndex G => M.mu)) =
      ∫ x : Fin nv → S,
        F (fun b => x (eB (coreBranchEquivBranching G hmin b)))
        ∂Measure.pi (fun _ : Fin nv => M.mu) := by
  let e : coreBranchIndex G ≃ Fin nv :=
    (coreBranchEquivBranching G hmin).trans eB
  let φ := MeasurableEquiv.piCongrLeft
    (fun _ : coreBranchIndex G => S) e.symm
  have hmp : MeasurePreserving φ
      (Measure.pi (fun _ : Fin nv => M.mu))
      (Measure.pi (fun _ : coreBranchIndex G => M.mu)) :=
    measurePreserving_piCongrLeft
      (fun _ : coreBranchIndex G => M.mu) e.symm
  have hφ (x : Fin nv → S) :
      φ x = fun b => x (eB (coreBranchEquivBranching G hmin b)) := by
    funext b
    simp [φ, e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  symm
  simpa only [hφ] using hmp.integral_comp' F

/-- Two distinct actual boundary stubs exhaust the boundary of a
degree-two component, so their unordered outside endpoints are
exactly the endpoint pair of the corresponding suppressed edge. -/
theorem degreeTwoPathEndpoints_eq_boundaryStubPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (C : (twoGraph G).ConnectedComponent)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) :
    degreeTwoPathEndpoints G hacyc C = s(qL.val.2, qR.val.2) := by
  have hval : qL.val ≠ qR.val := by
    intro h
    apply hne
    exact Subtype.ext h
  have hpair : componentBoundaryStubs G C = {qL.val, qR.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact qL.property
      · exact qR.property
    · rw [Finset.card_pair hval,
        componentBoundaryStubs_card_eq_two G hacyc C]
  have hpairVal := congrArg Finset.val hpair
  apply (Sym2.equivMultiset V).injective
  apply Subtype.ext
  rw [equivMultiset_val_eq_toMultiset,
    equivMultiset_val_eq_toMultiset,
    degreeTwoPathEndpoints_toMultiset, hpairVal]
  simp [Sym2.toMultiset, hval]
  change _ = qL.val.2 ::ₘ qR.val.2 ::ₘ 0
  rfl

/-- Under any relabelling of the actual branch vertices, the analytic
path-kernel factor of a degree-two component is literally the
unordered edge factor attached to its suppressed-kernel edge. -/
theorem pathKernelEdgeFactor_kernelBranchEndpoints_inl
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {m : ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (C : (twoGraph G).ConnectedComponent)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) {v : ℕ}
    (eB : (branchingVertices G : Set V) ≃ Fin v)
    (b : coreBranchIndex G → S) :
    pathKernelEdgeFactor M t m
        (fun i => b ((coreBranchEquivBranching G hmin).symm
          (eB.symm i)))
        (Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc
            (Sum.inl C : KernelEdgeLabel G))) =
      pathKernel M t m
        (b (componentBoundaryStubBranchIndex G C qL),
          b (componentBoundaryStubBranchIndex G C qR)) := by
  let bL : (branchingVertices G : Set V) :=
    ⟨qL.val.2, by
      have hne2 := (componentBoundaryStubBranchIndex G C qL).property
      change G.degree qL.val.2 ≠ 2 at hne2
      have htwo := hmin qL.val.2
      simp only [branchingVertices, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩
  let bR : (branchingVertices G : Set V) :=
    ⟨qR.val.2, by
      have hne2 := (componentBoundaryStubBranchIndex G C qR).property
      change G.degree qR.val.2 ≠ 2 at hne2
      have htwo := hmin qR.val.2
      simp only [branchingVertices, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩
  let eC : KernelEdgeLabel G := Sum.inl C
  have hend' : kernelBranchEndpoints G hmin hacyc eC = s(bL, bR) := by
    apply Sym2.map.injective Subtype.val_injective
    calc
      Sym2.map Subtype.val (kernelBranchEndpoints G hmin hacyc eC) =
          kernelEdgeEndpoints G hacyc eC :=
        kernelBranchEndpoints_map_val G hmin hacyc eC
      _ = degreeTwoPathEndpoints G hacyc C := rfl
      _ = s(qL.val.2, qR.val.2) :=
        degreeTwoPathEndpoints_eq_boundaryStubPair G hacyc C qL qR hne
      _ = Sym2.map Subtype.val s(bL, bR) := by
        simp [bL, bR]
  have hend : kernelBranchEndpoints G hmin hacyc
      (Sum.inl C : KernelEdgeLabel G) = s(bL, bR) := by
    simpa only [eC] using hend'
  rw [hend]
  simp only [Sym2.map_mk, pathKernelEdgeFactor_mk,
    Equiv.symm_apply_apply]
  congr 1

/-- Direct branch edges are represented by the same normalized unordered
endpoint table, with path length zero. -/
theorem pathKernelEdgeFactor_kernelBranchEndpoints_inr
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (d : {e // e ∈ directBranchEdges G}) {v : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin v)
    (b : coreBranchIndex G → S) :
    pathKernelEdgeFactor M t 0
        (fun i => b ((coreBranchEquivBranching G hmin).symm
          (eB.symm i)))
        (Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc
            (Sum.inr d : KernelEdgeLabel G))) =
      M.edgeFactor t (coreBranchAssemble G s₀ b) d.val := by
  let eD : KernelEdgeLabel G := Sum.inr d
  let z := kernelBranchEndpoints G hmin hacyc eD
  have hmap : Sym2.map Subtype.val z = d.val := by
    calc
      Sym2.map Subtype.val z = kernelEdgeEndpoints G hacyc eD :=
        kernelBranchEndpoints_map_val G hmin hacyc eD
      _ = d.val := rfl
  change pathKernelEdgeFactor M t 0
      (fun i => b ((coreBranchEquivBranching G hmin).symm
        (eB.symm i))) (Sym2.map eB z) = _
  rw [pathKernelEdgeFactor_zero_eq_edgeFactor]
  revert hmap
  induction z using Sym2.inductionOn with
  | _ i j =>
      intro hmap
      have hd : d.val = s(i.val, j.val) := by
        change Sym2.map Subtype.val s(i, j) = d.val at hmap
        rw [Sym2.map_mk] at hmap
        exact hmap.symm
      rw [hd]
      simp only [Sym2.map_mk, CompactBJRModel.edgeFactor_mk,
        Equiv.symm_apply_apply]
      rw [coreBranchAssemble_branch G s₀ b i.val
          ((coreBranchEquivBranching G hmin).symm i).property,
        coreBranchAssemble_branch G s₀ b j.val
          ((coreBranchEquivBranching G hmin).symm j).property]
      congr 2

/-- For every perturbation parameter, the literal branch block becomes the
product of the relabelled branch-vertex weights and the length-zero unordered
factors of all direct suppressed-kernel edges. -/
theorem graphCoreBranchFactor_relabel_eq_kernelFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) {nv : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin nv)
    (x : Fin nv → S) :
    graphCoreBranchFactor M t G s₀
        (fun b => x (eB (coreBranchEquivBranching G hmin b))) =
      (∏ i : Fin nv,
          Real.exp (-t * M.degreeFunction (x i))) *
        ∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
  classical
  let b : coreBranchIndex G → S :=
    fun c => x (eB (coreBranchEquivBranching G hmin c))
  have hvfilter :
      (Finset.univ : Finset (Fin k)).filter
          (fun v => coreVertexOwner G v = none) =
        branchingVertices G := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact coreVertexOwner_none_iff_branch G hmin v
  have hefilter :
      G.edgeFinset.filter (fun e => coreEdgeOwner G e = none) =
        directBranchEdges G := by
    apply Finset.Subset.antisymm
    · intro e he
      have heG := (Finset.mem_filter.mp he).1
      exact (coreEdgeOwner_none_iff_direct G hmin heG).mp
        (Finset.mem_filter.mp he).2
    · intro e hd
      have heG := directBranchEdges_subset_edgeFinset G hd
      exact Finset.mem_filter.mpr
        ⟨heG, (coreEdgeOwner_none_iff_direct G hmin heG).mpr hd⟩
  have hv :
      (∏ v ∈ branchingVertices G,
          Real.exp (-t * M.degreeFunction
            (coreBranchAssemble G s₀ b v))) =
        ∏ i : Fin nv,
          Real.exp (-t * M.degreeFunction (x i)) := by
    calc
      _ = ∏ z : (branchingVertices G : Set (Fin k)),
          Real.exp (-t * M.degreeFunction
            (coreBranchAssemble G s₀ b z.val)) := by
        exact Finset.prod_subtype (branchingVertices G)
          (fun _ => Iff.rfl)
          (fun v => Real.exp (-t * M.degreeFunction
            (coreBranchAssemble G s₀ b v)))
      _ = ∏ z : (branchingVertices G : Set (Fin k)),
          Real.exp (-t * M.degreeFunction (x (eB z))) := by
        apply Finset.prod_congr rfl
        intro z _
        rw [coreBranchAssemble_branch G s₀ b z.val
          ((coreBranchEquivBranching G hmin).symm z).property]
        change Real.exp (-t * M.degreeFunction
          (b ((coreBranchEquivBranching G hmin).symm z))) =
            Real.exp (-t * M.degreeFunction (x (eB z)))
        simp [b]
      _ = _ := by
        exact Fintype.prod_equiv eB
          (fun z : (branchingVertices G : Set (Fin k)) =>
            Real.exp (-t * M.degreeFunction (x (eB z))))
          (fun i : Fin nv => Real.exp (-t * M.degreeFunction (x i)))
          (fun _ => rfl)
  have he :
      (∏ e ∈ directBranchEdges G,
          M.edgeFactor t (coreBranchAssemble G s₀ b) e) =
        ∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
    calc
      _ = ∏ d : {e // e ∈ directBranchEdges G},
          M.edgeFactor t (coreBranchAssemble G s₀ b) d.val := by
        exact Finset.prod_subtype (directBranchEdges G)
          (fun _ => Iff.rfl)
          (fun e => M.edgeFactor t (coreBranchAssemble G s₀ b) e)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro d _
        simpa [b] using
          (pathKernelEdgeFactor_kernelBranchEndpoints_inr
            M t G hmin hacyc s₀ d eB b).symm
  change graphCoreBranchFactor M t G s₀ b = _
  unfold graphCoreBranchFactor coreBranchBlock
  rw [hvfilter, hefilter, hv, he]

/-- At the critical parameter, the preceding general identity uses the
standard zero-tree vertex factor. -/
theorem graphCoreBranchFactor_relabel_eq_zeroTreeKernelFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S)
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) {nv : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin nv)
    (x : Fin nv → S) :
    graphCoreBranchFactor M 1 G s₀
        (fun b => x (eB (coreBranchEquivBranching G hmin b))) =
      (∏ i : Fin nv, M.zeroTreeVertexFactor (x i)) *
        ∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M 1 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
  simpa only [CompactBJRModel.zeroTreeVertexFactor_apply,
    neg_mul, one_mul] using
    graphCoreBranchFactor_relabel_eq_kernelFactors
      M 1 G hmin hacyc s₀ eB x

end PerronWright.GraphCore
