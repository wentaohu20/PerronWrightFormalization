import PerronWright.Enumeration.CoreAttachmentWeightRelabel
import PerronWright.Enumeration.RootedProfileRelabel

/-!
# The literal weight of an assembled core with rooted-tree attachments

This scratch module proves the missing finite-dimensional bridge between
`LabelledCoreForestAttachment.assembleGraph` and the already established
labelled-forest exponential formula.  The intended final statement is

`finiteGraphWeight M 1 (D.assembleGraph H)`

equals the integral over the core types of the literal core integrand times
`M.labelledCoreForestAttachmentWeight roots D`.

No graph-classification statement is used here: the core `H` and the genuine
attachment datum `D` are fixed throughout.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The edge-set subtype and the edge-finset subtype carry the same literal
unordered pairs. -/
noncomputable def edgeSetEquivEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeSet ≃ {e // e ∈ G.edgeFinset} where
  toFun e := ⟨e.1, G.mem_edgeFinset.mpr e.2⟩
  invFun e := ⟨e.1, G.mem_edgeFinset.mp e.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Rewriting an edge-finset product as a product over the graph's edge-set
subtype. -/
theorem prod_edgeFinset_eq_prod_edgeSet
    {V R : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [CommMonoid R] (w : Sym2 V → R) :
    (∏ e ∈ G.edgeFinset, w e) = ∏ e : G.edgeSet, w e.1 := by
  classical
  calc
    (∏ e ∈ G.edgeFinset, w e) =
        ∏ e : {e // e ∈ G.edgeFinset}, w e.1 :=
      (Finset.prod_coe_sort G.edgeFinset w).symm
    _ = ∏ e : G.edgeSet, w e.1 := by
      exact (Fintype.prod_equiv (edgeSetEquivEdgeFinset G)
        (fun e : G.edgeSet ↦ w e.1)
        (fun e : {e // e ∈ G.edgeFinset} ↦ w e.1)
        (fun _ ↦ rfl)).symm

/-- The already-proved edge-index bijection, bundled as an equivalence. -/
noncomputable def LabelledCoreForestAttachment.edgeIndexEquiv
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    D.edgeIndex H ≃ (D.assembleGraph H).edgeSet :=
  Equiv.ofBijective (D.edgeIndexToEdge H)
    ⟨D.edgeIndexToEdge_injective H, D.edgeIndexToEdge_surjective H⟩

noncomputable instance LabelledCoreForestAttachment.edgeIndexFintype
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    Fintype (D.edgeIndex H) := by
  unfold LabelledCoreForestAttachment.edgeIndex
  infer_instance

/-- Every edge product on the assembled graph splits into the core edges,
one parent edge for every block, and the internal edges of that block. -/
theorem LabelledCoreForestAttachment.assembleGraph_edge_product
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n)
    {R : Type*} [CommMonoid R]
    (w : Sym2 (Fin q ⊕ Fin n) → R) :
    (∏ e ∈ (D.assembleGraph H).edgeFinset, w e) =
      (∏ e : H.edgeSet, w ((D.coreHom H).mapEdgeSet e).1) *
        ∏ B : D.1.parts,
          w s(Sum.inl (D.2 B).1, Sum.inr (D.2 B).2.root.1) *
            ∏ e : (D.2 B).2.graph.edgeSet,
              w ((D.branchHom H B).mapEdgeSet e).1 := by
  classical
  rw [prod_edgeFinset_eq_prod_edgeSet]
  calc
    (∏ e : (D.assembleGraph H).edgeSet, w e.1) =
        ∏ a : D.edgeIndex H, w (D.edgeIndexToEdge H a).1 := by
      exact (Fintype.prod_equiv
        (LabelledCoreForestAttachment.edgeIndexEquiv H D)
        (fun a : D.edgeIndex H ↦ w (D.edgeIndexToEdge H a).1)
        (fun e : (D.assembleGraph H).edgeSet ↦ w e.1)
        (fun _ ↦ rfl)).symm
    _ = _ := by
      change
        (∏ a : H.edgeSet ⊕
            Σ B : D.1.parts, Unit ⊕ (D.2 B).2.graph.edgeSet,
          w (D.edgeIndexToEdge H a).1) = _
      rw [Fintype.prod_sum_type, Fintype.prod_sigma]
      congr 1
      apply Fintype.prod_congr
      intro B
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      rfl

private theorem finpartition_prod_univ
    {n : ℕ} {R : Type*} [CommMonoid R]
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (f : Fin n → R) :
    (∏ i : Fin n, f i) = ∏ B : P.parts, ∏ i : B.1, f i.1 := by
  classical
  calc
    (∏ i : Fin n, f i) = ∏ i ∈ P.parts.biUnion id, f i := by
      rw [P.biUnion_parts]
    _ = ∏ B ∈ P.parts, ∏ i ∈ B, f i :=
      Finset.prod_biUnion P.supIndep.pairwiseDisjoint
    _ = _ := by
      rw [← Finset.prod_coe_sort P.parts
        (fun B ↦ ∏ i ∈ B, f i)]
      apply Fintype.prod_congr
      intro B
      exact (Finset.prod_coe_sort B.1 f).symm

/-- The arbitrary-finite-type edge factor underlying
`finiteGraphWeightIntegrand` at `t = 1`. -/
private def finiteEdgeFactor (M : CompactBJRModel S)
    {V : Type*} (x : V → S) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun i j ↦ M.kernel (x i) (x j), by
    intro i j
    exact M.kernel.symmetric (x i) (x j)⟩ e

@[simp] private theorem finiteEdgeFactor_mk (M : CompactBJRModel S)
    {V : Type*} (x : V → S) (i j : V) :
    finiteEdgeFactor M x s(i,j) = M.kernel (x i) (x j) := rfl

private theorem finiteEdgeFactor_coreHom
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) (e : H.edgeSet) :
    finiteEdgeFactor M (Sum.elim roots off)
        ((D.coreHom H).mapEdgeSet e).1 =
      finiteEdgeFactor M roots e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j => rfl

private theorem finiteEdgeFactor_branchHom
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S)
    (B : D.1.parts) (e : (D.2 B).2.graph.edgeSet) :
    finiteEdgeFactor M (Sum.elim roots off)
        ((D.branchHom H B).mapEdgeSet e).1 =
      finiteEdgeFactor M (fun i : B.1 ↦ off i.1) e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j => rfl

private theorem finiteEdgeFactor_rootEdge
    (M : CompactBJRModel S) {q n : ℕ}
    (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) (B : D.1.parts) :
    finiteEdgeFactor M (Sum.elim roots off)
        s(Sum.inl (D.2 B).1, Sum.inr (D.2 B).2.root.1) =
      M.kernel (roots (D.2 B).1) (off (D.2 B).2.root.1) := rfl

private theorem finiteGraphWeightIntegrand_eq_vertex_mul_edge
    (M : CompactBJRModel S) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → S) :
    finiteGraphWeightIntegrand M 1 G x =
      (∏ v : V, Real.exp (-M.degreeFunction (x v))) *
        ∏ e ∈ G.edgeFinset, finiteEdgeFactor M x e := by
  unfold finiteGraphWeightIntegrand finiteEdgeFactor
  simp only [one_mul, neg_mul]

private theorem fieldGraphWeightIntegrand_zero_eq_finiteGraphWeightIntegrand_one
    (M : CompactBJRModel S) {k : ℕ}
    (G : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.fieldGraphWeightIntegrand 0 G x =
      finiteGraphWeightIntegrand M 1 G x := by
  unfold CompactBJRModel.fieldGraphWeightIntegrand
    finiteGraphWeightIntegrand CompactBJRModel.edgeFactor
  simp only [ContinuousMap.zero_apply, zero_sub, neg_mul, one_mul]

private theorem edgeFactor_one_eq_finiteEdgeFactor
    (M : CompactBJRModel S) {k : ℕ} (x : Fin k → S)
    (e : Sym2 (Fin k)) :
    M.edgeFactor 1 x e = finiteEdgeFactor M x e := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      simp only [CompactBJRModel.edgeFactor_mk,
        finiteEdgeFactor_mk, one_mul]

/-- The literal contribution of one fixed rooted-tree block, after fixing
the types of the ordered core vertices. -/
def attachmentBlockIntegrand
    (M : CompactBJRModel S) {q n : ℕ}
    (roots : Fin q → S) (D : LabelledCoreForestAttachment q n)
    (B : D.1.parts) (y : B.1 → S) : ℝ :=
  M.kernel (roots (D.2 B).1) (y (D.2 B).2.root) *
    finiteGraphWeightIntegrand M 1 (D.2 B).2.graph y

/-- A fixed block integrates to the genuine root-edge kernel action on the
actual rooted-tree profile carried by that block. -/
theorem integral_attachmentBlockIntegrand_eq_kernelAction
    (M : CompactBJRModel S) {q n : ℕ}
    (roots : Fin q → S) (D : LabelledCoreForestAttachment q n)
    (B : D.1.parts) :
    (∫ y : B.1 → S, attachmentBlockIntegrand M roots D B y
      ∂Measure.pi (fun _ : B.1 ↦ M.mu)) =
      M.kernel.action M.mu
        (LabelledRootBranch.profileMap M (D.2 B).2)
        (roots (D.2 B).1) := by
  classical
  let e := B.1.equivFin
  let G : SimpleGraph (Fin B.1.card) :=
    (D.2 B).2.graph.comap (e.symm : Fin B.1.card → B.1)
  let v : Fin B.1.card := e (D.2 B).2.root
  have hpoint (y : B.1 → S) :
      attachmentBlockIntegrand M roots D B y =
        M.kernel (roots (D.2 B).1)
            ((fun j : Fin B.1.card ↦ y (e.symm j)) v) *
          M.fieldGraphWeightIntegrand 0 G
            (fun j : Fin B.1.card ↦ y (e.symm j)) := by
    unfold attachmentBlockIntegrand
    have hiso := finiteGraphWeightIntegrand_iso M 1 G (D.2 B).2.graph
      (SimpleGraph.Iso.comap e.symm (D.2 B).2.graph) y
    change finiteGraphWeightIntegrand M 1 G (y ∘ e.symm) =
      finiteGraphWeightIntegrand M 1 (D.2 B).2.graph y at hiso
    rw [← hiso]
    simp only [v, e, Equiv.symm_apply_apply]
    rw [fieldGraphWeightIntegrand_zero_eq_finiteGraphWeightIntegrand_one]
    rfl
  calc
    (∫ y : B.1 → S, attachmentBlockIntegrand M roots D B y
        ∂Measure.pi (fun _ : B.1 ↦ M.mu)) =
      ∫ y : B.1 → S,
        M.kernel (roots (D.2 B).1)
            ((fun j : Fin B.1.card ↦ y (e.symm j)) v) *
          M.fieldGraphWeightIntegrand 0 G
            (fun j : Fin B.1.card ↦ y (e.symm j))
        ∂Measure.pi (fun _ : B.1 ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ z : Fin B.1.card → S,
        M.kernel (roots (D.2 B).1) (z v) *
          M.fieldGraphWeightIntegrand 0 G z
        ∂Measure.pi (fun _ : Fin B.1.card ↦ M.mu) := by
      exact (integral_pi_reindex M.mu e
        (fun z : Fin B.1.card → S ↦
          M.kernel (roots (D.2 B).1) (z v) *
            M.fieldGraphWeightIntegrand 0 G z)).symm
    _ = _ := by
      simpa only [G, v, LabelledRootBranch.profileMap] using
        M.parentKernelWeightedFinGraphIntegral_eq_action G v
          (roots (D.2 B).1)

/-- Pointwise factorisation of the actual assembled zero-field integrand. -/
theorem finiteGraphWeightIntegrand_assembleGraph
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) :
    finiteGraphWeightIntegrand M 1 (D.assembleGraph H)
        (Sum.elim roots off) =
      M.graphWeightIntegrand 1 H roots *
        ∏ B : D.1.parts,
          attachmentBlockIntegrand M roots D B (fun i ↦ off i.1) := by
  classical
  rw [finiteGraphWeightIntegrand_eq_vertex_mul_edge]
  rw [LabelledCoreForestAttachment.assembleGraph_edge_product H D]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [finpartition_prod_univ D.1
    (fun i : Fin n ↦ Real.exp (-M.degreeFunction (off i)))]
  simp_rw [finiteEdgeFactor_coreHom M H D roots off]
  simp_rw [finiteEdgeFactor_branchHom M H D roots off]
  simp_rw [finiteEdgeFactor_rootEdge M D roots off]
  rw [← prod_edgeFinset_eq_prod_edgeSet H]
  simp_rw [← prod_edgeFinset_eq_prod_edgeSet]
  unfold attachmentBlockIntegrand
  simp_rw [finiteGraphWeightIntegrand_eq_vertex_mul_edge]
  unfold CompactBJRModel.graphWeightIntegrand
  simp only [one_mul, neg_mul]
  simp_rw [edgeFactor_one_eq_finiteEdgeFactor]
  simp_rw [Finset.prod_mul_distrib]
  ring

/-- The arbitrary finite assembled integrand is continuous. -/
theorem continuous_finiteGraphWeightIntegrand_assembleGraph
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    Continuous
      (finiteGraphWeightIntegrand M 1 (D.assembleGraph H)) := by
  classical
  unfold finiteGraphWeightIntegrand
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact (continuous_const.mul
      (M.degreeFunction.continuous.comp (continuous_apply i))).rexp
  · apply continuous_finsetProd
    intro e _
    induction e using Sym2.inductionOn with
    | _ i j =>
        exact continuous_const.mul
          (M.kernel.toContinuousMap.continuous.comp
            ((continuous_apply i).prodMk (continuous_apply j)))

/-- Exact fixed-core, fixed-attachment factorisation of the genuine
annealed zero-field graph weight. -/
theorem finiteGraphWeight_assembleGraph
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    finiteGraphWeight M 1 (D.assembleGraph H) =
      ∫ roots : Fin q → S,
        M.graphWeightIntegrand 1 H roots *
          M.labelledCoreForestAttachmentWeight roots D
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  classical
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin q ⊕ Fin n ↦ S)
  let F : ((Fin q → S) × (Fin n → S)) → ℝ := fun p ↦
    finiteGraphWeightIntegrand M 1 (D.assembleGraph H) (e.symm p)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu))
      ((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
        (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin q ⊕ Fin n ↦ M.mu)
  have hIntSource : Integrable
      (finiteGraphWeightIntegrand M 1 (D.assembleGraph H))
      (Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu)) :=
    (continuous_finiteGraphWeightIntegrand_assembleGraph M H D).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hcomp : F ∘ e =
      finiteGraphWeightIntegrand M 1 (D.assembleGraph H) := by
    funext x
    simp [F, e]
  have hInt : Integrable F
      ((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
        (Measure.pi (fun _ : Fin n ↦ M.mu))) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    simpa only [hcomp] using hIntSource
  unfold finiteGraphWeight
  calc
    (∫ x : (Fin q ⊕ Fin n) → S,
        finiteGraphWeightIntegrand M 1 (D.assembleGraph H) x
        ∂Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu)) =
      ∫ x : (Fin q ⊕ Fin n) → S, F (e x)
        ∂Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (congrFun hcomp x).symm)
    _ =
      ∫ p : (Fin q → S) × (Fin n → S), F p
        ∂((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
          (Measure.pi (fun _ : Fin n ↦ M.mu))) := by
      exact hmp.integral_comp' F
    _ = ∫ roots : Fin q → S,
        ∫ off : Fin n → S, F (roots, off)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu)
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) :=
      integral_prod _ hInt
    _ = ∫ roots : Fin q → S,
        M.graphWeightIntegrand 1 H roots *
          ∏ B : D.1.parts,
            M.kernel.action M.mu
              (LabelledRootBranch.profileMap M (D.2 B).2)
              (roots (D.2 B).1)
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with roots
      have hF (off : Fin n → S) :
          F (roots, off) =
            M.graphWeightIntegrand 1 H roots *
              ∏ B : D.1.parts,
                attachmentBlockIntegrand M roots D B (fun i ↦ off i.1) := by
        change finiteGraphWeightIntegrand M 1 (D.assembleGraph H)
            (Sum.elim roots off) = _
        exact finiteGraphWeightIntegrand_assembleGraph M H D roots off
      calc
        (∫ off : Fin n → S, F (roots, off)
            ∂Measure.pi (fun _ : Fin n ↦ M.mu)) =
          M.graphWeightIntegrand 1 H roots *
            ∫ off : Fin n → S,
              ∏ B : D.1.parts,
                attachmentBlockIntegrand M roots D B (fun i ↦ off i.1)
              ∂Measure.pi (fun _ : Fin n ↦ M.mu) := by
          simp_rw [hF]
          rw [integral_const_mul]
        _ = M.graphWeightIntegrand 1 H roots *
            ∏ B : D.1.parts,
              ∫ y : B.1 → S,
                attachmentBlockIntegrand M roots D B y
                ∂Measure.pi (fun _ : B.1 ↦ M.mu) := by
          rw [integral_finpartition_prod_eq_prod]
        _ = _ := by
          congr 1
          apply Fintype.prod_congr
          intro B
          exact integral_attachmentBlockIntegrand_eq_kernelAction M roots D B
    _ = _ := by
      rfl

/-- The attachment weight is continuous in the ordered vector of core
types.  This makes the finite sum over attachment data interchangeable with
the remaining core integral. -/
theorem continuous_labelledCoreForestAttachmentWeight
    (M : CompactBJRModel S) {q n : ℕ}
    (D : LabelledCoreForestAttachment q n) :
    Continuous
      (fun roots : Fin q → S ↦
        M.labelledCoreForestAttachmentWeight roots D) := by
  classical
  unfold CompactBJRModel.labelledCoreForestAttachmentWeight
  apply continuous_finsetProd
  intro B _
  exact (M.kernel.action M.mu
    (LabelledRootBranch.profileMap M (D.2 B).2)).continuous.comp
      (continuous_apply (D.2 B).1)

/-- Summing the genuine assembled graphs for one fixed ordered core now
interfaces directly with the existing labelled-forest exponential formula. -/
theorem sum_finiteGraphWeight_assembleGraph_eq_exp_coeff
    (M : CompactBJRModel S) {q : ℕ}
    (H : SimpleGraph (Fin q)) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        finiteGraphWeight M 1 (D.assembleGraph H)) =
      ∫ roots : Fin q → S,
        M.graphWeightIntegrand 1 H roots *
          ((n.factorial : ℝ) * PowerSeries.coeff n
            (PowerSeries.subst (M.coreBranchActionSeries roots)
              (PowerSeries.exp ℝ)))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  classical
  let f : LabelledCoreForestAttachment q n → (Fin q → S) → ℝ :=
    fun D roots ↦ M.graphWeightIntegrand 1 H roots *
      M.labelledCoreForestAttachmentWeight roots D
  have hf (D : LabelledCoreForestAttachment q n) : Integrable (f D)
      (Measure.pi (fun _ : Fin q ↦ M.mu)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (M.graphWeightIntegrand_continuous 1 H).mul
        (continuous_labelledCoreForestAttachmentWeight M D)
    · exact isClosed_closure.isCompact
  calc
    (∑ D : LabelledCoreForestAttachment q n,
        finiteGraphWeight M 1 (D.assembleGraph H)) =
      ∑ D : LabelledCoreForestAttachment q n,
        ∫ roots : Fin q → S, f D roots
          ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      apply Fintype.sum_congr
      intro D
      exact finiteGraphWeight_assembleGraph M H D
    _ = ∫ roots : Fin q → S,
        ∑ D : LabelledCoreForestAttachment q n, f D roots
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      exact (integral_finsetSum Finset.univ
        (fun D _ ↦ hf D)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with roots
      unfold f
      rw [← Finset.mul_sum]
      rw [M.sum_labelledCoreForestAttachmentWeight_eq_exp_coeff roots n]

end GraphCore
end PerronWright
