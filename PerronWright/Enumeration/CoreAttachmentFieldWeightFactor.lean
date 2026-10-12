import PerronWright.Enumeration.CoreAttachmentWeightFactor
import PerronWright.Enumeration.FieldRootedTreeFormal

/-!
# Complex-field rooted forests attached to a fixed ordered core

This file is the genuine complex-field counterpart of the finite attachment
sum in `CoreForestAttachments`.  It uses only the already proved finite
field-rooted graph profiles and the purely finite labelled-partition identity.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Literal complex-field weight of a rooted forest attached to fixed ordered
core types.  Core vertex and core edge factors are not included. -/
def CompactBJRModel.complexLabelledCoreForestAttachmentWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (roots : Fin q → S) (D : LabelledCoreForestAttachment q n) : ℂ :=
  ∏ B : D.1.parts,
    M.kernel.complexAction M.mu
      (FieldRootedTree.branchProfileMap M g (D.2 B).2)
      (roots (D.2 B).1)

/-- A fixed rooted finite graph profile is entire in the external field,
also in the arbitrary nonempty `Fin k` wrapper used by attachment blocks. -/
theorem FieldRootedTree.analyticAt_fixedRootedFinGraphProfileMap
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) (v : Fin k) :
    AnalyticAt ℂ (fun h ↦
      FieldRootedTree.fixedRootedFinGraphProfileMap M h H v) g := by
  cases k with
  | zero => exact Fin.elim0 v
  | succ n =>
      exact FieldRootedTree.analyticAt_fixedRootedGraphProfileMap M g H v

/-- The genuine profile of one independently labelled rooted branch is
entire in the external field. -/
theorem FieldRootedTree.analyticAt_branchProfileMap
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {n : ℕ} {B : Finset (Fin n)} (T : LabelledRootBranch B) :
    AnalyticAt ℂ (fun h ↦ FieldRootedTree.branchProfileMap M h T) g := by
  exact FieldRootedTree.analyticAt_fixedRootedFinGraphProfileMap M g _ _

/-- Sum the genuine complex-field rooted tree carried by a fixed label block,
then apply its parent edge at a fixed core type. -/
theorem CompactBJRModel.sum_fieldRootBranch_kernelAction_eq_factorial_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (B : Finset (Fin n)) (root : S) :
    (∑ T : LabelledRootBranch B,
        M.kernel.complexAction M.mu
          (FieldRootedTree.branchProfileMap M g T) root) =
      (B.card.factorial : ℂ) *
        PowerSeries.coeff B.card
          (M.complexKernelActionPowerSeries (FieldRootedTree.series M g)) root := by
  have h := FieldRootedTree.sum_branch_kernelAction_eq_factorial_coeff M g B
  simpa only [ContinuousMap.sum_apply,
    ContinuousKernel.complexActionCLM_apply,
    ContinuousMap.mul_apply, ContinuousMap.natCast_apply] using
    congrArg (fun f : C(S, ℂ) ↦ f root) h

/-- Aggregate branch-action series for all possible attachment roots among a
fixed ordered core, in the genuine complex field. -/
def CompactBJRModel.complexCoreBranchActionSeries
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦
    ∑ i : Fin q,
      PowerSeries.coeff k
        (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
        (roots i)

@[simp] theorem CompactBJRModel.complexCoreBranchActionSeries_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) (k : ℕ) :
    PowerSeries.coeff k (M.complexCoreBranchActionSeries g roots) =
      ∑ i : Fin q,
        PowerSeries.coeff k
          (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
          (roots i) := by
  simp only [CompactBJRModel.complexCoreBranchActionSeries,
    PowerSeries.coeff_mk]

theorem CompactBJRModel.complexCoreBranchActionSeries_constantCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) :
    PowerSeries.constantCoeff (M.complexCoreBranchActionSeries g roots) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [M.complexCoreBranchActionSeries_coeff]
  have hzero : PowerSeries.constantCoeff
      (M.complexKernelActionPowerSeries (FieldRootedTree.series M g)) = 0 := by
    rw [M.complexKernelActionPowerSeries_constantCoeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [FieldRootedTree.series_coeff_zero]
    exact (M.kernel.complexActionCLM M.mu).map_zero
  rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hzero
  simp only [hzero, ContinuousMap.zero_apply, Finset.sum_const_zero]

/-- Finite regrouping of all complex-field coloured rooted-tree blocks into
the labelled partition weight of the aggregate branch series. -/
theorem CompactBJRModel.sum_complexLabelledCoreForestAttachmentWeight_eq_partition
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        M.complexLabelledCoreForestAttachmentWeight g roots D) =
      labelledPartitionWeight
        (fun k ↦ (k.factorial : ℂ) *
          PowerSeries.coeff k (M.complexCoreBranchActionSeries g roots))
        (Finset.univ : Finset (Fin n)) := by
  classical
  unfold CompactBJRModel.complexLabelledCoreForestAttachmentWeight
  rw [sum_labelledCoreForestAttachment_product
    (w := fun B i T ↦
      M.kernel.complexAction M.mu
        (FieldRootedTree.branchProfileMap M g T) (roots i))]
  unfold labelledPartitionWeight
  apply Fintype.sum_congr
  intro P
  rw [← Finset.prod_coe_sort P.parts
    (fun B ↦ (B.card.factorial : ℂ) *
      PowerSeries.coeff B.card (M.complexCoreBranchActionSeries g roots))]
  apply Fintype.prod_congr
  intro B
  rw [Fintype.sum_prod_type]
  simp_rw [M.sum_fieldRootBranch_kernelAction_eq_factorial_coeff g B.1]
  rw [← Finset.mul_sum]
  exact congrArg ((B.1.card.factorial : ℂ) * ·)
    (M.complexCoreBranchActionSeries_coeff g roots B.1.card).symm

/-- Exact complex-field exponential formula for all labelled rooted forests
attached to a fixed ordered core. -/
theorem CompactBJRModel.sum_complexLabelledCoreForestAttachmentWeight_eq_exp_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        M.complexLabelledCoreForestAttachmentWeight g roots D) =
      (n.factorial : ℂ) * PowerSeries.coeff n
        (PowerSeries.subst (M.complexCoreBranchActionSeries g roots)
          (PowerSeries.exp ℂ)) := by
  rw [M.sum_complexLabelledCoreForestAttachmentWeight_eq_partition g roots n]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    labelledPartitionWeight_eq_factorial_mul_subst_exp_coeff
      (M.complexCoreBranchActionSeries g roots)
      (M.complexCoreBranchActionSeries_constantCoeff g roots)
      (Finset.univ : Finset (Fin n))

namespace GraphCore

/-- A complex graph integrand on an arbitrary finite vertex type, with an
arbitrary continuous vertex factor. -/
def finiteComplexGraphIntegrand (M : CompactBJRModel S) (q : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → S) : ℂ :=
  (∏ v : V, q (x v)) *
    ∏ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun i j ↦ (M.kernel (x i) (x j) : ℂ), by
        intro i j
        exact congrArg (fun r : ℝ ↦ (r : ℂ))
          (M.kernel.symmetric (x i) (x j))⟩ e

/-- The arbitrary-finite-type integrand specializes to the already used
`Fin k` generic field integrand. -/
theorem finiteComplexGraphIntegrand_fin_eq
    (M : CompactBJRModel S) (q : C(S, ℂ)) {k : ℕ}
    (G : SimpleGraph (Fin k)) (x : Fin k → S) :
    finiteComplexGraphIntegrand M q G x =
      FieldRootedTree.finiteIntegrand M q G x := by
  classical
  unfold finiteComplexGraphIntegrand FieldRootedTree.finiteIntegrand
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ i j =>
      change (M.kernel (x i) (x j) : ℂ) =
        (M.edgeFactor 1 x s(i,j) : ℂ)
      simp only [CompactBJRModel.edgeFactor_mk, one_mul]

/-- Generic complex graph integrands are invariant under simultaneous graph
and type-coordinate relabelling. -/
theorem finiteComplexGraphIntegrand_iso
    (M : CompactBJRModel S) (q : C(S, ℂ))
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) (x : W → S) :
    finiteComplexGraphIntegrand M q G (x ∘ e) =
      finiteComplexGraphIntegrand M q H x := by
  unfold finiteComplexGraphIntegrand
  congr 1
  · exact Equiv.prod_comp e.toEquiv (fun i : W ↦ q (x i))
  · apply Finset.prod_bijective (sym2Congr e.toEquiv)
    · exact (sym2Congr e.toEquiv).bijective
    · intro a
      induction a using Sym2.inductionOn with
      | _ i j =>
          simp only [sym2Congr_mk, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet]
          exact e.map_adj_iff.symm
    · intro a _
      induction a using Sym2.inductionOn with
      | _ i j => rfl

/-- Integrated arbitrary-finite-type complex graph weight. -/
def finiteComplexGraphWeight (M : CompactBJRModel S) (q : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℂ := by
  classical
  exact ∫ x : V → S, finiteComplexGraphIntegrand M q G x
    ∂Measure.pi (fun _ : V ↦ M.mu)

/-- The generic integrated weight specializes to the project's genuine
complex external-field weight. -/
theorem finiteComplexGraphWeight_vertexFactor_fin_eq
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (G : SimpleGraph (Fin k)) :
    finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g) G =
      M.complexFieldGraphWeight g G := by
  classical
  unfold finiteComplexGraphWeight CompactBJRModel.complexFieldGraphWeight
  change (∫ x : Fin k → S,
      finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g) G x
        ∂Measure.pi (fun _ : Fin k ↦ M.mu)) =
    ∫ x : Fin k → S, M.complexFieldGraphIntegrand g G x
      ∂Measure.pi (fun _ : Fin k ↦ M.mu)
  apply integral_congr_ae
  filter_upwards [] with x
  rw [finiteComplexGraphIntegrand_fin_eq]
  exact (FieldRootedTree.complexFieldGraphIntegrand_eq_finiteIntegrand
    M g G x).symm

/-- Arbitrary-finite complex graph weights are invariant under a genuine
graph isomorphism, with the iid product law reindexed explicitly. -/
theorem finiteComplexGraphWeight_iso
    (M : CompactBJRModel S) (qv : C(S, ℂ))
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    finiteComplexGraphWeight M qv G = finiteComplexGraphWeight M qv H := by
  classical
  unfold finiteComplexGraphWeight
  rw [FieldRootedTree.integral_pi_reindex_complex M.mu e.toEquiv]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (finiteComplexGraphIntegrand_iso M qv H G e.symm x).symm

/-- The deterministic core/off-core split preserves the genuine complex
external-field graph weight. -/
theorem finiteComplexGraphWeight_splitGraph_eq_complexFieldGraphWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj] :
    finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
        (greatestTwoCoreSplitGraph G) =
      M.complexFieldGraphWeight g G := by
  rw [finiteComplexGraphWeight_iso M (FieldRootedTree.vertexFactor M g)
    (greatestTwoCoreSplitGraph G) G (greatestTwoCoreSplitIso G)]
  exact finiteComplexGraphWeight_vertexFactor_fin_eq M g G

private def complexFiniteEdgeFactor (M : CompactBJRModel S)
    {V : Type*} (x : V → S) (e : Sym2 V) : ℂ :=
  Sym2.lift ⟨fun i j ↦ (M.kernel (x i) (x j) : ℂ), by
    intro i j
    exact congrArg (fun r : ℝ ↦ (r : ℂ))
      (M.kernel.symmetric (x i) (x j))⟩ e

@[simp] private theorem complexFiniteEdgeFactor_mk
    (M : CompactBJRModel S) {V : Type*} (x : V → S) (i j : V) :
    complexFiniteEdgeFactor M x s(i,j) = (M.kernel (x i) (x j) : ℂ) := rfl

private theorem complexFiniteEdgeFactor_coreHom
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) (e : H.edgeSet) :
    complexFiniteEdgeFactor M (Sum.elim roots off)
        ((D.coreHom H).mapEdgeSet e).1 =
      complexFiniteEdgeFactor M roots e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j => rfl

private theorem complexFiniteEdgeFactor_branchHom
    (M : CompactBJRModel S) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S)
    (B : D.1.parts) (e : (D.2 B).2.graph.edgeSet) :
    complexFiniteEdgeFactor M (Sum.elim roots off)
        ((D.branchHom H B).mapEdgeSet e).1 =
      complexFiniteEdgeFactor M (fun i : B.1 ↦ off i.1) e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ i j => rfl

private theorem complexFiniteEdgeFactor_rootEdge
    (M : CompactBJRModel S) {q n : ℕ}
    (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) (B : D.1.parts) :
    complexFiniteEdgeFactor M (Sum.elim roots off)
        s(Sum.inl (D.2 B).1, Sum.inr (D.2 B).2.root.1) =
      (M.kernel (roots (D.2 B).1) (off (D.2 B).2.root.1) : ℂ) := rfl

private theorem finiteComplexGraphIntegrand_eq_vertex_mul_edge
    (M : CompactBJRModel S) (qv : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → S) :
    finiteComplexGraphIntegrand M qv G x =
      (∏ v : V, qv (x v)) *
        ∏ e ∈ G.edgeFinset, complexFiniteEdgeFactor M x e := by
  rfl

private theorem finpartition_prod_univ_complex
    {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (f : Fin n → ℂ) :
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

/-- Literal contribution of one complex-field rooted-tree block after the
ordered core types have been fixed. -/
def complexAttachmentBlockIntegrand
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (roots : Fin q → S) (D : LabelledCoreForestAttachment q n)
    (B : D.1.parts) (y : B.1 → S) : ℂ :=
  (M.kernel (roots (D.2 B).1) (y (D.2 B).2.root) : ℂ) *
    finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
      (D.2 B).2.graph y

/-- Pointwise factorisation of the actual assembled complex-field
integrand into its core block and independent rooted-tree blocks. -/
theorem finiteComplexGraphIntegrand_assembleGraph
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (roots : Fin q → S) (off : Fin n → S) :
    finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph H) (Sum.elim roots off) =
      finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
          H roots *
        ∏ B : D.1.parts,
          complexAttachmentBlockIntegrand M g roots D B
            (fun i ↦ off i.1) := by
  classical
  rw [finiteComplexGraphIntegrand_eq_vertex_mul_edge]
  rw [LabelledCoreForestAttachment.assembleGraph_edge_product H D]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [finpartition_prod_univ_complex D.1
    (fun i : Fin n ↦ FieldRootedTree.vertexFactor M g (off i))]
  simp_rw [complexFiniteEdgeFactor_coreHom M H D roots off]
  simp_rw [complexFiniteEdgeFactor_branchHom M H D roots off]
  simp_rw [complexFiniteEdgeFactor_rootEdge M D roots off]
  rw [← prod_edgeFinset_eq_prod_edgeSet H]
  simp_rw [← prod_edgeFinset_eq_prod_edgeSet]
  unfold complexAttachmentBlockIntegrand
  simp_rw [finiteComplexGraphIntegrand_eq_vertex_mul_edge]
  simp_rw [Finset.prod_mul_distrib]
  ring

private theorem finiteComplexGraphIntegrand_vertexFactor_eq_field
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (G : SimpleGraph (Fin k)) (x : Fin k → S) :
    finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g) G x =
      M.complexFieldGraphIntegrand g G x := by
  rw [finiteComplexGraphIntegrand_fin_eq]
  exact (FieldRootedTree.complexFieldGraphIntegrand_eq_finiteIntegrand
    M g G x).symm

/-- A fixed rooted-tree block integrates to the genuine complex-field branch
profile followed by its parent kernel action. -/
theorem integral_complexAttachmentBlockIntegrand_eq_kernelAction
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (roots : Fin q → S) (D : LabelledCoreForestAttachment q n)
    (B : D.1.parts) :
    (∫ y : B.1 → S, complexAttachmentBlockIntegrand M g roots D B y
      ∂Measure.pi (fun _ : B.1 ↦ M.mu)) =
      M.kernel.complexAction M.mu
        (FieldRootedTree.branchProfileMap M g (D.2 B).2)
        (roots (D.2 B).1) := by
  classical
  let e := B.1.equivFin
  let G : SimpleGraph (Fin B.1.card) :=
    (D.2 B).2.graph.comap (e.symm : Fin B.1.card → B.1)
  let v : Fin B.1.card := e (D.2 B).2.root
  have hpoint (y : B.1 → S) :
      complexAttachmentBlockIntegrand M g roots D B y =
        (M.kernel (roots (D.2 B).1)
            ((fun j : Fin B.1.card ↦ y (e.symm j)) v) : ℂ) *
          M.complexFieldGraphIntegrand g G
            (fun j : Fin B.1.card ↦ y (e.symm j)) := by
    unfold complexAttachmentBlockIntegrand
    have hiso := finiteComplexGraphIntegrand_iso M
      (FieldRootedTree.vertexFactor M g) G (D.2 B).2.graph
      (SimpleGraph.Iso.comap e.symm (D.2 B).2.graph) y
    change finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        G (y ∘ e.symm) =
      finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        (D.2 B).2.graph y at hiso
    rw [← hiso]
    simp only [v, e, Equiv.symm_apply_apply]
    congr 1
    change finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        G (fun j : Fin B.1.card ↦ y (B.1.equivFin.symm j)) =
      M.complexFieldGraphIntegrand g G
        (fun j : Fin B.1.card ↦ y (B.1.equivFin.symm j))
    exact finiteComplexGraphIntegrand_vertexFactor_eq_field M g G _
  calc
    (∫ y : B.1 → S, complexAttachmentBlockIntegrand M g roots D B y
        ∂Measure.pi (fun _ : B.1 ↦ M.mu)) =
      ∫ y : B.1 → S,
        (M.kernel (roots (D.2 B).1)
            ((fun j : Fin B.1.card ↦ y (e.symm j)) v) : ℂ) *
          M.complexFieldGraphIntegrand g G
            (fun j : Fin B.1.card ↦ y (e.symm j))
        ∂Measure.pi (fun _ : B.1 ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ z : Fin B.1.card → S,
        (M.kernel (roots (D.2 B).1) (z v) : ℂ) *
          M.complexFieldGraphIntegrand g G z
        ∂Measure.pi (fun _ : Fin B.1.card ↦ M.mu) := by
      exact (FieldRootedTree.integral_pi_reindex_complex M.mu e
        (fun z : Fin B.1.card → S ↦
          (M.kernel (roots (D.2 B).1) (z v) : ℂ) *
            M.complexFieldGraphIntegrand g G z)).symm
    _ = _ := by
      simpa only [G, v, FieldRootedTree.branchProfileMap] using
        FieldRootedTree.parentKernelWeightedFinGraphIntegral_eq_action
          M g G v (roots (D.2 B).1)

private theorem integral_finpartition_prod_eq_prod_complex'
    {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (P : Finpartition (Finset.univ : Finset ι))
    (μ : Measure X) [SigmaFinite μ]
    (F : (B : P.parts) → (B.1 → X) → ℂ) :
    (∫ z : ι → X, ∏ B : P.parts, F B (fun i ↦ z i.1)
      ∂Measure.pi (fun _ : ι ↦ μ)) =
      ∏ B : P.parts, ∫ y : B.1 → X, F B y
        ∂Measure.pi (fun _ : B.1 ↦ μ) := by
  calc
    _ = ∫ u : (B : P.parts) → B.1 → X, ∏ B : P.parts, F B (u B)
        ∂Measure.pi (fun B : P.parts ↦ Measure.pi (fun _ : B.1 ↦ μ)) := by
      rw [← (measurePreserving_finpartitionPi P μ).integral_comp']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z ↦ by
        apply Finset.prod_congr rfl
        intro B _
        congr 1
        funext i
        exact (finpartitionPiMeasurableEquiv_apply P z B i).symm)
    _ = _ := integral_fintype_prod_eq_prod F

/-- Continuity of the arbitrary finite complex graph integrand. -/
theorem continuous_finiteComplexGraphIntegrand
    (M : CompactBJRModel S) (qv : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Continuous (finiteComplexGraphIntegrand M qv G) := by
  classical
  unfold finiteComplexGraphIntegrand
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact qv.continuous.comp (continuous_apply i)
  · apply continuous_finsetProd
    intro e _
    induction e using Sym2.inductionOn with
    | _ i j =>
        exact Complex.continuous_ofReal.comp
          (M.kernel.toContinuousMap.continuous.comp
            ((continuous_apply i).prodMk (continuous_apply j)))

/-- Exact fixed-core, fixed-attachment factorisation of the genuine
complex-field graph weight. -/
theorem finiteComplexGraphWeight_assembleGraph
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph H) =
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
            H roots *
          M.complexLabelledCoreForestAttachmentWeight g roots D
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  classical
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin q ⊕ Fin n ↦ S)
  let F : ((Fin q → S) × (Fin n → S)) → ℂ := fun p ↦
    finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
      (D.assembleGraph H) (e.symm p)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu))
      ((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
        (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin q ⊕ Fin n ↦ M.mu)
  have hIntSource : Integrable
      (finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph H))
      (Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu)) :=
    (continuous_finiteComplexGraphIntegrand M
      (FieldRootedTree.vertexFactor M g) (D.assembleGraph H)).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
  have hcomp : F ∘ e =
      finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph H) := by
    funext x
    simp [F, e]
  have hInt : Integrable F
      ((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
        (Measure.pi (fun _ : Fin n ↦ M.mu))) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    simpa only [hcomp] using hIntSource
  unfold finiteComplexGraphWeight
  calc
    (∫ x : (Fin q ⊕ Fin n) → S,
        finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
          (D.assembleGraph H) x
        ∂Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu)) =
      ∫ x : (Fin q ⊕ Fin n) → S, F (e x)
        ∂Measure.pi (fun _ : Fin q ⊕ Fin n ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (congrFun hcomp x).symm)
    _ = ∫ p : (Fin q → S) × (Fin n → S), F p
        ∂((Measure.pi (fun _ : Fin q ↦ M.mu)).prod
          (Measure.pi (fun _ : Fin n ↦ M.mu))) := by
      exact hmp.integral_comp' F
    _ = ∫ roots : Fin q → S,
        ∫ off : Fin n → S, F (roots, off)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu)
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) :=
      integral_prod _ hInt
    _ = ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
            H roots *
          ∏ B : D.1.parts,
            M.kernel.complexAction M.mu
              (FieldRootedTree.branchProfileMap M g (D.2 B).2)
              (roots (D.2 B).1)
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with roots
      have hF (off : Fin n → S) :
          F (roots, off) =
            finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
                H roots *
              ∏ B : D.1.parts,
                complexAttachmentBlockIntegrand M g roots D B
                  (fun i ↦ off i.1) := by
        change finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) (D.assembleGraph H)
            (Sum.elim roots off) = _
        exact finiteComplexGraphIntegrand_assembleGraph M g H D roots off
      calc
        (∫ off : Fin n → S, F (roots, off)
            ∂Measure.pi (fun _ : Fin n ↦ M.mu)) =
          finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
              H roots *
            ∫ off : Fin n → S,
              ∏ B : D.1.parts,
                complexAttachmentBlockIntegrand M g roots D B
                  (fun i ↦ off i.1)
              ∂Measure.pi (fun _ : Fin n ↦ M.mu) := by
          simp_rw [hF]
          rw [integral_const_mul]
        _ = finiteComplexGraphIntegrand M
              (FieldRootedTree.vertexFactor M g) H roots *
            ∏ B : D.1.parts,
              ∫ y : B.1 → S,
                complexAttachmentBlockIntegrand M g roots D B y
                ∂Measure.pi (fun _ : B.1 ↦ M.mu) := by
          rw [integral_finpartition_prod_eq_prod_complex']
        _ = _ := by
          congr 1
          apply Fintype.prod_congr
          intro B
          exact integral_complexAttachmentBlockIntegrand_eq_kernelAction
            M g roots D B
    _ = _ := by
      rfl

/-- The genuine complex-field attachment weight is continuous in the ordered
vector of core types. -/
theorem continuous_complexLabelledCoreForestAttachmentWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q n : ℕ}
    (D : LabelledCoreForestAttachment q n) :
    Continuous (fun roots : Fin q → S ↦
      M.complexLabelledCoreForestAttachmentWeight g roots D) := by
  classical
  unfold CompactBJRModel.complexLabelledCoreForestAttachmentWeight
  apply continuous_finsetProd
  intro B _
  exact (M.kernel.complexAction M.mu
    (FieldRootedTree.branchProfileMap M g (D.2 B).2)).continuous.comp
      (continuous_apply (D.2 B).1)

/-- Summing genuine complex-field assembled graph weights for one fixed
ordered core gives the exact labelled-forest exponential coefficient. -/
theorem sum_finiteComplexGraphWeight_assembleGraph_eq_exp_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (H : SimpleGraph (Fin q)) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
          (D.assembleGraph H)) =
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
            H roots *
          ((n.factorial : ℂ) * PowerSeries.coeff n
            (PowerSeries.subst (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ)))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  classical
  let f : LabelledCoreForestAttachment q n → (Fin q → S) → ℂ :=
    fun D roots ↦
      finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
          H roots *
        M.complexLabelledCoreForestAttachmentWeight g roots D
  have hf (D : LabelledCoreForestAttachment q n) : Integrable (f D)
      (Measure.pi (fun _ : Fin q ↦ M.mu)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_finiteComplexGraphIntegrand M
        (FieldRootedTree.vertexFactor M g) H).mul
          (continuous_complexLabelledCoreForestAttachmentWeight M g D)
    · exact isClosed_closure.isCompact
  calc
    (∑ D : LabelledCoreForestAttachment q n,
        finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
          (D.assembleGraph H)) =
      ∑ D : LabelledCoreForestAttachment q n,
        ∫ roots : Fin q → S, f D roots
          ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      apply Fintype.sum_congr
      intro D
      exact finiteComplexGraphWeight_assembleGraph M g H D
    _ = ∫ roots : Fin q → S,
        ∑ D : LabelledCoreForestAttachment q n, f D roots
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
      exact (integral_finsetSum Finset.univ (fun D _ ↦ hf D)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with roots
      unfold f
      rw [← Finset.mul_sum]
      rw [M.sum_complexLabelledCoreForestAttachmentWeight_eq_exp_coeff
        g roots n]

/-- The canonical forward core/forest decomposition of an arbitrary labelled
connected positive-surplus graph preserves its genuine complex field weight. -/
theorem finiteComplexGraphWeight_forwardArbitraryCoreAttachment
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {k ell : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = k + ell) :
    let K := greatestTwoCoreSplitGraph G
    letI : DecidableRel K.Adj := fun i j ↦ Classical.propDecidable (K.Adj i j)
    let D := forwardSplitCoreAttachment K
      ((greatestTwoCoreSplitIso G).connected_iff.mpr hconn)
      hell
      (by
        rw [(greatestTwoCoreSplitIso G).card_edgeFinset_eq]
        have hcard :
            Fintype.card
              (Fin (greatestTwoCoreSize G) ⊕
                Fin (greatestTwoCoreComplementSize G)) = k := by
          simpa using Fintype.card_congr (greatestTwoCoreSplitEquiv G)
        rw [hcard]
        exact hs)
      (greatestTwoCore_splitGraph_eq_range_inl G)
    finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph
          (K.comap
            (Sum.inl : Fin (greatestTwoCoreSize G) →
              Fin (greatestTwoCoreSize G) ⊕
                Fin (greatestTwoCoreComplementSize G)))) =
      M.complexFieldGraphWeight g G := by
  dsimp only
  rw [assembleGraph_forwardArbitraryCoreAttachment G hconn hell hs]
  exact finiteComplexGraphWeight_splitGraph_eq_complexFieldGraphWeight M g G

/-- The genuine complex field weight of an arbitrary labelled connected
positive-surplus graph is the fixed-core integral for its canonical split. -/
theorem complexFieldGraphWeight_eq_integral_forwardArbitraryCoreAttachment
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {k ell : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = k + ell) :
    let K := greatestTwoCoreSplitGraph G
    letI : DecidableRel K.Adj := fun i j ↦ Classical.propDecidable (K.Adj i j)
    let D := forwardSplitCoreAttachment K
      ((greatestTwoCoreSplitIso G).connected_iff.mpr hconn)
      hell
      (by
        rw [(greatestTwoCoreSplitIso G).card_edgeFinset_eq]
        have hcard :
            Fintype.card
              (Fin (greatestTwoCoreSize G) ⊕
                Fin (greatestTwoCoreComplementSize G)) = k := by
          simpa using Fintype.card_congr (greatestTwoCoreSplitEquiv G)
        rw [hcard]
        exact hs)
      (greatestTwoCore_splitGraph_eq_range_inl G)
    M.complexFieldGraphWeight g G =
      ∫ roots : Fin (greatestTwoCoreSize G) → S,
        finiteComplexGraphIntegrand M (FieldRootedTree.vertexFactor M g)
            (K.comap
              (Sum.inl : Fin (greatestTwoCoreSize G) →
                Fin (greatestTwoCoreSize G) ⊕
                  Fin (greatestTwoCoreComplementSize G))) roots *
          M.complexLabelledCoreForestAttachmentWeight g roots D
        ∂Measure.pi (fun _ : Fin (greatestTwoCoreSize G) ↦ M.mu) := by
  dsimp only
  rw [← finiteComplexGraphWeight_forwardArbitraryCoreAttachment
    M g G hconn hell hs]
  exact finiteComplexGraphWeight_assembleGraph M g _ _

end GraphCore

end PerronWright
