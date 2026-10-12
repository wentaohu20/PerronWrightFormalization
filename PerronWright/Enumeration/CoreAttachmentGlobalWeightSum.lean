import PerronWright.Enumeration.CoreAttachmentGlobalClassification
import PerronWright.Enumeration.CoreAttachmentFieldWeightFactor

/-!
# Global core/attachment weight sums

This module combines the deterministic global classification with
the genuine graph weights.  The `Nat.choose` factor is not an abstract fibre
cardinality: it is obtained by summing over the literal type
`CoreLabelSubset k q` and using `card_coreLabelSubset`.

The only constancy assertion used in that sum is proved below from the actual
graph isomorphism between an assembly on `Fin q ⊕ Fin n` and its relabelling
to a chosen subset of `Fin k`.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Relabelling a fixed core/attachment assembly onto a literal subset of
the original labels preserves the genuine real graph weight. -/
theorem graphWeight_assembleGraphOnCoreSubset
    (M : CompactBJRModel S) (t : ℝ) {k q n : ℕ}
    (hp : q + n = k) (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    M.graphWeight t (assembleGraphOnCoreSubset hp C H D) =
      finiteGraphWeight M t (D.assembleGraph H) := by
  rw [← finiteGraphWeight_fin_eq M t]
  exact finiteGraphWeight_iso M t
    (assembleGraphOnCoreSubset hp C H D) (D.assembleGraph H)
    (SimpleGraph.Iso.comap (coreLabelEquiv hp C).symm
      (D.assembleGraph H))

/-- Relabelling a fixed core/attachment assembly onto a literal subset of
the original labels preserves the genuine complex external-field weight. -/
theorem complexFieldGraphWeight_assembleGraphOnCoreSubset
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k q n : ℕ}
    (hp : q + n = k) (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    M.complexFieldGraphWeight g (assembleGraphOnCoreSubset hp C H D) =
      finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
        (D.assembleGraph H) := by
  rw [← finiteComplexGraphWeight_vertexFactor_fin_eq M g]
  exact finiteComplexGraphWeight_iso M
    (FieldRootedTree.vertexFactor M g)
    (assembleGraphOnCoreSubset hp C H D) (D.assembleGraph H)
    (SimpleGraph.Iso.comap (coreLabelEquiv hp C).symm
      (D.assembleGraph H))

/-- The existing forward weight theorem, stated in the notation of the
deterministic inverse used by the global equivalence. -/
theorem complexFieldGraphWeight_eq_canonicalSplitAttachment
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k ell : ℕ}
    (A : AttachmentFixedSurplusGraph k ell) :
    M.complexFieldGraphWeight g A.1 =
      finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
        ((canonicalSplitAttachment A).assembleGraph
          (canonicalSplitCore A)) := by
  classical
  have hspec := attachmentFixedSurplusGraph_spec A
  have hforward := finiteComplexGraphWeight_forwardArbitraryCoreAttachment
    M g A.1 hspec.1 (Nat.succ_pos ell) hspec.2
  dsimp only at hforward
  change finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
      ((canonicalSplitAttachment A).assembleGraph (canonicalSplitCore A)) =
        M.complexFieldGraphWeight g A.1 at hforward
  exact hforward.symm

/-- Real zero-field counterpart of the canonical forward weight identity. -/
theorem graphWeight_one_eq_canonicalSplitAttachment
    (M : CompactBJRModel S) {k ell : ℕ}
    (A : AttachmentFixedSurplusGraph k ell) :
    M.graphWeight 1 A.1 =
      finiteGraphWeight M 1
        ((canonicalSplitAttachment A).assembleGraph
          (canonicalSplitCore A)) := by
  classical
  have hspec := attachmentFixedSurplusGraph_spec A
  have hforward := finiteGraphWeight_forwardArbitraryCoreAttachment
    M A.1 hspec.1 (Nat.succ_pos ell) hspec.2
  dsimp only at hforward
  change finiteGraphWeight M 1
      ((canonicalSplitAttachment A).assembleGraph (canonicalSplitCore A)) =
        M.graphWeight 1 A.1 at hforward
  exact hforward.symm

/-- At fixed `(q,n,H,D)`, summing over the actual original core-label subsets
produces exactly the binomial relabelling multiplicity. -/
theorem sum_coreLabelSubset_graphWeight_assembleGraphOnCoreSubset
    (M : CompactBJRModel S) (t : ℝ) {k q n : ℕ}
    (hp : q + n = k) (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    (∑ C : CoreLabelSubset k q,
        M.graphWeight t (assembleGraphOnCoreSubset hp C H D)) =
      (Nat.choose k q : ℝ) * finiteGraphWeight M t (D.assembleGraph H) := by
  simp_rw [graphWeight_assembleGraphOnCoreSubset M t hp]
  rw [Finset.sum_const, Finset.card_univ, card_coreLabelSubset, nsmul_eq_mul]

/-- Complex-field version of the literal core-label-subset sum. -/
theorem sum_coreLabelSubset_complexFieldGraphWeight_assembleGraphOnCoreSubset
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k q n : ℕ}
    (hp : q + n = k) (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) :
    (∑ C : CoreLabelSubset k q,
        M.complexFieldGraphWeight g
          (assembleGraphOnCoreSubset hp C H D)) =
      (Nat.choose k q : ℂ) *
        finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
          (D.assembleGraph H) := by
  simp_rw [complexFieldGraphWeight_assembleGraphOnCoreSubset M g hp]
  rw [Finset.sum_const, Finset.card_univ, card_coreLabelSubset, nsmul_eq_mul]

/-- The complete fixed-size subset-labelled fibre sum, with the subset field
collapsed to its explicit binomial multiplicity. -/
theorem sum_subsetLabelledCoreAttachmentDatumAt_graphWeight
    (M : CompactBJRModel S) (t : ℝ) {k ell q n : ℕ}
    (hp : q + n = k) :
    (∑ X : SubsetLabelledCoreAttachmentDatumAt k ell q n,
        M.graphWeight t (subsetLabelledCoreAttachmentAssembly hp X)) =
      (Nat.choose k q : ℝ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          ∑ D : LabelledCoreForestAttachment q n,
            finiteGraphWeight M t (D.assembleGraph H.1) := by
  change
    (∑ X : CoreLabelSubset k q ×
        AdmissibleCoreAttachmentDatum ell q n,
      M.graphWeight t
        (assembleGraphOnCoreSubset hp X.1 X.2.1.1 X.2.2)) = _
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ HD : AdmissibleCoreAttachmentDatum ell q n,
        ∑ C : CoreLabelSubset k q,
          M.graphWeight t
            (assembleGraphOnCoreSubset hp C HD.1.1 HD.2)) =
        ∑ HD : AdmissibleCoreAttachmentDatum ell q n,
          (Nat.choose k q : ℝ) *
            finiteGraphWeight M t (HD.2.assembleGraph HD.1.1) := by
      apply Fintype.sum_congr
      rintro ⟨H, D⟩
      exact sum_coreLabelSubset_graphWeight_assembleGraphOnCoreSubset
        M t hp H.1 D
    _ = (Nat.choose k q : ℝ) *
        ∑ HD : AdmissibleCoreAttachmentDatum ell q n,
          finiteGraphWeight M t (HD.2.assembleGraph HD.1.1) := by
      rw [Finset.mul_sum]
    _ = (Nat.choose k q : ℝ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          ∑ D : LabelledCoreForestAttachment q n,
            finiteGraphWeight M t (D.assembleGraph H.1) := by
      apply congrArg (fun z : ℝ ↦ (Nat.choose k q : ℝ) * z)
      change
        (∑ HD : {H : SimpleGraph (Fin q) //
              IsAdmissibleAttachmentCore q ell H} ×
              LabelledCoreForestAttachment q n,
            finiteGraphWeight M t (HD.2.assembleGraph HD.1.1)) = _
      rw [Fintype.sum_prod_type]

/-- Complex-field version of the complete fixed-size subset-labelled fibre
sum. -/
theorem sum_subsetLabelledCoreAttachmentDatumAt_complexFieldGraphWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k ell q n : ℕ}
    (hp : q + n = k) :
    (∑ X : SubsetLabelledCoreAttachmentDatumAt k ell q n,
        M.complexFieldGraphWeight g
          (subsetLabelledCoreAttachmentAssembly hp X)) =
      (Nat.choose k q : ℂ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          ∑ D : LabelledCoreForestAttachment q n,
            finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
              (D.assembleGraph H.1) := by
  change
    (∑ X : CoreLabelSubset k q ×
        AdmissibleCoreAttachmentDatum ell q n,
      M.complexFieldGraphWeight g
        (assembleGraphOnCoreSubset hp X.1 X.2.1.1 X.2.2)) = _
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ HD : AdmissibleCoreAttachmentDatum ell q n,
        ∑ C : CoreLabelSubset k q,
          M.complexFieldGraphWeight g
            (assembleGraphOnCoreSubset hp C HD.1.1 HD.2)) =
        ∑ HD : AdmissibleCoreAttachmentDatum ell q n,
          (Nat.choose k q : ℂ) *
            finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
              (HD.2.assembleGraph HD.1.1) := by
      apply Fintype.sum_congr
      rintro ⟨H, D⟩
      exact
        sum_coreLabelSubset_complexFieldGraphWeight_assembleGraphOnCoreSubset
          M g hp H.1 D
    _ = (Nat.choose k q : ℂ) *
        ∑ HD : AdmissibleCoreAttachmentDatum ell q n,
          finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
            (HD.2.assembleGraph HD.1.1) := by
      rw [Finset.mul_sum]
    _ = (Nat.choose k q : ℂ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          ∑ D : LabelledCoreForestAttachment q n,
            finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
              (D.assembleGraph H.1) := by
      apply congrArg (fun z : ℂ ↦ (Nat.choose k q : ℂ) * z)
      change
        (∑ HD : {H : SimpleGraph (Fin q) //
              IsAdmissibleAttachmentCore q ell H} ×
              LabelledCoreForestAttachment q n,
            finiteComplexGraphWeight M (FieldRootedTree.vertexFactor M g)
              (HD.2.assembleGraph HD.1.1)) = _
      rw [Fintype.sum_prod_type]

/-- Complex external-field counterpart of
`connectedWeight_eq_sum_fixedSurplusGraphs`. -/
theorem complexFieldConnectedWeight_eq_sum_fixedSurplusGraphs
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k ell : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) =
      ∑ G ∈ fixedSurplusGraphs k ell,
        M.complexFieldGraphWeight g G := by
  classical
  unfold CompactBJRModel.complexFieldConnectedWeight fixedSurplusGraphs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro G _
  have heq : G.edgeFinset.card = k + (ell + 1) - 1 ↔
      G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1) := by
    simp only [Fintype.card_fin]
    omega
  simp only [heq]

/-- Exact global real-weight reindexing through the deterministic global
core/attachment equivalence, with explicit binomial relabelling factor. -/
theorem sum_fixedSurplusGraphs_graphWeight_eq_coreAttachment
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) :
    (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℝ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∑ D : LabelledCoreForestAttachment p.1.1 p.1.2,
              finiteGraphWeight M t (D.assembleGraph H.1) := by
  classical
  have hsub :
      (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G) =
        ∑ A : AttachmentFixedSurplusGraph k ell,
          M.graphWeight t A.1 := by
    exact Finset.sum_subtype (fixedSurplusGraphs k ell)
      (fun _ ↦ Iff.rfl) (fun G ↦ M.graphWeight t G)
  calc
    (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G) =
        ∑ A : AttachmentFixedSurplusGraph k ell,
          M.graphWeight t A.1 := hsub
    _ = ∑ X : AntidiagonalSubsetLabelledCoreAttachmentDatum k ell,
        M.graphWeight t
          (antidiagonalSubsetLabelledCoreAttachmentAssembly X).1 := by
      exact
        ((antidiagonalCoreAttachmentEquivFixedSurplusGraphs k ell).sum_comp
          (fun A : AttachmentFixedSurplusGraph k ell ↦
            M.graphWeight t A.1)).symm
    _ = ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        ∑ X : SubsetLabelledCoreAttachmentDatumAt
            k ell p.1.1 p.1.2,
          M.graphWeight t
            (subsetLabelledCoreAttachmentAssembly
              (mem_coreOffSizePairs.mp p.2) X) := by
      change
        (∑ X : (Σ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
            SubsetLabelledCoreAttachmentDatumAt k ell p.1.1 p.1.2),
          M.graphWeight t
            (antidiagonalSubsetLabelledCoreAttachmentAssembly X).1) = _
      rw [Fintype.sum_sigma]
      rfl
    _ = _ := by
      apply Fintype.sum_congr
      intro p
      exact sum_subsetLabelledCoreAttachmentDatumAt_graphWeight
        M t (mem_coreOffSizePairs.mp p.2)

/-- Exact global complex external-field reindexing through the deterministic
global core/attachment equivalence, with explicit binomial relabelling factor.
This is a sum of the project's genuine `complexFieldGraphWeight`, not an
abstract weight function. -/
theorem sum_fixedSurplusGraphs_complexFieldGraphWeight_eq_coreAttachment
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k ell : ℕ) :
    (∑ G ∈ fixedSurplusGraphs k ell,
        M.complexFieldGraphWeight g G) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℂ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∑ D : LabelledCoreForestAttachment p.1.1 p.1.2,
              finiteComplexGraphWeight M
                (FieldRootedTree.vertexFactor M g)
                (D.assembleGraph H.1) := by
  classical
  have hsub :
      (∑ G ∈ fixedSurplusGraphs k ell,
          M.complexFieldGraphWeight g G) =
        ∑ A : AttachmentFixedSurplusGraph k ell,
          M.complexFieldGraphWeight g A.1 := by
    exact Finset.sum_subtype (fixedSurplusGraphs k ell)
      (fun _ ↦ Iff.rfl) (fun G ↦ M.complexFieldGraphWeight g G)
  calc
    (∑ G ∈ fixedSurplusGraphs k ell,
        M.complexFieldGraphWeight g G) =
        ∑ A : AttachmentFixedSurplusGraph k ell,
          M.complexFieldGraphWeight g A.1 := hsub
    _ = ∑ X : AntidiagonalSubsetLabelledCoreAttachmentDatum k ell,
        M.complexFieldGraphWeight g
          (antidiagonalSubsetLabelledCoreAttachmentAssembly X).1 := by
      exact
        ((antidiagonalCoreAttachmentEquivFixedSurplusGraphs k ell).sum_comp
          (fun A : AttachmentFixedSurplusGraph k ell ↦
            M.complexFieldGraphWeight g A.1)).symm
    _ = ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        ∑ X : SubsetLabelledCoreAttachmentDatumAt
            k ell p.1.1 p.1.2,
          M.complexFieldGraphWeight g
            (subsetLabelledCoreAttachmentAssembly
              (mem_coreOffSizePairs.mp p.2) X) := by
      change
        (∑ X : (Σ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
            SubsetLabelledCoreAttachmentDatumAt k ell p.1.1 p.1.2),
          M.complexFieldGraphWeight g
            (antidiagonalSubsetLabelledCoreAttachmentAssembly X).1) = _
      rw [Fintype.sum_sigma]
      rfl
    _ = _ := by
      apply Fintype.sum_congr
      intro p
      exact
        sum_subsetLabelledCoreAttachmentDatumAt_complexFieldGraphWeight
          M g (mem_coreOffSizePairs.mp p.2)

/-- Genuine complex connected weight, globally reindexed by explicit
core/off-core size, original core labels, ordered core, and attachment data. -/
theorem complexFieldConnectedWeight_eq_coreAttachment
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k ell : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℂ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∑ D : LabelledCoreForestAttachment p.1.1 p.1.2,
              finiteComplexGraphWeight M
                (FieldRootedTree.vertexFactor M g)
                (D.assembleGraph H.1) := by
  rw [complexFieldConnectedWeight_eq_sum_fixedSurplusGraphs]
  exact sum_fixedSurplusGraphs_complexFieldGraphWeight_eq_coreAttachment
    M g k ell

/-- After the global complex-weight reindexing, the already proved fixed-core
attachment formula eliminates the remaining finite attachment sum. -/
theorem sum_fixedSurplusGraphs_complexFieldGraphWeight_eq_coreAttachmentCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k ell : ℕ) :
    (∑ G ∈ fixedSurplusGraphs k ell,
        M.complexFieldGraphWeight g G) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℂ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∫ roots : Fin p.1.1 → S,
              finiteComplexGraphIntegrand M
                  (FieldRootedTree.vertexFactor M g) H.1 roots *
                ((p.1.2.factorial : ℂ) * PowerSeries.coeff p.1.2
                  (PowerSeries.subst
                    (M.complexCoreBranchActionSeries g roots)
                    (PowerSeries.exp ℂ)))
              ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu) := by
  rw [sum_fixedSurplusGraphs_complexFieldGraphWeight_eq_coreAttachment]
  apply Fintype.sum_congr
  intro p
  apply congrArg (fun z : ℂ ↦ (Nat.choose k p.1.1 : ℂ) * z)
  apply Fintype.sum_congr
  intro H
  exact sum_finiteComplexGraphWeight_assembleGraph_eq_exp_coeff
    M g H.1 p.1.2

/-- Coefficient form of the genuine complex connected-weight identity. -/
theorem complexFieldConnectedWeight_eq_coreAttachmentCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k ell : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℂ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∫ roots : Fin p.1.1 → S,
              finiteComplexGraphIntegrand M
                  (FieldRootedTree.vertexFactor M g) H.1 roots *
                ((p.1.2.factorial : ℂ) * PowerSeries.coeff p.1.2
                  (PowerSeries.subst
                    (M.complexCoreBranchActionSeries g roots)
                    (PowerSeries.exp ℂ)))
              ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu) := by
  rw [complexFieldConnectedWeight_eq_sum_fixedSurplusGraphs]
  exact
    sum_fixedSurplusGraphs_complexFieldGraphWeight_eq_coreAttachmentCoeff
      M g k ell

/-- The analogous zero-field real formula, obtained at `t = 1` from the
real fixed-core attachment coefficient theorem. -/
theorem sum_fixedSurplusGraphs_graphWeight_one_eq_coreAttachmentCoeff
    (M : CompactBJRModel S) (k ell : ℕ) :
    (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight 1 G) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℝ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∫ roots : Fin p.1.1 → S,
              M.graphWeightIntegrand 1 H.1 roots *
                ((p.1.2.factorial : ℝ) * PowerSeries.coeff p.1.2
                  (PowerSeries.subst (M.coreBranchActionSeries roots)
                    (PowerSeries.exp ℝ)))
              ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu) := by
  rw [sum_fixedSurplusGraphs_graphWeight_eq_coreAttachment M 1]
  apply Fintype.sum_congr
  intro p
  apply congrArg (fun z : ℝ ↦ (Nat.choose k p.1.1 : ℝ) * z)
  apply Fintype.sum_congr
  intro H
  exact sum_finiteGraphWeight_assembleGraph_eq_exp_coeff M H.1 p.1.2

/-- Direct connected-weight corollary of the real global formula. -/
theorem connectedWeight_one_eq_coreAttachmentCoeff
    (M : CompactBJRModel S) (k ell : ℕ) :
    M.connectedWeight 1 k (ell + 1) =
      ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
        (Nat.choose k p.1.1 : ℝ) *
          ∑ H : {H : SimpleGraph (Fin p.1.1) //
              IsAdmissibleAttachmentCore p.1.1 ell H},
            ∫ roots : Fin p.1.1 → S,
              M.graphWeightIntegrand 1 H.1 roots *
                ((p.1.2.factorial : ℝ) * PowerSeries.coeff p.1.2
                  (PowerSeries.subst (M.coreBranchActionSeries roots)
                    (PowerSeries.exp ℝ)))
              ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu) := by
  rw [connectedWeight_eq_sum_fixedSurplusGraphs]
  exact sum_fixedSurplusGraphs_graphWeight_one_eq_coreAttachmentCoeff
    M k ell

end GraphCore
end PerronWright
