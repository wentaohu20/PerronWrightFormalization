import PerronWright.Enumeration.RootedTreeFormalIdentity

/-!
# Labelled rooted forests attached to an ordered finite core

This is the first finite combinatorial layer needed after leaf pruning.
For a fixed ordered list of core types, every off-core rooted tree is a
labelled block, and the block is coloured by the core vertex to which its
root edge is incident.  The sum over the actual rooted tree carried by a
block is already supplied by `sum_labelledRootBranch_profileMap_eq_factorial_coeff`.
The sum over coloured blocks is therefore an ordinary labelled exponential.

No graph-to-core classification is asserted in this file.  That separate
equivalence is the next combinatorial layer.
-/

open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A finite labelled forest attached to an ordered `q`-vertex core.
The off-core labels are partitioned into nonempty blocks; every block chooses
one core vertex and carries one rooted labelled tree. -/
def LabelledCoreForestAttachment (q n : ℕ) :=
  Σ P : Finpartition (Finset.univ : Finset (Fin n)),
    (B : P.parts) → Fin q × LabelledRootBranch B.1

noncomputable instance labelledCoreForestAttachmentFintype (q n : ℕ) :
    Fintype (LabelledCoreForestAttachment q n) := by
  unfold LabelledCoreForestAttachment
  infer_instance

/-- Pure finite distributivity for coloured rooted-tree blocks.  Keeping this
lemma independent of the graph weight makes the same combinatorial bijection
available for the later complex-field coefficients. -/
theorem sum_labelledCoreForestAttachment_product
    {R : Type*} [CommSemiring R] {q n : ℕ}
    (w : (B : Finset (Fin n)) → Fin q → LabelledRootBranch B → R) :
    (∑ D : LabelledCoreForestAttachment q n,
        ∏ B : D.1.parts, w B.1 (D.2 B).1 (D.2 B).2) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        ∏ B : P.parts,
          ∑ z : Fin q × LabelledRootBranch B.1, w B.1 z.1 z.2 := by
  classical
  unfold LabelledCoreForestAttachment
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro P
  exact (Fintype.prod_sum
    (fun (B : P.parts) (z : Fin q × LabelledRootBranch B.1) ↦
      w B.1 z.1 z.2)).symm

/-- Literal weight of one coloured rooted-forest attachment after fixing the
types of the ordered core vertices.  The core vertex factors and core edge
factors are deliberately not included here. -/
def CompactBJRModel.labelledCoreForestAttachmentWeight
    (M : CompactBJRModel S) {q n : ℕ} (roots : Fin q → S)
    (D : LabelledCoreForestAttachment q n) : ℝ :=
  ∏ B : D.1.parts,
    M.kernel.action M.mu
      (LabelledRootBranch.profileMap M (D.2 B).2)
      (roots (D.2 B).1)

/-- Sum the genuine rooted tree carried by one fixed label block, and then
apply the root edge to a fixed core type. -/
theorem CompactBJRModel.sum_labelledRootBranch_kernelAction_eq_factorial_coeff
    (M : CompactBJRModel S) {n : ℕ} (B : Finset (Fin n)) (root : S) :
    (∑ T : LabelledRootBranch B,
        M.kernel.action M.mu (LabelledRootBranch.profileMap M T) root) =
      (B.card.factorial : ℝ) *
        PowerSeries.coeff B.card
          (M.kernelActionPowerSeries M.typeRootedTreeEGF) root := by
  simpa only [ContinuousMap.mul_apply, ContinuousMap.natCast_apply] using
    M.sum_labelledRootBranch_kernelAction_eq B root

/-- The formal series of all possible rooted-tree branches incident to one
of the fixed ordered core types.  Its coefficient is the sum over the choice
of the incident core vertex. -/
def CompactBJRModel.coreBranchActionSeries
    (M : CompactBJRModel S) {q : ℕ} (roots : Fin q → S) : PowerSeries ℝ :=
  PowerSeries.mk fun k ↦
    ∑ i : Fin q,
      PowerSeries.coeff k
        (M.kernelActionPowerSeries M.typeRootedTreeEGF) (roots i)

@[simp] theorem CompactBJRModel.coreBranchActionSeries_coeff
    (M : CompactBJRModel S) {q : ℕ} (roots : Fin q → S) (k : ℕ) :
    PowerSeries.coeff k (M.coreBranchActionSeries roots) =
      ∑ i : Fin q,
        PowerSeries.coeff k
          (M.kernelActionPowerSeries M.typeRootedTreeEGF) (roots i) := by
  simp only [CompactBJRModel.coreBranchActionSeries, PowerSeries.coeff_mk]

theorem CompactBJRModel.coreBranchActionSeries_constantCoeff
    (M : CompactBJRModel S) {q : ℕ} (roots : Fin q → S) :
    PowerSeries.constantCoeff (M.coreBranchActionSeries roots) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [M.coreBranchActionSeries_coeff]
  have hzero := M.kernelAction_typeRootedTreeEGF_constantCoeff
  rw [← PowerSeries.coeff_zero_eq_constantCoeff] at hzero
  simp only [hzero, ContinuousMap.zero_apply, Finset.sum_const_zero]

/-- Exact finite regrouping of all coloured rooted-tree blocks into the
ordinary labelled partition weight of the aggregate branch series. -/
theorem CompactBJRModel.sum_labelledCoreForestAttachmentWeight_eq_partition
    (M : CompactBJRModel S) {q : ℕ} (roots : Fin q → S) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        M.labelledCoreForestAttachmentWeight roots D) =
      labelledPartitionWeight
        (fun k ↦ (k.factorial : ℝ) *
          PowerSeries.coeff k (M.coreBranchActionSeries roots))
        (Finset.univ : Finset (Fin n)) := by
  classical
  unfold CompactBJRModel.labelledCoreForestAttachmentWeight
  rw [sum_labelledCoreForestAttachment_product
    (w := fun B i T ↦
      M.kernel.action M.mu (LabelledRootBranch.profileMap M T) (roots i))]
  unfold labelledPartitionWeight
  apply Fintype.sum_congr
  intro P
  rw [← Finset.prod_coe_sort P.parts
    (fun B ↦ (B.card.factorial : ℝ) *
      PowerSeries.coeff B.card (M.coreBranchActionSeries roots))]
  apply Fintype.prod_congr
  intro B
  rw [Fintype.sum_prod_type]
  simp_rw [M.sum_labelledRootBranch_kernelAction_eq_factorial_coeff B.1]
  rw [← Finset.mul_sum]
  exact congrArg ((B.1.card.factorial : ℝ) * ·)
    (M.coreBranchActionSeries_coeff roots B.1.card).symm

/-- The exact exponential formula for all labelled rooted forests attached
to a fixed ordered core.  This theorem is finite in every coefficient and
uses the actual compact-type rooted-tree coefficients. -/
theorem CompactBJRModel.sum_labelledCoreForestAttachmentWeight_eq_exp_coeff
    (M : CompactBJRModel S) {q : ℕ} (roots : Fin q → S) (n : ℕ) :
    (∑ D : LabelledCoreForestAttachment q n,
        M.labelledCoreForestAttachmentWeight roots D) =
      (n.factorial : ℝ) * PowerSeries.coeff n
        (PowerSeries.subst (M.coreBranchActionSeries roots)
          (PowerSeries.exp ℝ)) := by
  rw [M.sum_labelledCoreForestAttachmentWeight_eq_partition roots n]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    labelledPartitionWeight_eq_factorial_mul_subst_exp_coeff
      (M.coreBranchActionSeries roots)
      (M.coreBranchActionSeries_constantCoeff roots)
      (Finset.univ : Finset (Fin n))

end PerronWright
