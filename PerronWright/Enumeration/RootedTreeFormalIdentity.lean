import PerronWright.Enumeration.LabelledRootBranchSum

/-!
# The actual rooted-tree formal identity

The proved block-profile layer lives in
`PerronWright.Enumeration.LabelledRootBranchSum`.  This scratch file now
contains only the remaining action, global reindexing, and coefficientwise
formal-equation layers.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem continuousMap_finset_sum_apply
    {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → C(X, ℝ)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ContinuousMap.add_apply, ih]

private theorem continuousMap_finset_prod_apply
    {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → C(X, ℝ)) (x : X) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, ContinuousMap.mul_apply, ih]

private theorem sum_dite_eq_sum_subtype
    {α R : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid R]
    (p : α → Prop) [DecidablePred p] (f : ∀ a, p a → R) :
    (∑ a : α, if h : p a then f a h else 0) =
      ∑ a : {a // p a}, f a.1 a.2 := by
  classical
  let F : α → R := fun a => if h : p a then f a h else 0
  calc
    (∑ a : α, if h : p a then f a h else 0) = ∑ a : α, F a := rfl
    _ = ∑ a ∈ (Finset.univ.filter p), F a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p a <;> simp [F, ha]
    _ = ∑ a : {a // p a}, F a.1 := by
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) F
    _ = ∑ a : {a // p a}, f a.1 a.2 := by
      apply Fintype.sum_congr
      intro a
      simp [F, a.2]

/-- Pointwise evaluation of the continuous-map-valued labelled partition
weight, written with its blocks as a finite subtype. -/
private theorem labelledPartitionWeight_apply
    {X α : Type*} [TopologicalSpace X]
    [Fintype α] [DecidableEq α]
    (w : ℕ → C(X, ℝ)) (s : Finset α) (root : X) :
    labelledPartitionWeight w s root =
      ∑ P : Finpartition s, ∏ B : P.parts, w B.1.card root := by
  unfold labelledPartitionWeight
  rw [continuousMap_finset_sum_apply (s := Finset.univ)
    (f := fun P : Finpartition s => ∏ B ∈ P.parts, w B.card)]
  apply Fintype.sum_congr
  intro P
  rw [continuousMap_finset_prod_apply (s := P.parts)
    (f := fun B => w B.card)]
  exact (Finset.prod_coe_sort P.parts
    (fun B => w B.card root)).symm

/-- The decomposition carries its canonical finite Sigma/Pi structure. -/
noncomputable instance labelledRootBranchDecompositionFintype (n : ℕ) :
    Fintype (LabelledRootBranchDecomposition n) := by
  unfold LabelledRootBranchDecomposition
  infer_instance

/-- Applying the kernel action to the exact block-profile sum produces the
factorial-normalized coefficient of the coefficientwise kernel-action
series. -/
theorem CompactBJRModel.sum_labelledRootBranch_kernelActionMap_eq
    (M : CompactBJRModel S) {n : ℕ} (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B,
        M.kernel.actionCLM M.mu (LabelledRootBranch.profileMap M T)) =
      (B.card.factorial : C(S, ℝ)) *
        PowerSeries.coeff B.card
          (M.kernelActionPowerSeries M.typeRootedTreeEGF) := by
  let L := M.kernel.actionCLM M.mu
  have hprofiles :=
    M.sum_labelledRootBranch_profileMap_eq_factorial_coeff B
  have hmap := congrArg L hprofiles
  simp only [map_sum] at hmap
  calc
    (∑ T : LabelledRootBranch B,
        M.kernel.actionCLM M.mu (LabelledRootBranch.profileMap M T)) =
        L ((B.card.factorial : C(S, ℝ)) *
          PowerSeries.coeff B.card M.typeRootedTreeEGF) := hmap
    _ = L ((B.card.factorial : ℝ) •
          PowerSeries.coeff B.card M.typeRootedTreeEGF) := by
      congr 1
    _ = (B.card.factorial : ℝ) •
          L (PowerSeries.coeff B.card M.typeRootedTreeEGF) := by
      exact map_smul L _ _
    _ = (B.card.factorial : C(S, ℝ)) *
          M.kernel.actionCLM M.mu
            (PowerSeries.coeff B.card M.typeRootedTreeEGF) := by
      ext x
      rfl
    _ = (B.card.factorial : C(S, ℝ)) *
          PowerSeries.coeff B.card
            (M.kernelActionPowerSeries M.typeRootedTreeEGF) := by
      rw [M.kernelActionPowerSeries_coeff]

/-- Pointwise form of the preceding exact block-action identity. -/
theorem CompactBJRModel.sum_labelledRootBranch_kernelAction_eq
    (M : CompactBJRModel S) {n : ℕ} (B : Finset (Fin n)) (root : S) :
    (∑ T : LabelledRootBranch B,
        M.kernel.action M.mu (LabelledRootBranch.profileMap M T) root) =
      ((B.card.factorial : C(S, ℝ)) *
        PowerSeries.coeff B.card
          (M.kernelActionPowerSeries M.typeRootedTreeEGF)) root := by
  calc
    (∑ T : LabelledRootBranch B,
        M.kernel.action M.mu (LabelledRootBranch.profileMap M T) root) =
        (∑ T : LabelledRootBranch B,
          M.kernel.actionCLM M.mu
            (LabelledRootBranch.profileMap M T)) root := by
      rw [continuousMap_finset_sum_apply (s := Finset.univ)
        (f := fun T : LabelledRootBranch B =>
          M.kernel.actionCLM M.mu (LabelledRootBranch.profileMap M T))]
      simp only [ContinuousKernel.actionCLM_apply]
    _ = ((B.card.factorial : C(S, ℝ)) *
          PowerSeries.coeff B.card
            (M.kernelActionPowerSeries M.typeRootedTreeEGF)) root := by
      rw [M.sum_labelledRootBranch_kernelActionMap_eq B]

/-- Reindex the full labelled-tree numerator by an actual partition of the
non-root labels and an independently rooted tree on every block. -/
theorem CompactBJRModel.rootedTreeNumerator_eq_sum_rootBranchDecomposition
    (M : CompactBJRModel S) (n : ℕ) (root : S) :
    M.rootedTreeNumerator n root =
      ∑ D : LabelledRootBranchDecomposition n,
        M.zeroTreeVertexFactor root *
          ∏ B : D.1.parts,
            M.kernel.action M.mu
              (LabelledRootBranch.profileMap M (D.2 B)) root := by
  rw [M.rootedTreeNumerator_eq_sum_rootBranch_kernelActions]
  rw [sum_dite_eq_sum_subtype
    (p := fun H : SimpleGraph (Fin (n + 1)) => H.IsTree)
    (f := fun H hT =>
      M.zeroTreeVertexFactor root *
        ∏ B : (finRootlessPartition n H).parts,
          M.kernel.action M.mu
            (M.relabelledRootBlockTreeProfileMap H
              (finRootlessBranchRoot H hT B)) root)]
  refine Fintype.sum_equiv
    (labelledTreeEquivRootBranchDecomposition n) _ _ ?_
  intro H
  change
    M.zeroTreeVertexFactor root *
        ∏ B : (finRootlessPartition n H.1).parts,
          M.kernel.action M.mu
            (M.relabelledRootBlockTreeProfileMap H.1
              (finRootlessBranchRoot H.1 H.2 B)) root =
      M.zeroTreeVertexFactor root *
        ∏ B : (finRootlessPartition n H.1).parts,
          M.kernel.action M.mu
            (LabelledRootBranch.profileMap M
              ((treeRootBranchDecomposition H.1 H.2).2 B)) root
  congr 1
  apply Fintype.prod_congr
  intro B
  rw [M.treeRootBranch_profileMap_eq H.1 H.2 B]

/-- The complete actual labelled-tree numerator is the root-vertex factor
times the labelled partition weight of the genuine block-action
coefficients. -/
theorem CompactBJRModel.rootedTreeNumerator_eq_zeroTreeVertexFactor_mul_labelledPartitionWeight
    (M : CompactBJRModel S) (n : ℕ) (root : S) :
    M.rootedTreeNumerator n root =
      M.zeroTreeVertexFactor root *
        labelledPartitionWeight
          (fun k => (k.factorial : C(S, ℝ)) *
            PowerSeries.coeff k
              (M.kernelActionPowerSeries M.typeRootedTreeEGF))
          (Finset.univ : Finset (Fin n)) root := by
  rw [M.rootedTreeNumerator_eq_sum_rootBranchDecomposition n root]
  unfold LabelledRootBranchDecomposition
  rw [Fintype.sum_sigma]
  rw [labelledPartitionWeight_apply]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro P
  rw [← Finset.mul_sum]
  congr 1
  change
    (∑ i : (B : P.parts) → LabelledRootBranch B.1,
      ∏ B : P.parts,
        M.kernel.action M.mu
          (LabelledRootBranch.profileMap M (i B)) root) = _
  calc
    (∑ i : (B : P.parts) → LabelledRootBranch B.1,
        ∏ B : P.parts,
          M.kernel.action M.mu
            (LabelledRootBranch.profileMap M (i B)) root) =
        ∏ B : P.parts,
          ∑ T : LabelledRootBranch B.1,
            M.kernel.action M.mu
              (LabelledRootBranch.profileMap M T) root := by
      exact (Fintype.prod_sum (fun B T =>
        M.kernel.action M.mu
          (LabelledRootBranch.profileMap M T) root)).symm
    _ = _ := by
      apply Fintype.prod_congr
      intro B
      exact M.sum_labelledRootBranch_kernelAction_eq B.1 root

/-- Exact coefficient comparison between the actual labelled-tree
numerator and the formal rooted-tree right-hand side. -/
theorem CompactBJRModel.rootedTreeNumerator_eq_factorial_mul_formalRHS_coeff
    (M : CompactBJRModel S) (n : ℕ) (root : S) :
    M.rootedTreeNumerator n root =
      (n.factorial : ℝ) *
        PowerSeries.coeff (n + 1)
          (M.rootedTreeFormalRHS M.typeRootedTreeEGF) root := by
  rw [M.rootedTreeNumerator_eq_zeroTreeVertexFactor_mul_labelledPartitionWeight
    n root]
  exact M.zeroTreeVertexFactor_mul_labelledPartitionWeight_eq n root

/-- The genuinely enumerated type-resolved rooted-tree series satisfies
the complete compact-BJR formal rooted-tree equation, coefficient by
coefficient and with no assumed recurrence. -/
theorem CompactBJRModel.typeRootedTreeEGF_eq_rootedTreeFormalRHS
    (M : CompactBJRModel S) :
    M.typeRootedTreeEGF = M.rootedTreeFormalRHS M.typeRootedTreeEGF := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      rw [M.typeRootedTreeEGF_coeff_zero,
        M.rootedTreeFormalRHS_coeff_zero]
  | succ n =>
      rw [M.typeRootedTreeEGF_coeff_succ]
      ext root
      rw [M.rootedTreeCoefficientMap_apply]
      unfold CompactBJRModel.rootedTreeCoefficient
      rw [M.rootedTreeNumerator_eq_factorial_mul_formalRHS_coeff n root]
      have hfac : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp

end PerronWright
