import PerronWright.Enumeration.TreeRootBranchDecomposition
import PerronWright.Enumeration.RootedProfileRelabel
import PerronWright.Enumeration.LabelledPartitionExp

/-!
# Summing independently rooted branch trees

This file is the finite bridge from the actual root-branch decomposition to
the factorial-normalized coefficient of the genuine type-resolved rooted-tree
series.  No recurrence is assumed.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Relabelling a rooted tree on an arbitrary finite block by `Fin |B|`
gives a labelled tree together with the image of its distinguished root. -/
noncomputable def labelledRootBranchEquivFin
    {n : ℕ} (B : Finset (Fin n)) :
    LabelledRootBranch B ≃
      ({G : SimpleGraph (Fin B.card) // G.IsTree} × Fin B.card) where
  toFun T :=
    (⟨B.equivFin.simpleGraph T.graph, by
      exact (SimpleGraph.Iso.comap B.equivFin.symm T.graph).isTree_iff.mpr
        T.isTree⟩,
      B.equivFin T.root)
  invFun q :=
    { graph := B.equivFin.simpleGraph.symm q.1.1
      isTree := by
        exact (SimpleGraph.Iso.comap B.equivFin q.1.1).isTree_iff.mpr q.1.2
      root := B.equivFin.symm q.2 }
  left_inv T := by
    apply LabelledRootBranch.ext
    · exact B.equivFin.simpleGraph.symm_apply_apply T.graph
    · exact B.equivFin.symm_apply_apply T.root
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      exact B.equivFin.simpleGraph.apply_symm_apply q.1.1
    · exact B.equivFin.apply_symm_apply q.2

noncomputable instance labelledRootBranchFintype
    {n : ℕ} (B : Finset (Fin n)) : Fintype (LabelledRootBranch B) :=
  Fintype.ofEquiv
    ({G : SimpleGraph (Fin B.card) // G.IsTree} × Fin B.card)
    (labelledRootBranchEquivFin B).symm

/-- The branch profile is exactly the fixed-root profile after canonical
relabeling by `Fin |B|`. -/
theorem CompactBJRModel.labelledRootBranch_profileMap_equivFin
    (M : CompactBJRModel S) {n : ℕ} {B : Finset (Fin n)}
    (T : LabelledRootBranch B) :
    LabelledRootBranch.profileMap M T =
      M.fixedRootedFinGraphProfileMap
        ((labelledRootBranchEquivFin B T).1.1)
        (labelledRootBranchEquivFin B T).2 := by
  rfl

/-- Reindex the actual finite sum over rooted branch trees by a tree on
`Fin |B|` and its distinguished root label. -/
theorem CompactBJRModel.sum_labelledRootBranch_profileMap_eq_fin
    (M : CompactBJRModel S) {n : ℕ} (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B, LabelledRootBranch.profileMap M T) =
      ∑ q : ({G : SimpleGraph (Fin B.card) // G.IsTree} × Fin B.card),
        M.fixedRootedFinGraphProfileMap q.1.1 q.2 := by
  exact Fintype.sum_equiv (labelledRootBranchEquivFin B) _ _
    (fun T => M.labelledRootBranch_profileMap_equivFin T)

/-- A finite dependent sum with a proof-dependent summand can be restricted
from the ambient finite type to the corresponding subtype. -/
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

/-- Evaluation of a finite sum of continuous maps is pointwise.  We keep
this local rather than relying on coercion simplification through the
`Fintype` sum notation. -/
private theorem continuousMap_finset_sum_apply
    {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → C(X, ℝ)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ContinuousMap.add_apply, ih]

/-- The sum of fixed-root profiles over all labelled trees is the numerator
appearing in the genuine rooted-tree coefficient, hence is `m!` times that
coefficient. -/
theorem CompactBJRModel.sum_tree_fixedRootedGraphProfileMap_eq_factorial_coeff
  (M : CompactBJRModel S) (m : ℕ) :
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfileMap H.1 0) =
      (m.factorial : C(S, ℝ)) * M.rootedTreeCoefficientMap m := by
  ext root
  rw [continuousMap_finset_sum_apply (s := Finset.univ)
    (f := fun H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree} =>
      M.fixedRootedGraphProfileMap H.1 0)]
  simp only [
    CompactBJRModel.fixedRootedGraphProfileMap_apply,
    ContinuousMap.mul_apply,
    ContinuousMap.natCast_apply,
    CompactBJRModel.rootedTreeCoefficientMap_apply]
  change
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
      M.fixedRootedGraphProfile H.1 0 root) =
      (m.factorial : ℝ) * M.rootedTreeCoefficient m root
  have hsum := sum_dite_eq_sum_subtype
    (R := ℝ) (p := fun H : SimpleGraph (Fin (m + 1)) => H.IsTree)
    (fun H _ => ∫ z : Fin m → S,
      M.fieldGraphWeightIntegrand 0 H (Fin.insertNth 0 root z)
        ∂Measure.pi (fun _ : Fin m => M.mu))
  have htrees :
      (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        M.fixedRootedGraphProfile H.1 0 root) =
        M.rootedTreeNumerator m root := by
    unfold CompactBJRModel.rootedTreeNumerator
    calc
      (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
          M.fixedRootedGraphProfile H.1 0 root) =
          ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
            ∫ z : Fin m → S,
              M.fieldGraphWeightIntegrand 0 H.1 (Fin.insertNth 0 root z)
                ∂Measure.pi (fun _ : Fin m => M.mu) := by
        rfl
      _ = ∑ H : SimpleGraph (Fin (m + 1)),
            if H.IsTree then
              ∫ z : Fin m → S,
                M.fieldGraphWeightIntegrand 0 H (Fin.insertNth 0 root z)
                  ∂Measure.pi (fun _ : Fin m => M.mu)
            else 0 := hsum.symm
  rw [htrees, CompactBJRModel.rootedTreeCoefficient]
  have hfac : (m.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- Summing every independently rooted tree on a block gives the exact
factorial-normalized coefficient of the genuine rooted-tree series. -/
theorem CompactBJRModel.sum_labelledRootBranch_profileMap_eq_factorial_coeff
    (M : CompactBJRModel S) {n : ℕ} (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B, LabelledRootBranch.profileMap M T) =
      (B.card.factorial : C(S, ℝ)) *
        PowerSeries.coeff B.card M.typeRootedTreeEGF := by
  rw [M.sum_labelledRootBranch_profileMap_eq_fin B]
  cases hcard : B.card with
  | zero =>
      simp [M.typeRootedTreeEGF_coeff_zero]
  | succ m =>
      rw [Fintype.sum_prod_type_right]
      calc
        (∑ v : Fin (m + 1),
            ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
              M.fixedRootedFinGraphProfileMap H.1 v) =
            ∑ v : Fin (m + 1),
              ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
                M.fixedRootedGraphProfileMap H.1 0 := by
          apply Fintype.sum_congr
          intro v
          exact M.sum_tree_fixedRootedGraphProfileMap_eq_root_zero v
        _ = (m + 1) •
              (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
                M.fixedRootedGraphProfileMap H.1 0) := by
          simp
        _ = ((m + 1).factorial : C(S, ℝ)) *
              PowerSeries.coeff (m + 1) M.typeRootedTreeEGF := by
          rw [M.sum_tree_fixedRootedGraphProfileMap_eq_factorial_coeff m,
            M.typeRootedTreeEGF_coeff_succ, Nat.factorial_succ]
          ext root
          simp [nsmul_eq_mul, mul_assoc]

end PerronWright
