import PerronWright.Enumeration.FieldRootedTreeFinite

open MeasureTheory
open Topology
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

namespace FieldRootedTree

theorem numerator_eq_sum_rootBranchDecomposition
    (M : CompactBJRModel S) (g : C(S, ℂ)) (n : ℕ) :
    numerator M g n =
      ∑ D : LabelledRootBranchDecomposition n,
        vertexFactor M g *
      ∏ B : D.1.parts,
            M.kernel.complexAction M.mu (branchProfileMap M g (D.2 B)) := by
  classical
  calc
    numerator M g n =
        ∑ H : {G : SimpleGraph (Fin (n + 1)) // G.IsTree},
          fixedRootedGraphProfileMap M g H.1 0 := by
      unfold numerator
      exact sum_dite_eq_sum_subtype
        (p := fun H : SimpleGraph (Fin (n + 1)) ↦ H.IsTree)
        (f := fun H _ ↦ fixedRootedGraphProfileMap M g H 0)
    _ = _ := by
      refine Fintype.sum_equiv
        (labelledTreeEquivRootBranchDecomposition n) _ _ ?_
      intro H
      apply ContinuousMap.ext
      intro root
      rw [fixedTreeProfile_eq_rootBranchActions M g H.1 H.2 root]
      simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply]
      change
        vertexFactor M g root *
            ∏ B : (finRootlessPartition n H.1).parts,
              M.kernel.complexAction M.mu
                (relabelledRootBlockProfileMap M g H.1
                  (finRootlessBranchRoot H.1 H.2 B)) root =
          vertexFactor M g root *
            ∏ B : (finRootlessPartition n H.1).parts,
              M.kernel.complexAction M.mu
                (branchProfileMap M g
                  ((treeRootBranchDecomposition H.1 H.2).2 B)) root
      congr 1
      apply Fintype.prod_congr
      intro B
      rw [treeRootBranch_profileMap_eq M g H.1 H.2 B]

theorem branchProfileMap_equivFin
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {n : ℕ} {B : Finset (Fin n)} (T : LabelledRootBranch B) :
    branchProfileMap M g T =
      fixedRootedFinGraphProfileMap M g
        ((labelledRootBranchEquivFin B T).1.1)
        (labelledRootBranchEquivFin B T).2 := by
  rfl

theorem sum_branchProfileMap_eq_fin
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {n : ℕ} (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B, branchProfileMap M g T) =
      ∑ a : ({G : SimpleGraph (Fin B.card) // G.IsTree} × Fin B.card),
        fixedRootedFinGraphProfileMap M g a.1.1 a.2 := by
  exact Fintype.sum_equiv (labelledRootBranchEquivFin B) _ _
    (fun T ↦ branchProfileMap_equivFin M g T)

private theorem sum_tree_root_zero_eq_numerator
    (M : CompactBJRModel S) (g : C(S, ℂ)) (m : ℕ) :
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        fixedRootedGraphProfileMap M g H.1 0) = numerator M g m := by
  unfold numerator
  exact (sum_dite_eq_sum_subtype
    (p := fun H : SimpleGraph (Fin (m + 1)) ↦ H.IsTree)
    (f := fun H _ ↦ fixedRootedGraphProfileMap M g H 0)).symm

/-- Summing all rooted trees on a finite block gives the factorial-normalised
actual field coefficient. -/
theorem sum_branchProfileMap_eq_factorial_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B, branchProfileMap M g T) =
      (B.card.factorial : C(S, ℂ)) *
        PowerSeries.coeff B.card (series M g) := by
  rw [sum_branchProfileMap_eq_fin M g B]
  cases hcard : B.card with
  | zero =>
      simp [series_coeff_zero]
  | succ m =>
      rw [Fintype.sum_prod_type_right]
      have hroot (v : Fin (m + 1)) :
          (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
              fixedRootedGraphProfileMap M g H.1 v) =
            ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
              fixedRootedGraphProfileMap M g H.1 0 :=
        sum_tree_fixedRootedGraphProfileMap_eq_root_zero M g v
      calc
        _ = ∑ v : Fin (m + 1),
              ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
                fixedRootedGraphProfileMap M g H.1 v := by rfl
        _ = (m + 1) •
              (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
                fixedRootedGraphProfileMap M g H.1 0) := by
              simp_rw [hroot]
              simp
        _ = ((m + 1).factorial : C(S, ℂ)) *
              PowerSeries.coeff (m + 1) (series M g) := by
              rw [series_coeff_succ, sum_tree_root_zero_eq_numerator]
              unfold coefficient
              rw [Nat.factorial_succ]
              ext root
              simp only [nsmul_eq_mul, ContinuousMap.mul_apply,
                ContinuousMap.natCast_apply, ContinuousMap.smul_apply,
                smul_eq_mul]
              push_cast
              have hfac : (m.factorial : ℂ) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero m
              field_simp

/-- Applying the genuine kernel action to the full branch sum produces the
factorial-normalised coefficient of the coefficientwise action series. -/
theorem sum_branch_kernelAction_eq_factorial_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {n : ℕ} (B : Finset (Fin n)) :
    (∑ T : LabelledRootBranch B,
        M.kernel.complexActionCLM M.mu (branchProfileMap M g T)) =
      (B.card.factorial : C(S, ℂ)) *
        PowerSeries.coeff B.card
          (M.complexKernelActionPowerSeries (series M g)) := by
  let L := M.kernel.complexActionCLM M.mu
  have hprofiles := sum_branchProfileMap_eq_factorial_coeff M g B
  have hmap := congrArg L hprofiles
  simp only [map_sum] at hmap
  calc
    _ = L ((B.card.factorial : C(S, ℂ)) *
          PowerSeries.coeff B.card (series M g)) := hmap
    _ = L ((B.card.factorial : ℂ) •
          PowerSeries.coeff B.card (series M g)) := by congr 1
    _ = (B.card.factorial : ℂ) •
          L (PowerSeries.coeff B.card (series M g)) := by
      exact map_smul L _ _
    _ = (B.card.factorial : C(S, ℂ)) *
          PowerSeries.coeff B.card
            (M.complexKernelActionPowerSeries (series M g)) := by
      ext root
      simp only [ContinuousMap.smul_apply, smul_eq_mul,
        ContinuousMap.mul_apply, ContinuousMap.natCast_apply,
        CompactBJRModel.complexKernelActionPowerSeries_coeff]
      rfl

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem labelledPartitionWeight_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : ℕ → C(S, ℂ)) (s : Finset α) (root : S) :
    labelledPartitionWeight w s root =
      ∑ P : Finpartition s, ∏ B : P.parts, w B.1.card root := by
  unfold labelledPartitionWeight
  rw [continuousMap_finset_sum_apply]
  apply Fintype.sum_congr
  intro P
  rw [continuousMap_finset_prod_apply]
  exact (Finset.prod_coe_sort P.parts
    (fun B ↦ w B.card root)).symm

/-- The complete genuine field numerator is the field vertex factor times
the labelled partition exponential of the genuine branch coefficients. -/
theorem numerator_eq_vertexFactor_mul_labelledPartitionWeight
    (M : CompactBJRModel S) (g : C(S, ℂ)) (n : ℕ) :
    numerator M g n =
      vertexFactor M g *
        labelledPartitionWeight
          (fun k ↦ (k.factorial : C(S, ℂ)) *
            PowerSeries.coeff k
              (M.complexKernelActionPowerSeries (series M g)))
          (Finset.univ : Finset (Fin n)) := by
  rw [numerator_eq_sum_rootBranchDecomposition M g n]
  unfold LabelledRootBranchDecomposition
  rw [Fintype.sum_sigma]
  apply ContinuousMap.ext
  intro root
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.prod_apply]
  rw [labelledPartitionWeight_apply]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro P
  rw [← Finset.mul_sum]
  congr 1
  change
    (∑ i : (B : P.parts) → LabelledRootBranch B.1,
      ∏ B : P.parts,
        M.kernel.complexAction M.mu (branchProfileMap M g (i B)) root) = _
  calc
    _ = ∏ B : P.parts,
        ∑ T : LabelledRootBranch B.1,
          M.kernel.complexAction M.mu (branchProfileMap M g T) root := by
      exact (Fintype.prod_sum (fun B T ↦
        M.kernel.complexAction M.mu (branchProfileMap M g T) root)).symm
    _ = _ := by
      apply Fintype.prod_congr
      intro B
      have h := sum_branch_kernelAction_eq_factorial_coeff M g B.1
      simpa only [ContinuousMap.sum_apply,
        ContinuousKernel.complexActionCLM_apply] using
        congrArg (fun f : C(S, ℂ) ↦ f root) h

private theorem kernelAction_series_constantCoeff_zero
    (M : CompactBJRModel S) (g : C(S, ℂ)) :
    PowerSeries.constantCoeff
      (M.complexKernelActionPowerSeries (series M g)) = 0 := by
  rw [M.complexKernelActionPowerSeries_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [series_coeff_zero]
  exact (M.kernel.complexActionCLM M.mu).map_zero

/-- Coefficient comparison between the finite labelled-tree sum and the
field-dependent formal tree equation. -/
theorem numerator_eq_factorial_mul_formalRHS_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (n : ℕ) :
    numerator M g n =
      (n.factorial : C(S, ℂ)) *
        PowerSeries.coeff (n + 1) (formalRHS M g (series M g)) := by
  rw [numerator_eq_vertexFactor_mul_labelledPartitionWeight M g n]
  have hpart := labelledPartitionWeight_eq_factorial_mul_subst_exp_coeff
    (M.complexKernelActionPowerSeries (series M g))
    (kernelAction_series_constantCoeff_zero M g)
    (Finset.univ : Finset (Fin n))
  rw [hpart]
  rw [formalRHS, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_C_mul]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- The actual finite labelled-tree series satisfies the complete
field-dependent formal equation coefficient by coefficient. -/
theorem series_eq_formalRHS (M : CompactBJRModel S) (g : C(S, ℂ)) :
    series M g = formalRHS M g (series M g) := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => rw [series_coeff_zero, formalRHS_coeff_zero]
  | succ n =>
      rw [series_coeff_succ]
      unfold coefficient
      rw [numerator_eq_factorial_mul_formalRHS_coeff M g n]
      have hfac : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      ext root
      simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        ContinuousMap.natCast_apply, smul_eq_mul]
      field_simp

/-- The genuine field series is the unique zero-constant formal solution. -/
theorem formalRHS_fixedPoint_unique
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (F : PowerSeries C(S, ℂ))
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : F = formalRHS M g F) :
    F = series M g := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          calc
            PowerSeries.coeff 0 F = 0 := by
              simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
            _ = PowerSeries.coeff 0 (series M g) := by
              simpa only using (series_coeff_zero M g).symm
      | succ m =>
          let AF := M.complexKernelActionPowerSeries F
          let AT := M.complexKernelActionPowerSeries (series M g)
          have hAF0 : PowerSeries.constantCoeff AF = 0 := by
            dsimp only [AF]
            rw [M.complexKernelActionPowerSeries_constantCoeff, hF0, map_zero]
          have hAT0 : PowerSeries.constantCoeff AT = 0 := by
            exact kernelAction_series_constantCoeff_zero M g
          have hAcoeff : ∀ k ≤ m,
              PowerSeries.coeff k AF = PowerSeries.coeff k AT := by
            intro k hk
            dsimp only [AF, AT]
            simp only [M.complexKernelActionPowerSeries_coeff]
            rw [ih k (by omega)]
          have hExp := powerSeries_subst_exp_coeff_eq_of_coeff_eq_up_to
            AF AT hAF0 hAT0 m hAcoeff
          have hFn := congrArg (PowerSeries.coeff (m + 1)) hF
          have hTn := congrArg (PowerSeries.coeff (m + 1))
            (series_eq_formalRHS M g)
          rw [formalRHS, PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul] at hFn hTn
          calc
            PowerSeries.coeff (m + 1) F =
                vertexFactor M g * PowerSeries.coeff m
                  (PowerSeries.subst AF (PowerSeries.exp C(S, ℂ))) := by
              simpa only [AF] using hFn
            _ = vertexFactor M g * PowerSeries.coeff m
                  (PowerSeries.subst AT (PowerSeries.exp C(S, ℂ))) := by
              rw [hExp]
            _ = PowerSeries.coeff (m + 1) (series M g) := by
              simpa only [AT] using hTn.symm

end FieldRootedTree

end PerronWright

