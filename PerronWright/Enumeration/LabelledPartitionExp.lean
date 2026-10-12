import PerronWright.Enumeration.TreeFormalEquation
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Labelled partitions and the formal exponential

A partition of a finite labelled set can be split at the block containing a
distinguished label. This gives an exact recurrence for weighted labelled
partitions. The derivative of a substituted formal exponential gives its
coefficientwise algebraic counterpart.
-/

open scoped Classical
noncomputable section

namespace PerronWright

private theorem finpartition_heq_copy
    {α : Type*} [Lattice α] [OrderBot α]
    {s t : α} (P : Finpartition s) (h : s = t) :
    HEq P (P.copy h) := by
  subst t
  apply heq_of_eq
  apply Finpartition.ext
  rfl

theorem finpartition_parts_avoid_part
    {α : Type*} [DecidableEq α] {s B : Finset α}
    (P : Finpartition s) (hB : B ∈ P.parts) :
    (P.avoid B).parts = P.parts.erase B := by
  ext C
  rw [P.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨D, hD, hDnot, rfl⟩
    have hDB : D ≠ B := fun h => hDnot (h ▸ le_rfl)
    have hdis : Disjoint D B := P.disjoint hD hB hDB
    rw [Finset.sdiff_eq_self_of_disjoint hdis]
    exact ⟨hDB, hD⟩
  · rintro ⟨hCB, hC⟩
    have hdis : Disjoint C B := P.disjoint hC hB hCB
    have hnot : ¬C ⊆ B := by
      intro hsub
      obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hC
      exact (Finset.disjoint_left.mp hdis) ha (hsub ha)
    exact ⟨C, hC, hnot, Finset.sdiff_eq_self_of_disjoint hdis⟩

/-- A partition of `s` is exactly a choice of its block containing `a` and a
partition of the complementary labels. -/
noncomputable def finpartitionMarkedBlockEquiv
    {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (ha : a ∈ s) :
    Finpartition s ≃
      Σ B : {B : Finset α // B ⊆ s ∧ a ∈ B}, Finpartition (s \ B.1) where
  toFun P :=
    ⟨⟨P.part a, P.part_subset a, P.mem_part ha⟩, P.avoid (P.part a)⟩
  invFun q := by
    let B : Finset α := q.1.1
    have hBne : B ≠ ∅ := by
      intro h
      have hmem : a ∈ (∅ : Finset α) := h ▸ q.1.2.2
      nomatch hmem
    exact q.2.extend hBne Finset.sdiff_disjoint
      (Finset.sdiff_union_of_subset q.1.2.1)
  left_inv P := by
    apply Finpartition.ext
    change insert (P.part a) (P.avoid (P.part a)).parts = P.parts
    rw [finpartition_parts_avoid_part P (P.part_mem.mpr ha)]
    exact Finset.insert_erase (P.part_mem.mpr ha)
  right_inv q := by
    rcases q with ⟨⟨B, hBs, haB⟩, Q⟩
    have hBne : B ≠ ∅ := by
      intro h
      have hmem : a ∈ (∅ : Finset α) := h ▸ haB
      nomatch hmem
    let E : Finpartition s :=
      Q.extend hBne Finset.sdiff_disjoint
        (Finset.sdiff_union_of_subset hBs)
    have hBmem : B ∈ E.parts := by
      change B ∈ insert B Q.parts
      exact Finset.mem_insert_self B Q.parts
    change
      (⟨⟨E.part a, E.part_subset a, E.mem_part ha⟩, E.avoid (E.part a)⟩ :
        Σ C : {C : Finset α // C ⊆ s ∧ a ∈ C}, Finpartition (s \ C.1)) =
      ⟨⟨B, hBs, haB⟩, Q⟩
    have hpart : E.part a = B := E.part_eq_of_mem hBmem haB
    have hsupp : s \ E.part a = s \ B :=
      congrArg (fun C : Finset α => s \ C) hpart
    have hcopy : (E.avoid (E.part a)).copy hsupp = Q := by
      apply Finpartition.ext
      rw [Finpartition.copy_parts, hpart, finpartition_parts_avoid_part E hBmem]
      change (insert B Q.parts).erase B = Q.parts
      rw [Finset.erase_insert]
      intro hBQ
      have hsub : B ⊆ s \ B := Q.subset hBQ
      have hmem : a ∈ s \ B := hsub haB
      exact (Finset.mem_sdiff.mp hmem).2 haB
    refine Sigma.ext (Subtype.ext hpart) ?_
    exact (finpartition_heq_copy (E.avoid (E.part a)) hsupp).trans
      (heq_of_eq hcopy)

/-- The weighted sum over actual labelled set partitions. -/
def labelledPartitionWeight
    {α R : Type*} [DecidableEq α] [CommSemiring R]
    (w : ℕ → R) (s : Finset α) : R :=
  ∑ P : Finpartition s, ∏ B ∈ P.parts, w B.card

/-- Exact marked-block recurrence for the labelled partition sum. -/
theorem labelledPartitionWeight_eq_sum_markedBlock
    {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R]
    (w : ℕ → R) (s : Finset α) (a : α) (ha : a ∈ s) :
    labelledPartitionWeight w s =
      ∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B},
        w B.1.card * labelledPartitionWeight w (s \ B.1) := by
  classical
  let e := finpartitionMarkedBlockEquiv s a ha
  unfold labelledPartitionWeight
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_sigma'
    (fun (B : {B : Finset α // B ⊆ s ∧ a ∈ B})
      (Q : Finpartition (s \ B.1)) =>
      w B.1.card * ∏ C ∈ Q.parts, w C.card)]
  rw [← e.sum_comp]
  apply Fintype.sum_congr
  intro P
  let B := P.part a
  change (∏ C ∈ P.parts, w C.card) =
    w B.card * ∏ C ∈ (P.avoid B).parts, w C.card
  have hB : B ∈ P.parts := P.part_mem.mpr ha
  have hparts : (P.avoid B).parts = P.parts.erase B :=
    finpartition_parts_avoid_part P hB
  rw [← Finset.mul_prod_erase _ _ hB, hparts]

/-- Coefficient recurrence for the substituted formal exponential. This is
the algebraic counterpart of `labelledPartitionWeight_eq_sum_markedBlock`:
the second antidiagonal coordinate is the size-minus-one of the marked
block. -/
theorem powerSeries_subst_exp_coeff_succ
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : PowerSeries R) (hA : PowerSeries.HasSubst A) (n : ℕ) :
    (n + 1 : R) * PowerSeries.coeff (n + 1)
        (PowerSeries.subst A (PowerSeries.exp R)) =
      ∑ ij ∈ Finset.antidiagonal n,
        PowerSeries.coeff ij.1
            (PowerSeries.subst A (PowerSeries.exp R)) *
          ((ij.2 + 1 : R) * PowerSeries.coeff (ij.2 + 1) A) := by
  have hder := PowerSeries.derivative_subst
    (f := PowerSeries.exp R) (g := A) hA
  rw [PowerSeries.derivative_exp] at hder
  have hcoeff := congrArg (PowerSeries.coeff n) hder
  simpa only [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_comm, mul_left_comm,
    mul_assoc] using hcoeff

/-- Erasing the marked label identifies subsets of `s` containing it with
arbitrary subsets of the remaining labels. -/
noncomputable def markedSubsetEraseEquiv
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∈ s) :
    {B : Finset α // B ⊆ s ∧ a ∈ B} ≃ (s.erase a).powerset where
  toFun B := ⟨B.1.erase a, by
    rw [Finset.mem_powerset]
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxa, hxB⟩
    exact Finset.mem_erase.mpr ⟨hxa, B.2.1 hxB⟩⟩
  invFun T := ⟨insert a T.1, by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact ha
      · exact Finset.erase_subset a s ((Finset.mem_powerset.mp T.2) hxT)
    · exact Finset.mem_insert_self a T.1⟩
  left_inv B := by
    apply Subtype.ext
    exact Finset.insert_erase B.2.2
  right_inv T := by
    apply Subtype.ext
    have hnot : a ∉ T.1 := by
      intro hat
      exact (Finset.mem_erase.mp ((Finset.mem_powerset.mp T.2) hat)).1 rfl
    change (insert a T.1).erase a = T.1
    rw [Finset.erase_insert]
    exact hnot

/-- The sum over marked subsets, regrouped exactly by the number of
unmarked labels in the subset. -/
theorem sum_markedSubsets_by_card
    {α R : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid R]
    (s : Finset α) (a : α) (ha : a ∈ s) (f : ℕ → R) :
    (∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B}, f B.1.card) =
      ∑ j ∈ Finset.range s.card,
        (Nat.choose (s.card - 1) j) • f (j + 1) := by
  classical
  let e := markedSubsetEraseEquiv s a ha
  have he :
      (∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B}, f B.1.card) =
        ∑ T : (s.erase a).powerset, f (T.1.card + 1) := by
    rw [← e.sum_comp]
    apply Fintype.sum_congr
    intro B
    change f B.1.card = f ((B.1.erase a).card + 1)
    rw [Finset.card_erase_of_mem B.2.2]
    exact congrArg f (Nat.sub_add_cancel
      (Finset.one_le_card.mpr ⟨a, B.2.2⟩)).symm
  rw [he]
  calc
    (∑ T : (s.erase a).powerset, f (T.1.card + 1)) =
        ∑ T ∈ (s.erase a).powerset, f (T.card + 1) := by
      simpa only using
        (Finset.sum_coe_sort
          (f := fun T : Finset α => f (T.card + 1))
          (s := (s.erase a).powerset))
    _ = ∑ j ∈ Finset.range ((s.erase a).card + 1),
        (Nat.choose (s.erase a).card j) • f (j + 1) := by
      rw [Finset.sum_powerset]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_powersetCard j (s.erase a) (fun m => f (m + 1))
    _ = ∑ j ∈ Finset.range s.card,
        (Nat.choose (s.card - 1) j) • f (j + 1) := by
      have hcard : (s.erase a).card + 1 = s.card := by
        rw [Finset.card_erase_of_mem ha]
        exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨a, ha⟩)
      rw [hcard, Finset.card_erase_of_mem ha]

/-- Factorial normalization turns the derivative recurrence for the
substituted exponential into the labelled marked-block recurrence. -/
theorem factorial_mul_subst_exp_coeff_succ
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : PowerSeries R) (hA : PowerSeries.HasSubst A) (n : ℕ) :
    (n + 1).factorial * PowerSeries.coeff (n + 1)
        (PowerSeries.subst A (PowerSeries.exp R)) =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : R) *
          ((j + 1).factorial * PowerSeries.coeff (j + 1) A) *
          ((n - j).factorial * PowerSeries.coeff (n - j)
            (PowerSeries.subst A (PowerSeries.exp R))) := by
  have hrec := powerSeries_subst_exp_coeff_succ A hA n
  rw [← Finset.Nat.sum_antidiagonal_swap] at hrec
  simp only [Prod.swap] at hrec
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  calc
    (n + 1).factorial * PowerSeries.coeff (n + 1)
          (PowerSeries.subst A (PowerSeries.exp R)) =
        n.factorial * ((n + 1 : R) * PowerSeries.coeff (n + 1)
          (PowerSeries.subst A (PowerSeries.exp R))) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = n.factorial *
        (∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff (n - j)
              (PowerSeries.subst A (PowerSeries.exp R)) *
            ((j + 1 : R) * PowerSeries.coeff (j + 1) A)) := by
      rw [hrec]
    _ = ∑ j ∈ Finset.range (n + 1),
        n.factorial *
          (PowerSeries.coeff (n - j)
              (PowerSeries.subst A (PowerSeries.exp R)) *
            ((j + 1 : R) * PowerSeries.coeff (j + 1) A)) := by
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : R) *
          ((j + 1).factorial * PowerSeries.coeff (j + 1) A) *
          ((n - j).factorial * PowerSeries.coeff (n - j)
            (PowerSeries.subst A (PowerSeries.exp R))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hfac :
          (Nat.choose n j : R) * (j.factorial : R) *
              ((n - j).factorial : R) = (n.factorial : R) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul,
          Nat.choose_mul_factorial_mul_factorial hjle]
      rw [← hfac, Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The exact labelled exponential formula, proved from actual finite set
partitions. No coefficient recursion is assumed: the only hypothesis on the
inner series is the zero constant term required for substitution. -/
theorem labelledPartitionWeight_eq_factorial_mul_subst_exp_coeff
    {α R : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] [Algebra ℚ R]
    (A : PowerSeries R) (hA0 : PowerSeries.constantCoeff A = 0)
    (s : Finset α) :
    labelledPartitionWeight
        (fun n => (n.factorial : R) * PowerSeries.coeff n A) s =
      (s.card.factorial : R) * PowerSeries.coeff s.card
        (PowerSeries.subst A (PowerSeries.exp R)) := by
  classical
  let w : ℕ → R :=
    fun n => (n.factorial : R) * PowerSeries.coeff n A
  let E : PowerSeries R := PowerSeries.subst A (PowerSeries.exp R)
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hE0 : PowerSeries.coeff 0 E = 1 := by
    dsimp only [E]
    rw [PowerSeries.coeff_subst' hA (PowerSeries.exp R) 0,
      finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_pow, hA0, zero_pow hd]
      simp
  change labelledPartitionWeight w s =
    (s.card.factorial : R) * PowerSeries.coeff s.card E
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      cases n with
      | zero =>
          have hs0 : s = ∅ := Finset.card_eq_zero.mp hcard
          subst s
          simp only [Nat.factorial_zero, Nat.cast_one, one_mul, hE0]
          unfold labelledPartitionWeight
          change (∑ P : Finpartition (⊥ : Finset α),
            ∏ B ∈ P.parts, w B.card) = 1
          rw [Fintype.sum_unique]
          change (∏ B ∈ (Finpartition.empty (Finset α)).parts,
            w B.card) = 1
          simp
      | succ m =>
          have hsne : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
          obtain ⟨a, ha⟩ := hsne
          rw [labelledPartitionWeight_eq_sum_markedBlock w s a ha]
          calc
            (∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B},
                w B.1.card * labelledPartitionWeight w (s \ B.1)) =
                ∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B},
                  w B.1.card *
                    (((s \ B.1).card.factorial : R) *
                      PowerSeries.coeff (s \ B.1).card E) := by
              apply Fintype.sum_congr
              intro B
              have hlt : (s \ B.1).card < m + 1 := by
                rw [Finset.card_sdiff_of_subset B.2.1, hcard]
                have hBpos : 0 < B.1.card :=
                  Finset.card_pos.mpr ⟨a, B.2.2⟩
                omega
              rw [ih _ hlt (s \ B.1) rfl]
            _ = ∑ B : {B : Finset α // B ⊆ s ∧ a ∈ B},
                w B.1.card *
                  (((m + 1 - B.1.card).factorial : R) *
                    PowerSeries.coeff (m + 1 - B.1.card) E) := by
              apply Fintype.sum_congr
              intro B
              rw [Finset.card_sdiff_of_subset B.2.1, hcard]
            _ = ∑ j ∈ Finset.range s.card,
                (Nat.choose (s.card - 1) j) •
                  (w (j + 1) *
                    (((m + 1 - (j + 1)).factorial : R) *
                      PowerSeries.coeff (m + 1 - (j + 1)) E)) := by
              exact sum_markedSubsets_by_card s a ha
                (fun k => w k *
                  (((m + 1 - k).factorial : R) *
                    PowerSeries.coeff (m + 1 - k) E))
            _ = (m + 1).factorial * PowerSeries.coeff (m + 1) E := by
              simpa [hcard, w, E, nsmul_eq_mul, mul_assoc] using
                (factorial_mul_subst_exp_coeff_succ A hA m).symm

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The labelled exponential formula specialized to the actual
coefficientwise kernel action on the type-resolved rooted-tree series. -/
theorem CompactBJRModel.labelledPartitionWeight_kernelAction_typeRootedTreeEGF
    (M : CompactBJRModel S) (n : ℕ) :
    labelledPartitionWeight
        (fun k => (k.factorial : C(S, ℝ)) *
          PowerSeries.coeff k
            (M.kernelActionPowerSeries M.typeRootedTreeEGF))
        (Finset.univ : Finset (Fin n)) =
      (n.factorial : C(S, ℝ)) * PowerSeries.coeff n
        (PowerSeries.subst
          (M.kernelActionPowerSeries M.typeRootedTreeEGF)
          (PowerSeries.exp C(S, ℝ))) := by
  simpa using
    (labelledPartitionWeight_eq_factorial_mul_subst_exp_coeff
      (M.kernelActionPowerSeries M.typeRootedTreeEGF)
      M.kernelAction_typeRootedTreeEGF_constantCoeff
      (Finset.univ : Finset (Fin n)))

/-- Pointwise form after adjoining the genuine root-vertex factor. Its
right-hand side is the size-`n + 1` coefficient of the actual formal
rooted-tree right-hand side. -/
theorem CompactBJRModel.zeroTreeVertexFactor_mul_labelledPartitionWeight_eq
    (M : CompactBJRModel S) (n : ℕ) (root : S) :
    M.zeroTreeVertexFactor root *
        (labelledPartitionWeight
          (fun k => (k.factorial : C(S, ℝ)) *
            PowerSeries.coeff k
              (M.kernelActionPowerSeries M.typeRootedTreeEGF))
          (Finset.univ : Finset (Fin n))) root =
      (n.factorial : ℝ) *
        PowerSeries.coeff (n + 1)
          (M.rootedTreeFormalRHS M.typeRootedTreeEGF) root := by
  have hmap :
      M.zeroTreeVertexFactor *
          labelledPartitionWeight
            (fun k => (k.factorial : C(S, ℝ)) *
              PowerSeries.coeff k
                (M.kernelActionPowerSeries M.typeRootedTreeEGF))
            (Finset.univ : Finset (Fin n)) =
        (n.factorial : C(S, ℝ)) *
          PowerSeries.coeff (n + 1)
            (M.rootedTreeFormalRHS M.typeRootedTreeEGF) := by
    rw [M.labelledPartitionWeight_kernelAction_typeRootedTreeEGF n]
    rw [CompactBJRModel.rootedTreeFormalRHS,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    ring
  exact congrArg (fun f : C(S, ℝ) => f root) hmap

end PerronWright
