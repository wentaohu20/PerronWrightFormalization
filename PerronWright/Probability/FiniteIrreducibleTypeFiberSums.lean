import PerronWright.Probability.FiniteIrreducibleTypePlacementMultiplicity
import Mathlib.Logic.Equiv.Sum

/-!
# Exact sums over actual finite type fibres

These identities retain the true empirical type counts of the fixed
assignment. They do not replace empirical weights by a target law.
-/

open scoped BigOperators Classical

noncomputable section

namespace PerronWright.FiniteIrreducibleTypeFiberSums

open FiniteIrreducibleTypePlacementMultiplicity

variable {A B S : Type*} [Fintype A] [Fintype B] [Fintype S]

omit [Fintype A] in
theorem sum_fiberCount (x : B → S) :
    ∑ a : S, fiberCount x a = Fintype.card B := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv x)
  simpa only [Fintype.card_sigma, fiberCount] using h

omit [Fintype A] in
/-- A literal finite sum grouped by the actual fibres of the assignment. -/
theorem sum_by_typeFibers (x : B → S) (F : S → ℝ) :
    (∑ v : B, F (x v)) = ∑ a : S, (fiberCount x a : ℝ) * F a := by
  let e := Equiv.sigmaFiberEquiv x
  calc
    _ = ∑ p : (Σ a : S, {v : B // x v = a}), F (x (e p)) :=
      (e.sum_comp (fun v ↦ F (x v))).symm
    _ = ∑ p : (Σ a : S, {v : B // x v = a}), F p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      change F (x p.2.val) = F p.1
      rw [p.2.property]
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fiberCount]

/-- Every cross-pair sum is exactly the true fibre-count quadratic sum. -/
theorem sum_pair_by_typeFibers (x : A → S) (y : B → S) (H : S → S → ℝ) :
    (∑ v : A, ∑ w : B, H (x v) (y w)) =
      ∑ a : S, ∑ b : S,
        (fiberCount x a : ℝ) * H a b * (fiberCount y b : ℝ) := by
  simp_rw [sum_by_typeFibers y]
  rw [sum_by_typeFibers x (fun a ↦ ∑ b : S, (fiberCount y b : ℝ) * H a b)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end PerronWright.FiniteIrreducibleTypeFiberSums

