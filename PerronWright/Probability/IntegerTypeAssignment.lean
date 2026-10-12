import PerronWright.Model.FiniteTypeCounts
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Basic

/-!
# A literal vertex type assignment with the constructed integer counts

The finite multiset of type slots is put in bijection with `Fin n`.
Consequently the constructed positive counts are realized by actual
deterministic vertex types, not merely by a vector of formal proportions.
-/

open Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.IntegerTypeAssignment

variable {I : Type*} [Fintype I]

/-- Label the finite set of type slots by the actual graph vertex set. -/
def vertexEquiv {n : ℕ} (c : I → ℕ) (hc : ∑ a, c a = n) :
    Fin n ≃ (Σ a : I, Fin (c a)) :=
  (Fintype.equivFinOfCardEq (α := Σ a : I, Fin (c a))
    (by simpa only [Fintype.card_sigma, Fintype.card_fin] using hc)).symm

/-- The actual deterministic type vector attached to the slot labeling. -/
def typeVector {n : ℕ} (c : I → ℕ) (hc : ∑ a, c a = n) (v : Fin n) : I :=
  (vertexEquiv c hc v).1

/-- The type-`a` vertices are in bijection with precisely `c a` slots. -/
def fiberEquiv {n : ℕ} (c : I → ℕ) (hc : ∑ a, c a = n) (a : I) :
    {v : Fin n // typeVector c hc v = a} ≃ Fin (c a) :=
  ((vertexEquiv c hc).subtypeEquiv
    (q := fun p : (Σ a : I, Fin (c a)) ↦ p.1 = a)
    (fun _ ↦ Iff.rfl)).trans (Equiv.sigmaSubtype a)

theorem typeVector_fiber_card {n : ℕ} (c : I → ℕ) (hc : ∑ a, c a = n) (a : I) :
    Fintype.card {v : Fin n // typeVector c hc v = a} = c a :=
  (Fintype.card_congr (fiberEquiv c hc a)).trans (Fintype.card_fin _)

/-- The constructed deterministic assignment of the target finite type law. -/
def roundedTypeVector (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) : Fin n → I :=
  typeVector (FiniteTypeCounts.counts a0 nu n)
    (FiniteTypeCounts.sum_counts a0 nu hnu hsum n)

theorem roundedTypeVector_fiber_card (a0 : I) (nu : I → ℝ)
    (hnu : ∀ a, 0 ≤ nu a) (hsum : ∑ a, nu a = 1) (n : ℕ) (a : I) :
    Fintype.card {v : Fin n // roundedTypeVector a0 nu hnu hsum n v = a} =
      FiniteTypeCounts.counts a0 nu n a := typeVector_fiber_card _ _ a

/-- The empirical probabilities of the actual vertex assignment converge
in total absolute variation, by the proved rounding estimate. -/
theorem roundedTypeVector_empirical_error_tendsto (a0 : I) (nu : I → ℝ)
    (hnu : ∀ a, 0 ≤ nu a) (hsum : ∑ a, nu a = 1) :
    Tendsto (fun n : ℕ ↦ ∑ a : I,
      |(Fintype.card {v : Fin n // roundedTypeVector a0 nu hnu hsum n v = a} : ℝ) /
        (n : ℝ) - nu a|) atTop (nhds 0) := by
  simp_rw [roundedTypeVector_fiber_card]
  exact FiniteTypeCounts.empirical_error_tendsto_zero a0 nu hnu hsum

theorem roundedTypeVector_each_type_eventually (a0 : I) (nu : I → ℝ)
    (hnu : ∀ a, 0 < nu a) (hsum : ∑ a, nu a = 1) :
    ∀ᶠ n : ℕ in atTop, ∀ a : I,
      ∃ v : Fin n, roundedTypeVector a0 nu (fun a ↦ (hnu a).le) hsum n v = a := by
  filter_upwards [FiniteTypeCounts.counts_pos_eventually a0 nu hnu] with n hn
  intro a
  have hc : 0 < Fintype.card {v : Fin n //
      roundedTypeVector a0 nu (fun a ↦ (hnu a).le) hsum n v = a} := by
    rw [roundedTypeVector_fiber_card]
    exact hn a
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨v.val, v.property⟩

end PerronWright.IntegerTypeAssignment
