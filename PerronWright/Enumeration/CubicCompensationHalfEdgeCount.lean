import PerronWright.Enumeration.KernelBounds
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact degree-constrained half-edge coefficients

The multinomial coefficient is obtained here from an actual finite sum over
half-edge assignments, by extracting a coefficient of the literal product
of sums.  This is the all-kernel counting ingredient of the connected cubic
decomposition, with neither connectivity nor its eventual recurrence assumed.
-/

noncomputable section

open scoped BigOperators Classical

namespace PerronWright.GraphCore

variable {I V : Type*} [Fintype I] [Fintype V]

/-- The literal multiplicity vector of a labelled half-edge assignment. -/
def halfEdgeExponent (x : I → V) : V →₀ ℕ :=
  ∑ i : I, Finsupp.single (x i) 1

omit [Fintype V] in
theorem halfEdgeExponent_apply (x : I → V) (v : V) :
    halfEdgeExponent x v = Fintype.card {i : I // x i = v} := by
  simp [halfEdgeExponent, Fintype.card_subtype, Finsupp.single_apply,
    Finset.sum_boole]

omit [Fintype V] in
theorem prod_halfEdge_variables (x : I → V) :
    (∏ i : I, (MvPolynomial.X (x i) : MvPolynomial V ℕ)) =
      MvPolynomial.monomial (halfEdgeExponent x) 1 := by
  simpa [halfEdgeExponent, MvPolynomial.X] using
    (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i : I ↦ Finsupp.single (x i) 1) (fun _ ↦ (1 : ℕ))).symm

/-- A coefficient of the finite half-edge assignment polynomial is exactly
the cardinal of its actual degree-vector fibre. -/
theorem card_halfEdgeExponent_fiber (d : V →₀ ℕ) :
    Fintype.card {x : I → V // halfEdgeExponent x = d} =
      MvPolynomial.coeff d
        ((∑ v : V, (MvPolynomial.X v : MvPolynomial V ℕ)) ^ Fintype.card I) := by
  have hp : ((∑ v : V, (MvPolynomial.X v : MvPolynomial V ℕ)) ^ Fintype.card I) =
      ∑ x : I → V, MvPolynomial.monomial (halfEdgeExponent x) 1 := by
    calc
      _ = ∏ _i : I, ∑ v : V, (MvPolynomial.X v : MvPolynomial V ℕ) := by simp
      _ = ∑ x : I → V, ∏ i : I, (MvPolynomial.X (x i) : MvPolynomial V ℕ) :=
        Fintype.prod_sum _
      _ = _ := by simp_rw [prod_halfEdge_variables]
  rw [hp, MvPolynomial.coeff_sum]
  simp [Fintype.card_subtype, MvPolynomial.coeff_monomial, eq_comm]

theorem card_halfEdgeExponent_fiber_eq_multinomial (d : V →₀ ℕ)
    (hd : d.sum (fun _ n ↦ n) = Fintype.card I) :
    Fintype.card {x : I → V // halfEdgeExponent x = d} = d.multinomial := by
  rw [card_halfEdgeExponent_fiber, MvPolynomial.coeff_sum_X_pow_of_fintype,
    if_pos hd]
  rfl

/-- Actual labelled half-edge maps with exactly `degree` occurrences of each
vertex label. -/
abbrev UniformHalfEdgeAssignment (I V : Type*) [Fintype I]
    (degree : ℕ) := {x : I → V // ∀ v, Nat.card {i : I // x i = v} = degree}

theorem card_uniformHalfEdgeAssignment_mul_factorialPower (degree : ℕ)
    [Fintype (UniformHalfEdgeAssignment I V degree)]
    (hsize : Fintype.card I = degree * Fintype.card V) :
    Fintype.card (UniformHalfEdgeAssignment I V degree) *
        degree.factorial ^ Fintype.card V = (Fintype.card I).factorial := by
  let d : V →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ ↦ degree)
  have hdv (v : V) : d v = degree := by simp [d]
  have hds : d.sum (fun _ n ↦ n) = Fintype.card I := by
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
    simp [hdv, hsize, mul_comm]
  have he : (UniformHalfEdgeAssignment I V degree) ≃
      {x : I → V // halfEdgeExponent x = d} :=
    Equiv.subtypeEquivRight (fun x ↦ by
      rw [Finsupp.ext_iff]
      simp [halfEdgeExponent_apply, hdv, Nat.card_eq_fintype_card])
  rw [Fintype.card_congr he, card_halfEdgeExponent_fiber_eq_multinomial d hds]
  have hm := Nat.multinomial_spec (Finset.univ : Finset V) (fun _ ↦ degree)
  have hdmu : d.multinomial = Nat.multinomial Finset.univ (fun _ : V ↦ degree) := by
    rw [← Finsupp.multinomial_of_support_subset (Finset.subset_univ _)]
    exact Nat.multinomial_congr (fun v _ ↦ hdv v)
  rw [hdmu]
  simpa [hsize, mul_comm] using hm

/-- Cubic half-edges retain both the actual edge label and the endpoint side. -/
abbrev CubicHalfEdgeSlot (ell : ℕ) := Fin (3 * ell) × Bool

theorem card_cubicHalfEdgeSlot (ell : ℕ) :
    Fintype.card (CubicHalfEdgeSlot ell) = 6 * ell := by
  simp [CubicHalfEdgeSlot, mul_comm, mul_left_comm]

theorem card_cubicHalfEdgeAssignment_mul_sixPower (ell : ℕ) :
    Fintype.card (UniformHalfEdgeAssignment (CubicHalfEdgeSlot ell) (Fin (2 * ell)) 3) *
        6 ^ (2 * ell) = (6 * ell).factorial := by
  have hs : Fintype.card (CubicHalfEdgeSlot ell) =
      3 * Fintype.card (Fin (2 * ell)) := by
    rw [card_cubicHalfEdgeSlot, Fintype.card_fin]
    omega
  simpa only [card_cubicHalfEdgeSlot, Fintype.card_fin,
    show Nat.factorial 3 = 6 from rfl] using
    (card_uniformHalfEdgeAssignment_mul_factorialPower
      (I := CubicHalfEdgeSlot ell) (V := Fin (2 * ell)) 3 hs)

end PerronWright.GraphCore
