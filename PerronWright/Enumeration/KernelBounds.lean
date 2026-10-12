import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sym.Sym2
import PerronWright.Enumeration.ConnectedWeight

/-!
Arithmetic of the multigraph kernel after suppressing degree-two paths.
The endpoint representation retains loops and parallel edges.
-/

noncomputable section
namespace PerronWright

/-- An edge-labelled multigraph; loops and parallel edges are allowed. -/
structure FiniteMultiGraph (v e : ℕ) where
  endpoints : Fin e → Sym2 (Fin v)

namespace FiniteMultiGraph

/-- A loop contributes twice to the degree of its endpoint. -/
def incidence {v : ℕ} (edge : Sym2 (Fin v)) (x : Fin v) : ℕ :=
  Sym2.lift ⟨fun i j => (if i = x then 1 else 0) + (if j = x then 1 else 0), by
    intro i j
    apply add_comm⟩ edge

@[simp] theorem incidence_mk {v : ℕ} (i j x : Fin v) :
    incidence s(i,j) x = (if i = x then 1 else 0) + (if j = x then 1 else 0) := rfl

theorem sum_incidence {v : ℕ} (edge : Sym2 (Fin v)) :
    ∑ x : Fin v, incidence edge x = 2 := by
  classical
  induction edge using Sym2.inductionOn with
  | _ i j =>
      simp [incidence_mk, Finset.sum_add_distrib]

def degree {v e : ℕ} (H : FiniteMultiGraph v e) (x : Fin v) : ℕ :=
  ∑ edge : Fin e, incidence (H.endpoints edge) x

theorem sum_degree {v e : ℕ} (H : FiniteMultiGraph v e) :
    ∑ x : Fin v, H.degree x = 2 * e := by
  classical
  unfold degree
  rw [Finset.sum_comm]
  simp [sum_incidence, mul_comm]

/-- Any multigraph kernel of minimum degree three and excess `ell` has
at most `2 ell` vertices; this is independent of connectivity. -/
theorem vertices_le_two_excess {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hmin : ∀ x : Fin v, 3 ≤ H.degree x)
    (hexcess : e = v + ell) : v ≤ 2 * ell := by
  have hsum : 3 * v ≤ ∑ x : Fin v, H.degree x := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun x (_ : x ∈ Finset.univ) => hmin x)
    simpa [mul_comm] using h
  rw [H.sum_degree, hexcess] at hsum
  omega

theorem edges_le_three_excess {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hmin : ∀ x : Fin v, 3 ≤ H.degree x)
    (hexcess : e = v + ell) : e ≤ 3 * ell := by
  have hv := H.vertices_le_two_excess hmin hexcess
  omega

end FiniteMultiGraph
end PerronWright

