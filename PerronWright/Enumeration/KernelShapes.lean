import PerronWright.Enumeration.KernelBounds
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Sigma

noncomputable section
namespace PerronWright
namespace FiniteMultiGraph

def endpointsEquiv (v e : ℕ) : FiniteMultiGraph v e ≃ (Fin e → Sym2 (Fin v)) where
  toFun H := H.endpoints
  invFun f := ⟨f⟩
  left_inv H := by cases H; rfl
  right_inv f := rfl

instance (v e : ℕ) : Fintype (FiniteMultiGraph v e) :=
  Fintype.ofEquiv (Fin e → Sym2 (Fin v)) (endpointsEquiv v e).symm

theorem vertices_eq_two_excess_iff_cubic {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hmin : ∀ x : Fin v, 3 ≤ H.degree x) (hexcess : e = v + ell) :
    v = 2 * ell ↔ ∀ x : Fin v, H.degree x = 3 := by
  constructor
  · intro hv
    have hsum : (∑ x : Fin v, (3 : ℕ)) = ∑ x : Fin v, H.degree x := by
      rw [H.sum_degree]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    have heq := (Finset.sum_eq_sum_iff_of_le (fun x (_ : x ∈ Finset.univ) => hmin x)).mp hsum
    intro x
    exact (heq x (Finset.mem_univ x)).symm
  · intro hcubic
    have hsum := H.sum_degree
    simp only [hcubic, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega

theorem edges_eq_three_excess_iff_cubic {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hmin : ∀ x : Fin v, 3 ≤ H.degree x) (hexcess : e = v + ell) :
    e = 3 * ell ↔ ∀ x : Fin v, H.degree x = 3 := by
  rw [← H.vertices_eq_two_excess_iff_cubic hmin hexcess]
  omega

theorem cubic_counts {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hcubic : ∀ x : Fin v, H.degree x = 3) (hexcess : e = v + ell) :
    v = 2 * ell ∧ e = 3 * ell := by
  have hmin : ∀ x : Fin v, 3 ≤ H.degree x := fun x => (hcubic x).symm.le
  exact ⟨(H.vertices_eq_two_excess_iff_cubic hmin hexcess).mpr hcubic,
    (H.edges_eq_three_excess_iff_cubic hmin hexcess).mpr hcubic⟩

end FiniteMultiGraph

/-- A finite ambient type for vertex- and edge-labelled endpoint shapes.
No injectivity or looplessness restriction is imposed on the endpoints. -/
def BoundedKernelShape (ell : ℕ) :=
  Σ v : Fin (2 * ell + 1), Σ e : Fin (3 * ell + 1), FiniteMultiGraph v.val e.val

instance (ell : ℕ) : Fintype (BoundedKernelShape ell) := by
  unfold BoundedKernelShape
  infer_instance

def BoundedKernelShape.IsKernel {ell : ℕ} (H : BoundedKernelShape ell) : Prop :=
  (∀ x, 3 ≤ H.2.2.degree x) ∧ H.2.1.val = H.1.val + ell

/-- Fixed-excess multigraph kernels are a subtype of an explicitly finite type. -/
def KernelShape (ell : ℕ) := {H : BoundedKernelShape ell // H.IsKernel}

instance (ell : ℕ) : Fintype (KernelShape ell) := by
  classical
  unfold KernelShape
  infer_instance

def FiniteMultiGraph.toKernelShape {v e ell : ℕ} (H : FiniteMultiGraph v e)
    (hmin : ∀ x : Fin v, 3 ≤ H.degree x) (hexcess : e = v + ell) : KernelShape ell :=
  ⟨⟨⟨v, Nat.lt_succ_of_le (H.vertices_le_two_excess hmin hexcess)⟩,
      ⟨e, Nat.lt_succ_of_le (H.edges_le_three_excess hmin hexcess)⟩, H⟩, hmin, hexcess⟩

/-- Forget the bounds but retain the literal vertex labels, edge labels,
loops, and repetitions of endpoint pairs. -/
def KernelShape.forget {ell : ℕ} (H : KernelShape ell) :
    Σ v : ℕ, Σ e : ℕ, FiniteMultiGraph v e :=
  ⟨H.val.1.val, H.val.2.1.val, H.val.2.2⟩

@[simp] theorem FiniteMultiGraph.toKernelShape_forget {v e ell : ℕ}
    (H : FiniteMultiGraph v e) (hmin : ∀ x : Fin v, 3 ≤ H.degree x)
    (hexcess : e = v + ell) :
    (H.toKernelShape hmin hexcess).forget = ⟨v, e, H⟩ := rfl

theorem finite_kernel_shapes (ell : ℕ) :
    Set.Finite {H : (Σ v : ℕ, Σ e : ℕ, FiniteMultiGraph v e) |
      (∀ x, 3 ≤ H.2.2.degree x) ∧ H.2.1 = H.1 + ell} := by
  have hr : Set.Finite (Set.range (KernelShape.forget (ell := ell))) := Set.finite_range _
  apply hr.subset
  intro H hH
  exact ⟨H.2.2.toKernelShape hH.1 hH.2, rfl⟩





end PerronWright

