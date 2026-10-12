import PerronWright.Kernel.FiniteIrreducibleSpectral
import PerronWright.Analysis.CompactSymmetric

/-!
# Nonnegative critical Perron vectors without primitivity

The absolute value of a self-adjoint norm endpoint eigenvector is fixed
for a nonnegative finite matrix of norm one.  This permits an eigenvalue
`-1`; irreducibility, rather than a strictly positive power, will then
upgrade the nonnegative fixed vector to a positive simple Perron vector.
-/

open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

def absVector (M : FiniteIrreducibleModel S) (v : M.Hilbert) : M.Hilbert :=
  WithLp.toLp 2 (fun a ↦ |v a|)

@[simp] theorem absVector_apply (M : FiniteIrreducibleModel S) (v : M.Hilbert) (a : S) :
    M.absVector v a = |v a| := rfl

theorem norm_absVector (M : FiniteIrreducibleModel S) (v : M.Hilbert) :
    ‖M.absVector v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, M.absVector_apply, sq_abs]

theorem eq_of_nonneg_le_of_norm_le (M : FiniteIrreducibleModel S) (v w : M.Hilbert)
    (hv : ∀ a, 0 ≤ v a) (hvw : ∀ a, v a ≤ w a) (hnorm : ‖w‖ ≤ ‖v‖) : v = w := by
  have hsq : ∀ a, v a ^ 2 ≤ w a ^ 2 := fun a ↦
    (sq_le_sq₀ (hv a) ((hv a).trans (hvw a))).mpr (hvw a)
  have hs : (∑ a, v a ^ 2) = ∑ a, w a ^ 2 := by
    apply le_antisymm (Finset.sum_le_sum (fun a _ ↦ hsq a))
    simpa only [EuclideanSpace.real_norm_sq_eq] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  have he := (Finset.sum_eq_sum_iff_of_le (fun a _ ↦ hsq a)).mp hs
  apply (WithLp.ext_iff 2).mpr
  funext a
  exact (sq_eq_sq₀ (hv a) ((hv a).trans (hvw a))).mp (he a (Finset.mem_univ a))

theorem abs_operator_le (M : FiniteIrreducibleModel S) (v : M.Hilbert) (a : S) :
    |M.operator v a| ≤ M.operator (M.absVector v) a := by
  rw [M.operator_apply, M.operator_apply]
  calc
    |∑ b, M.symmetricMatrix a b * v b| ≤ ∑ b, |M.symmetricMatrix a b * v b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, M.symmetricMatrix a b * M.absVector v b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (M.symmetricMatrix_nonneg a b), M.absVector_apply]

theorem fixed_abs_of_endpoint_eigenvector (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) {lam : ℝ} (hlam : |lam| = 1) (v : M.Hilbert)
    (hev : M.operator v = lam • v) : M.operator (M.absVector v) = M.absVector v := by
  apply Eq.symm
  apply M.eq_of_nonneg_le_of_norm_le
  · intro a
    exact abs_nonneg _
  · intro a
    have he : |M.operator v a| = |v a| := by
      rw [hev]
      change |lam * v a| = |v a|
      rw [abs_mul, hlam, one_mul]
    rw [M.absVector_apply, ← he]
    exact M.abs_operator_le v a
  · simpa [M.norm_operator_eq_one hcrit] using M.operator.le_opNorm (M.absVector v)

theorem exists_nonnegative_fixed (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ v : M.Hilbert, v ≠ 0 ∧ (∀ a, 0 ≤ v a) ∧ M.operator v = v := by
  have hev := PerronWright.eigenvalue_one_or_neg_one M.operator M.isCompactOperator_operator
    M.isSymmetric_operator (M.norm_operator_eq_one hcrit)
  have he : ∃ lam : ℝ, |lam| = 1 ∧ Module.End.HasEigenvalue M.operator.toLinearMap lam := by
    rcases hev with hp | hn
    · exact ⟨1, by norm_num, hp⟩
    · exact ⟨-1, by norm_num, hn⟩
  obtain ⟨lam, hlam, hev⟩ := he
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  have hfix := M.fixed_abs_of_endpoint_eigenvector hcrit hlam v (Module.End.mem_eigenspace_iff.mp hv)
  have habsne : M.absVector v ≠ 0 := by
    intro hz
    apply hvne
    apply norm_eq_zero.mp
    rw [← M.norm_absVector v, hz, norm_zero]
  exact ⟨M.absVector v, habsne, fun a ↦ abs_nonneg _, hfix⟩

end PerronWright.FiniteIrreducibleModel
