import PerronWright.Analysis.FiniteIrreducibleAbsolute
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Positive simple Perron eigenspace from irreducibility

A zero coordinate of a nonnegative fixed vector propagates along every
positive kernel edge.  The literal irreducibility assumption propagates it
to every coordinate, contradicting nonzeroness.  The same argument for
absolute values yields geometric and generalized-eigenspace simplicity.
No primitivity or exclusion of eigenvalue `-1` is used.
-/

open Module

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem nonnegative_fixed_pos (M : FiniteIrreducibleModel S) (v : M.Hilbert)
    (hv : ∀ a, 0 ≤ v a) (hvne : v ≠ 0) (hfix : M.operator v = v) (a : S) :
    0 < v a := by
  apply lt_of_le_of_ne (hv a)
  intro hzero
  have hstep : ∀ i j, 0 < M.kernel i j → v i = 0 → v j = 0 := by
    intro i j hij hi
    have he := congrArg (fun v : M.Hilbert ↦ v i) hfix
    rw [M.operator_apply, hi] at he
    have hle : M.symmetricMatrix i j * v j ≤ ∑ b, M.symmetricMatrix i b * v b :=
      Finset.single_le_sum (fun b _ ↦ mul_nonneg (M.symmetricMatrix_nonneg i b) (hv b))
        (Finset.mem_univ j)
    have hp : 0 < M.symmetricMatrix i j := (M.symmetricMatrix_pos_iff i j).mpr hij
    have hprod : M.symmetricMatrix i j * v j = 0 :=
      le_antisymm (he ▸ hle) (mul_nonneg hp.le (hv j))
    exact (mul_eq_zero.mp hprod).resolve_left hp.ne'
  let _ : Quiver S := Matrix.toQuiver M.kernel
  have hpath : ∀ {i j : S}, Quiver.Path i j → v i = 0 → v j = 0 := by
    intro i j p
    induction p with
    | nil => exact fun hi ↦ hi
    | @cons b c p e ih =>
      intro hi
      exact hstep b c e.down (ih hi)
  have hz : v = 0 := by
    apply (WithLp.ext_iff 2).mpr
    funext b
    obtain ⟨p, _⟩ := M.irreducible.connected a b
    exact hpath p hzero.symm
  exact hvne hz

theorem exists_positive_fixed (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ v : M.Hilbert, v ≠ 0 ∧ (∀ a, 0 < v a) ∧ M.operator v = v := by
  obtain ⟨v, hvne, hv, hfix⟩ := M.exists_nonnegative_fixed hcrit
  exact ⟨v, hvne, M.nonnegative_fixed_pos v hv hvne hfix, hfix⟩

theorem fixed_abs_pos (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (v : M.Hilbert) (hvne : v ≠ 0) (hfix : M.operator v = v) (a : S) : 0 < |v a| := by
  have hfa := M.fixed_abs_of_endpoint_eigenvector hcrit (lam := 1) (by norm_num) v (by simpa using hfix)
  have hne : M.absVector v ≠ 0 := by
    intro hz
    apply hvne
    apply norm_eq_zero.mp
    rw [← M.norm_absVector v, hz, norm_zero]
  exact M.nonnegative_fixed_pos _ (fun b ↦ abs_nonneg _) hne hfa a

theorem fixed_eq_scalar_multiple (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (u : M.Hilbert) (hu : ∀ a, 0 < u a) (hTu : M.operator u = u)
    (v : M.Hilbert) (hTv : M.operator v = v) : ∃ c : ℝ, v = c • u := by
  let a := Classical.choice M.nonempty
  let c := v a / u a
  let w : M.Hilbert := v - c • u
  have hTw : M.operator w = w := by
    dsimp only [w]
    rw [map_sub, map_smul, hTv, hTu]
  have hwa : w a = 0 := by
    change v a - c * u a = 0
    dsimp only [c]
    rw [div_mul_cancel₀ _ (hu a).ne', sub_self]
  have hz : w = 0 := by
    by_contra hne
    have hp := M.fixed_abs_pos hcrit w hne hTw a
    simp [hwa] at hp
  exact ⟨c, sub_eq_zero.mp hz⟩

theorem eigenspace_one_eq_span (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (u : M.Hilbert) (hu : ∀ a, 0 < u a) (hTu : M.operator u = u) :
    Module.End.eigenspace M.operator.toLinearMap 1 = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨c, hc⟩ := M.fixed_eq_scalar_multiple hcrit u hu hTu v
      (by simpa using Module.End.mem_eigenspace_iff.mp hv)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    exact Module.End.mem_eigenspace_iff.mpr (by simpa using hTu)

theorem genEigenspace_one_finrank (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (u : M.Hilbert) (hu : ∀ a, 0 < u a) (hTu : M.operator u = u)
    {n : ℕ∞} (hn : 0 < n) :
    Module.finrank ℝ (Module.End.genEigenspace M.operator.toLinearMap 1 n) = 1 := by
  rw [M.isSymmetric_operator.isFinitelySemisimple.genEigenspace_eq_eigenspace 1 hn,
    M.eigenspace_one_eq_span hcrit u hu hTu]
  apply finrank_span_singleton
  intro hz
  have hp := hu (Classical.choice M.nonempty)
  simp [hz] at hp

end PerronWright.FiniteIrreducibleModel
