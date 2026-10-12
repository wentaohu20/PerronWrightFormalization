import PerronWright.Model.FiniteIrreduciblePerronQuantities
import Mathlib.Tactic.FinCases

/-!
# A critical bipartite regression model

Two equally likely types have kernel two across the two parts and zero
within them.  This literal irreducible critical model has eigenvalue `-1`.
It witnesses why the general finite branch cannot assume the compact
primitive branch's exclusion of the negative unit endpoint.
-/

open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

def bipartite : FiniteIrreducibleModel (Fin 2) where
  weight := fun _ ↦ 1 / 2
  weight_pos := fun _ ↦ by norm_num
  weight_sum := by norm_num [Fin.sum_univ_two]
  kernel := fun a b ↦ if a = b then 0 else 2
  symmetric := by intro a b; simp [eq_comm]
  irreducible := by
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun a b ↦ if a = b then 0 else 2
    change A.IsIrreducible
    apply (Matrix.isIrreducible_iff_exists_pow_pos (A := A)
      (fun a b ↦ by dsimp [A]; split_ifs <;> norm_num)).mpr
    intro a b
    by_cases h : a = b
    · subst b
      refine ⟨2, by decide, ?_⟩
      rw [pow_two, Matrix.mul_apply]
      fin_cases a <;> norm_num [A, Fin.sum_univ_two]
    · refine ⟨1, by decide, ?_⟩
      rw [pow_one]
      simp [A, h]

theorem bipartite_symmetricMatrix (a b : Fin 2) :
    bipartite.symmetricMatrix a b = if a = b then 0 else 1 := by
  change Real.sqrt (1 / 2) * (if a = b then 0 else 2) * Real.sqrt (1 / 2) = _
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg h]
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith

theorem bipartite_operator_zero (v : bipartite.Hilbert) : bipartite.operator v 0 = v 1 := by
  rw [bipartite.operator_apply]
  simp [bipartite_symmetricMatrix, Fin.sum_univ_two]

theorem bipartite_operator_one (v : bipartite.Hilbert) : bipartite.operator v 1 = v 0 := by
  rw [bipartite.operator_apply]
  simp [bipartite_symmetricMatrix, Fin.sum_univ_two]

theorem bipartite_operator_norm_apply (v : bipartite.Hilbert) : ‖bipartite.operator v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    bipartite_operator_zero, bipartite_operator_one, add_comm]

theorem bipartite_operator_norm : ‖bipartite.operator‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [bipartite_operator_norm_apply]
  · let v : bipartite.Hilbert := WithLp.toLp 2 ![(1 : ℝ), 0]
    have hvne : v ≠ 0 := by
      intro hz
      have h := congrArg (fun v : bipartite.Hilbert ↦ v 0) hz
      change (1 : ℝ) = 0 at h
      norm_num at h
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hb := bipartite.operator.le_opNorm v
    rw [bipartite_operator_norm_apply] at hb
    exact (mul_le_mul_iff_of_pos_right hn).mp (by simpa using hb)

theorem bipartite_critical : bipartite.IsCritical := by
  unfold IsCritical
  rw [← bipartite.spectralRadius_operator,
    ContinuousLinearMap.spectralRadius_eq_nnnorm bipartite.operator
      bipartite.isSymmetric_operator.isSelfAdjoint]
  have hn : ‖bipartite.operator‖₊ = (1 : NNReal) := by
    apply NNReal.eq
    exact bipartite_operator_norm
  rw [hn]
  simp

theorem bipartite_has_negative_unit_eigenvalue :
    Module.End.HasEigenvalue bipartite.operator.toLinearMap (-1) := by
  let v : bipartite.Hilbert := WithLp.toLp 2 ![(1 : ℝ), -1]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    apply (WithLp.ext_iff 2).mpr
    funext a
    fin_cases a <;>
      simp [v, bipartite_operator_zero, bipartite_operator_one]
  · intro hz
    have h := congrArg (fun v : bipartite.Hilbert ↦ v 0) hz
    change (1 : ℝ) = 0 at h
    norm_num at h

end PerronWright.FiniteIrreducibleModel
