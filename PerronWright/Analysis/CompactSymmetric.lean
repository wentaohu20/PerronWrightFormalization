import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Endpoint eigenvalues of compact symmetric operators

This file extracts the precise spectral fact needed from `(B1)`.  It is
proved directly from mathlib's Rayleigh-quotient and compact-spectrum API;
no Perron--Frobenius or spectral endpoint is introduced as an assumption.
-/

open Module

noncomputable section

namespace PerronWright

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- For a symmetric operator on a nontrivial real Hilbert space, at least
one of the two norm endpoints belongs to the spectrum. -/
theorem norm_or_neg_norm_mem_spectrum (T : E →L[ℝ] E)
    [Nontrivial E] (hT : T.IsSymmetric) :
    ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
  simp_rw [spectrum, Set.mem_compl_iff]
  by_contra! h
  obtain ⟨c, hc0, hc⟩ :=
    T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
  grind [ciSup_le hc, ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]

/-- A compact symmetric operator of norm one has eigenvalue `1` or `-1`.
The degenerate Hilbert space is ruled out internally by the norm hypothesis. -/
theorem eigenvalue_one_or_neg_one (T : E →L[ℝ] E)
    (hcompact : IsCompactOperator T) (hsymm : T.IsSymmetric)
    (hnorm : ‖T‖ = 1) :
    Module.End.HasEigenvalue T.toLinearMap 1 ∨
      Module.End.HasEigenvalue T.toLinearMap (-1) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
      let _ := h
      have hz : T = 0 := Subsingleton.elim _ _
      simp [hz] at hnorm
  | inr h =>
      let _ := h
      have h := norm_or_neg_norm_mem_spectrum T hsymm
      rw [hnorm] at h
      exact h.imp ((hcompact.hasEigenvalue_iff_mem_spectrum one_ne_zero).mpr)
        ((hcompact.hasEigenvalue_iff_mem_spectrum
          (by norm_num : (-1 : ℝ) ≠ 0)).mpr)

omit [CompleteSpace E] in
/-- A vector attaining the norm-one upper Rayleigh bound is fixed. -/
theorem fixed_of_inner_ge (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (v : E)
    (hinner : ‖v‖ ^ 2 ≤ inner ℝ (T v) v) : T v = v := by
  have hn : ‖T v‖ ≤ ‖v‖ := calc
    ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = ‖v‖ := one_mul _
  have hs := norm_sub_sq_real (T v) v
  have hn2 : ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have hz : ‖T v - v‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖T v - v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

omit [CompleteSpace E] in
/-- Symmetry rules out a Jordan chain of length two at the zero
eigenvalue. -/
theorem no_second_order_kernel (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    (v : E) (hv : T (T v) = 0) : T v = 0 := by
  have hi := hT v (T v)
  change inner ℝ (T v) (T v) = inner ℝ v (T (T v)) at hi
  rw [hv, inner_zero_right] at hi
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hi

end PerronWright
