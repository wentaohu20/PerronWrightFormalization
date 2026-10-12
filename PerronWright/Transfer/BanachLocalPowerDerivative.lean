import Mathlib.Analysis.Complex.Liouville

/-!
Local Cauchy estimates for Banach-valued power-bounded remainders.
The disc hypotheses must later be verified geometrically from the actual
Δ-domain; this lemma does not assume or prove the global coefficient
transfer theorem.
-/

open Complex Metric
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- A local power bound on the boundary of a holomorphic disc yields
an explicit bound for every derivative at its center. -/
theorem banach_iteratedDeriv_le_local_power
    {F : ℂ → E} {z : ℂ} {r C a : ℝ} (j : ℕ)
    (hr : 0 < r) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hF : DiffContOnCl ℂ F (ball z r))
    (hpow : ∀ ζ ∈ sphere z r,
      ‖F ζ‖ ≤ C * ‖(1 : ℂ) - ζ‖ ^ a) :
    ‖iteratedDeriv j F z‖ ≤
      j.factorial * (C * (‖(1 : ℂ) - z‖ + r) ^ a) /
        r ^ j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j hr hF
  intro ζ hζ
  have hdist : ‖(1 : ℂ) - ζ‖ ≤ ‖(1 : ℂ) - z‖ + r := by
    calc
      ‖(1 : ℂ) - ζ‖ = ‖((1 : ℂ) - z) + (z - ζ)‖ := by
        congr 1
        ring
      _ ≤ ‖(1 : ℂ) - z‖ + ‖z - ζ‖ := norm_add_le _ _
      _ = ‖(1 : ℂ) - z‖ + r := by
        have hzr : ‖z - ζ‖ = r := by
          rw [norm_sub_rev z ζ]
          simpa only [mem_sphere_iff_norm] using hζ
        rw [hzr]
  exact (hpow ζ hζ).trans <|
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hdist ha) hC

end PerronWright.Transfer
