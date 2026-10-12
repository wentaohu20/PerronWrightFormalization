import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

/-!
# Finite analytic amplitudes and the extra-X gain

This module contains only the analytic algebra needed after a fixed-surplus
kernel contribution has already been written as `X ^ (-e)` times an analytic
amplitude.  It does not assert that such an amplitude exists for graph
kernels, and it contains no coefficient-transfer or asymptotic statement.
-/

open scoped Topology

namespace PerronWright.AnalyticFiniteAmplitude

variable {ι E A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedCommRing A] [NormedAlgebra ℂ A]

/-- A finite product of analytic factors is analytic.  This is kept as a
small named wrapper for the later finite-kernel assembly. -/
theorem finite_product_analyticAt
    (s : Finset ι) (f : ι → E → A) (x : E)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun y => ∏ i ∈ s, f i y) x :=
  s.analyticAt_fun_prod hf

/-- Multiplying a scalar analytic amplitude by a nonnegative power of the
local coordinate preserves analyticity. -/
theorem pow_mul_analyticAt_zero
    (d : ℕ) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun X => X ^ d * F X) 0 :=
  (analyticAt_id.pow d).mul hF

/-- The elementary arithmetic behind the noncubic gain: if a kernel has
strictly fewer than the cubic edge count `3 * ell`, then normalization by
the cubic pole order leaves at least one nonnegative power of `X`.  The
strict inequality avoids any ambiguity from truncated subtraction in `ℕ`. -/
theorem one_le_cubicDefect
    {ell e : ℕ} (he : e < 3 * ell) :
    1 ≤ 3 * ell - e := by
  omega

/-- A noncubic contribution normalized to the cubic pole order vanishes at
the critical point.  This conclusion uses only the edge-count inequality
and analyticity of the supplied amplitude. -/
theorem noncubic_normalizedAmplitude_analytic_zero
    {ell e : ℕ} (he : e < 3 * ell)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun X => X ^ (3 * ell - e) * F X) 0 ∧
      (0 : ℂ) ^ (3 * ell - e) * F 0 = 0 := by
  constructor
  · exact pow_mul_analyticAt_zero (3 * ell - e) F hF
  · have hpos : 0 < 3 * ell - e := one_le_cubicDefect he
    simp [Nat.ne_of_gt hpos]

/-- Strong form of the one-extra-`X` improvement.  The remaining factor is
again analytic, and the factorization is an identity for every `X`, not only
a germ equality. -/
theorem noncubic_normalizedAmplitude_eq_X_mul
    {ell e : ℕ} (he : e < 3 * ell)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧
      ∀ X, X ^ (3 * ell - e) * F X = X * R X := by
  let d := 3 * ell - e
  have hd : 0 < d := one_le_cubicDefect he
  let R : ℂ → ℂ := fun X => X ^ (d - 1) * F X
  refine ⟨R, (analyticAt_id.pow (d - 1)).mul hF, ?_⟩
  intro X
  have hsucc : d - 1 + 1 = d := by omega
  change X ^ d * F X = X * (X ^ (d - 1) * F X)
  have hpow : X ^ d = X ^ (d - 1) * X := by
    conv_lhs => rw [← hsucc, pow_succ]
  calc
    X ^ d * F X = (X ^ (d - 1) * X) * F X :=
      congrArg (fun z : ℂ => z * F X) hpow
    _ = X * (X ^ (d - 1) * F X) := by ring

/-- Direct finite-product version used when the analytic amplitude has
already been assembled from finitely many vertex, edge, and correction
factors. -/
theorem noncubic_finiteProduct_eq_X_mul
    {ell e : ℕ} (he : e < 3 * ell)
    (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧
      ∀ X,
        X ^ (3 * ell - e) * (∏ i ∈ s, f i X) = X * R X := by
  exact noncubic_normalizedAmplitude_eq_X_mul he
    (fun X => ∏ i ∈ s, f i X)
    (finite_product_analyticAt s f 0 hf)

end PerronWright.AnalyticFiniteAmplitude
