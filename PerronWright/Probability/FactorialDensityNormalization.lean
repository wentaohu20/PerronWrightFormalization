import PerronWright.Probability.FactorialDensity

/-!
# Exact starred-coordinate normalization of the factorial density

Both the polynomial exponent and the surplus-dependent size factors are
transformed, including the `q`-dimensional Jacobian.  This is the literal
algebraic normalization used for Aldous identification, not an assertion
of the Brownian density formula or of process convergence.
-/

open scoped BigOperators Real

noncomputable section

namespace PerronWright.FactorialDensity

theorem sizeFactor_rescaling {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (r : ℕ) :
    sizeFactor (c ^ 3) x r = c * sizeFactor 1 (c * x) r := by
  have hp : (c ^ 3) ^ (((r : ℝ) - 1) / 2) =
      c * c ^ (3 * (r : ℝ) / 2 - 5 / 2) := by
    rw [← Real.rpow_natCast_mul hc.le 3]
    norm_num only [Nat.cast_ofNat]
    have he : (3 : ℝ) * (((r : ℝ) - 1) / 2) = 1 + (3 * (r : ℝ) / 2 - 5 / 2) := by ring
    rw [he, Real.rpow_add hc, Real.rpow_one]
  unfold sizeFactor
  rw [hp, Real.one_rpow, Real.mul_rpow hc.le hx.le]
  ring

theorem density_rescaling {q : ℕ} (alpha lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (x : Fin q → ℝ) (r : Fin q → ℕ) (hx : ∀ i, 0 < x i) :
    density alpha (c ^ 3) lambda x r =
      c ^ q * density 1 1 (alpha * lambda / c ^ 2) (fun i ↦ c * x i) r := by
  unfold density
  rw [criticalExponent_rescaling alpha lambda (∑ i, x i) hc.ne', Finset.mul_sum]
  simp_rw [sizeFactor_rescaling hc (hx _) (r _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- The inverse Jacobian cancels the complete size-factor amplitude. -/
theorem density_rescaling_with_jacobian {q : ℕ} (alpha lambda : ℝ) {c : ℝ}
    (hc : 0 < c) (x : Fin q → ℝ) (r : Fin q → ℕ) (hx : ∀ i, 0 < x i) :
    c⁻¹ ^ q * density alpha (c ^ 3) lambda x r =
      density 1 1 (alpha * lambda / c ^ 2) (fun i ↦ c * x i) r := by
  rw [density_rescaling alpha lambda hc x r hx, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hc.ne', one_pow, one_mul]

theorem beta_cubeRoot_cube {beta : ℝ} (hbeta : 0 < beta) :
    (beta ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = beta := by
  rw [← Real.rpow_mul_natCast hbeta.le]
  norm_num

theorem beta_cubeRoot_square {beta : ℝ} (hbeta : 0 < beta) :
    (beta ^ (1 / 3 : ℝ)) ^ (2 : ℕ) = beta ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast hbeta.le]
  congr 1
  ring

/-- Exact density and Jacobian in the paper's starred size coordinates
and its stated Aldous parameter `alpha * beta^(-2/3) * lambda`. -/
theorem density_starred_normalization {q : ℕ} (alpha lambda : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (x : Fin q → ℝ) (r : Fin q → ℕ) (hx : ∀ i, 0 < x i) :
    (beta ^ (1 / 3 : ℝ))⁻¹ ^ q * density alpha beta lambda x r =
      density 1 1 (alpha * beta ^ (-2 / 3 : ℝ) * lambda)
        (fun i ↦ beta ^ (1 / 3 : ℝ) * x i) r := by
  have hc : 0 < beta ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hbeta _
  have hl : alpha * lambda / (beta ^ (1 / 3 : ℝ)) ^ (2 : ℕ) =
      alpha * beta ^ (-2 / 3 : ℝ) * lambda := by
    rw [beta_cubeRoot_square hbeta]
    have he : (-2 / 3 : ℝ) = -(2 / 3 : ℝ) := by ring
    rw [he, Real.rpow_neg hbeta.le, div_eq_mul_inv]
    ring
  simpa only [beta_cubeRoot_cube hbeta, hl] using
    density_rescaling_with_jacobian alpha lambda hc x r hx

end PerronWright.FactorialDensity
