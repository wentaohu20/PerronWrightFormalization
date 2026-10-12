import PerronWright.Enumeration.PerronWrightFormulaMainTerm

/-!
# The compact-type limiting factorial density

The polynomial and each surplus-dependent coefficient are the literal
expressions in the probability theorem.  The square-completion and cubic
bound are proved algebraically; this file does not assume that a graph
process converges to a process possessing these densities.
-/

open scoped BigOperators Real

noncomputable section

namespace PerronWright.FactorialDensity

/-- The critical finite-population exponent. -/
def criticalExponent (alpha beta lambda size : ℝ) : ℝ :=
  beta * size ^ 3 / 6 - alpha * lambda * size ^ 2 / 2 +
    alpha ^ 2 * lambda ^ 2 * size / (2 * beta)

/-- The fixed-surplus size factor in the limiting factorial density. -/
def sizeFactor (beta x : ℝ) (r : ℕ) : ℝ :=
  PerronWrightFormulaMainTerm.wrightConstant r * beta ^ (((r : ℝ) - 1) / 2) /
    Real.sqrt (2 * Real.pi) * x ^ (3 * (r : ℝ) / 2 - 5 / 2)

/-- The literal ordered `q`-point size-and-surplus factorial density. -/
def density {q : ℕ} (alpha beta lambda : ℝ) (x : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  Real.exp (-criticalExponent alpha beta lambda (∑ i, x i)) *
    ∏ i, sizeFactor beta (x i) (r i)

theorem sizeFactor_pos {beta x : ℝ} (hbeta : 0 < beta) (hx : 0 < x) (r : ℕ) :
    0 < sizeFactor beta x r := by
  have hw := PerronWrightFormulaMainTerm.wrightConstant_pos r
  have hp := Real.pi_pos
  unfold sizeFactor
  positivity

theorem density_pos {q : ℕ} (alpha lambda : ℝ) {beta : ℝ} (hbeta : 0 < beta)
    (x : Fin q → ℝ) (r : Fin q → ℕ) (hx : ∀ i, 0 < x i) :
    0 < density alpha beta lambda x r := by
  unfold density
  apply mul_pos (Real.exp_pos _)
  exact Finset.prod_pos (fun i _ ↦ sizeFactor_pos hbeta (hx i) (r i))

/-- The exponent is a positive square plus a cubic coercive term. -/
theorem criticalExponent_complete_square (alpha lambda size : ℝ)
    {beta : ℝ} (hbeta : beta ≠ 0) :
    criticalExponent alpha beta lambda size =
      beta * size ^ 3 / 24 + size / (2 * beta) *
        (alpha * lambda - beta * size / 2) ^ 2 := by
  unfold criticalExponent
  field_simp
  ring

theorem criticalExponent_cubic_lower (alpha lambda : ℝ)
    {beta size : ℝ} (hbeta : 0 < beta) (hsize : 0 ≤ size) :
    beta * size ^ 3 / 24 ≤ criticalExponent alpha beta lambda size := by
  rw [criticalExponent_complete_square alpha lambda size hbeta.ne']
  exact le_add_of_nonneg_right (by positivity)

/-- The density's cubic decay is uniform in the critical-window parameter. -/
theorem density_le_cubic_bound {q : ℕ} (alpha lambda : ℝ)
    {beta : ℝ} (hbeta : 0 < beta) (x : Fin q → ℝ) (r : Fin q → ℕ)
    (hx : ∀ i, 0 < x i) :
    density alpha beta lambda x r ≤
      Real.exp (-beta * (∑ i, x i) ^ 3 / 24) *
        ∏ i, sizeFactor beta (x i) (r i) := by
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ ↦ (hx i).le)
  have he := criticalExponent_cubic_lower alpha lambda hbeta hs
  unfold density
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    linarith
  · exact (Finset.prod_pos (fun i _ ↦ sizeFactor_pos hbeta (hx i) (r i))).le

/-- The exponent becomes the homogeneous Aldous exponent under the
size scale `c` and critical-window parameter `alpha*lambda/c^2`. -/
theorem criticalExponent_rescaling (alpha lambda size : ℝ) {c : ℝ} (hc : c ≠ 0) :
    criticalExponent alpha (c ^ 3) lambda size =
      criticalExponent 1 1 (alpha * lambda / c ^ 2) (c * size) := by
  unfold criticalExponent
  field_simp

end PerronWright.FactorialDensity
