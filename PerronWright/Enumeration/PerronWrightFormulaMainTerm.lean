import PerronWright.Enumeration.LowSurplusPerronWrightFormula
import PerronWright.Enumeration.PositiveSurplusCubicConstantPositivity

/-!
# Main term in the notation of the bounded-surplus theorem

The three already constructed constants (tree, unicyclic, and the finite
cubic-kernel sum) are assembled here into the paper's single family `w_r`.
This file only normalizes notation and proves exact identities; it contains
no asymptotic assertion.
-/

open Filter Topology PerronWright
open scoped Real

noncomputable section

namespace PerronWright.PerronWrightFormulaMainTerm

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Wright's constants indexed by surplus.  For `r ≥ 2`, the cubic-kernel
excess is `ell = r - 1`. -/
def wrightConstant : ℕ → ℝ
  | 0 => 1
  | 1 => UnicyclicPerronWrightFormula.unicyclicWrightConstant
  | ell + 2 => GraphCore.positiveSurplusWrightConstantReal (ell + 1)

@[simp] theorem wrightConstant_zero : wrightConstant 0 = 1 := rfl

@[simp] theorem wrightConstant_one :
    wrightConstant 1 =
      UnicyclicPerronWrightFormula.unicyclicWrightConstant := rfl

@[simp] theorem wrightConstant_succ_succ (ell : ℕ) :
    wrightConstant (ell + 2) =
      GraphCore.positiveSurplusWrightConstantReal (ell + 1) := by
  rfl

/-- Every Wright constant in the unified family is strictly positive. -/
theorem wrightConstant_pos (r : ℕ) : 0 < wrightConstant r := by
  cases r with
  | zero => simp
  | succ r =>
      cases r with
      | zero =>
          unfold wrightConstant
            UnicyclicPerronWrightFormula.unicyclicWrightConstant
          positivity
      | succ ell =>
          simpa [wrightConstant, Nat.succ_eq_add_one] using
            GraphCore.positiveSurplusWrightConstantReal_pos
              (ell + 1) (Nat.succ_pos ell)

/-- The literal radius-dependent main term
`w_r beta^((r-1)/2) rho(t)^(-k) e^(-k) k^(k+3r/2-2)` from the paper. -/
def perronWrightRadiusMainTerm (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (k r : ℕ) (t : ℝ) : ℝ :=
  wrightConstant r *
    (M.beta hM) ^ (((r : ℝ) - 1) / 2) *
    (TreePerronWrightFormula.physicalTreeRadius M hM t)⁻¹ ^ k *
    Real.exp (-(k : ℝ)) *
    (k : ℝ) ^ ((k : ℝ) + 3 * (r : ℝ) / 2 - 2)

/-- At surplus zero the unified main term is exactly the previously proved
tree radius main term. -/
theorem perronWrightRadiusMainTerm_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    perronWrightRadiusMainTerm M hM k 0 t =
      TreePerronWrightFormula.physicalTreeRadiusMainTerm M hM k t := by
  have hbetaExp :
      ((((0 : ℕ) : ℝ) - 1) / 2) = -(1 / 2 : ℝ) := by norm_num
  have hkExp :
      (k : ℝ) + 3 * ((0 : ℕ) : ℝ) / 2 - 2 =
        (k : ℝ) - 2 := by norm_num
  rw [TreePerronWrightFormula.physicalTreeRadiusMainTerm_eq_exp_rpow
    M hM hk t]
  unfold perronWrightRadiusMainTerm
  rw [hbetaExp, hkExp]
  simp only [wrightConstant_zero, one_mul]

/-- At surplus one the unified main term is exactly the previously proved
unicyclic radius main term. -/
theorem perronWrightRadiusMainTerm_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    perronWrightRadiusMainTerm M hM k 1 t =
      UnicyclicPerronWrightFormula.physicalUnicyclicRadiusMainTerm M hM k t := by
  have hbetaExp :
      ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  have hkExp :
      (k : ℝ) + 3 * ((1 : ℕ) : ℝ) / 2 - 2 =
        (k : ℝ) - 1 / 2 := by
    norm_num
    ring
  rw [UnicyclicPerronWrightFormula.physicalUnicyclicRadiusMainTerm_eq_exp_rpow
    M hM hk t]
  unfold perronWrightRadiusMainTerm
  rw [hbetaExp, hkExp]
  simp only [wrightConstant_one, Real.rpow_zero, mul_one]

/-- On the complete range `r ≤ 1`, the unified paper main term agrees with
the low-surplus packaging used to combine the two existing proofs. -/
theorem perronWrightRadiusMainTerm_eq_lowSurplus
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k r : ℕ} (hk : 0 < k) (hr : r ≤ 1) (t : ℝ) :
    perronWrightRadiusMainTerm M hM k r t =
      LowSurplusPerronWrightFormula.lowSurplusRadiusMainTerm
        M hM k r t := by
  have hrCases : r = 0 ∨ r = 1 := by omega
  rcases hrCases with rfl | rfl
  · exact perronWrightRadiusMainTerm_zero M hM hk t
  · exact perronWrightRadiusMainTerm_one M hM hk t

/-- The bounded-surplus Perron--Wright theorem in the unified notation is
already complete for the simultaneous range `0 ≤ r ≤ 1`, on every
nonnegative shrinking window. -/
theorem exists_lowSurplus_unified_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) →
      Filter.Tendsto eta Filter.atTop (nhds 0) →
      ∀ᶠ k : ℕ in Filter.atTop,
      ∀ r : ℕ, r ≤ 1 → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    LowSurplusPerronWrightFormula.exists_lowSurplusPerronWright_radius_relative_bound_uniform_eta
      M hM
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hboundWindow := hbound eta hetaNonneg heta
  filter_upwards [hboundWindow, Filter.eventually_ge_atTop (1 : ℕ)]
    with k hk hkOne
  intro r hr t ht
  have hkPos : 0 < k := Nat.zero_lt_one.trans_le hkOne
  rw [perronWrightRadiusMainTerm_eq_lowSurplus M hM hkPos hr t]
  exact hk r hr t ht

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_lowSurplus_unified_radius_relative_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in Filter.atTop,
      ∀ r : ℕ, r ≤ 1 → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_lowSurplus_unified_radius_relative_bound_uniform_eta M hM
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

/-- For positive excess `ell`, the unified main term exposes exactly the
real cubic-kernel Wright constant and the factor `beta^(ell/2)`. -/
theorem perronWrightRadiusMainTerm_positive
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) (k : ℕ) (t : ℝ) :
    perronWrightRadiusMainTerm M hM k (ell + 1) t =
      GraphCore.positiveSurplusWrightConstantReal ell *
        (M.beta hM) ^ ((ell : ℝ) / 2) *
        (TreePerronWrightFormula.physicalTreeRadius M hM t)⁻¹ ^ k *
        Real.exp (-(k : ℝ)) *
        (k : ℝ) ^ ((k : ℝ) + 3 * (ell : ℝ) / 2 - 1 / 2) := by
  cases ell with
  | zero => omega
  | succ m =>
      have hbetaExp :
          (((((m + 1 + 1 : ℕ) : ℝ) - 1) / 2)) =
            ((m + 1 : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      have hkExp :
          (k : ℝ) + 3 * ((m + 1 + 1 : ℕ) : ℝ) / 2 - 2 =
            (k : ℝ) + 3 * ((m + 1 : ℕ) : ℝ) / 2 - 1 / 2 := by
        push_cast
        ring
      unfold perronWrightRadiusMainTerm
      rw [hbetaExp, hkExp]
      simp only [wrightConstant_succ_succ]

end PerronWright.PerronWrightFormulaMainTerm
