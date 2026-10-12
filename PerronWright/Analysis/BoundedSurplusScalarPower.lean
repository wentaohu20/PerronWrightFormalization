import PerronWright.Analysis.ScalarFieldBridge
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# A uniform scalar-field power bound over bounded surplus

The scalar-field bridge contributes the elementary factor `t^(r-1)`.
For a fixed upper surplus bound, this file obtains one local Lipschitz
constant simultaneously for every permitted integer exponent.  The proof
uses differentiability at `t = 1` and a finite sum of Big-O bounds.
-/

open Filter Topology Asymptotics
open scoped BigOperators

noncomputable section

namespace PerronWright.BoundedSurplusScalarPower

/-- The residual scalar factor occurring in the physical/field bridge. -/
def scalarSurplusPower (r : ℕ) (t : ℝ) : ℝ :=
  t ^ ((r : ℤ) - 1)

@[simp] theorem scalarSurplusPower_one (r : ℕ) :
    scalarSurplusPower r 1 = 1 := by
  simp [scalarSurplusPower]

private theorem scalarSurplusPower_sub_one_isBigO (r : ℕ) :
    (fun t : ℝ ↦ ‖scalarSurplusPower r t - 1‖) =O[nhds 1]
      (fun t : ℝ ↦ ‖t - 1‖) := by
  have hd : DifferentiableAt ℝ
      (fun t : ℝ ↦ t ^ ((r : ℤ) - 1)) 1 :=
    differentiableAt_zpow.mpr (Or.inl one_ne_zero)
  have hO := hd.isBigO_sub.norm_norm
  simpa only [scalarSurplusPower, one_zpow, Real.norm_eq_abs] using hO

/-- For every fixed surplus cutoff, one constant controls the scalar bridge
factor uniformly over all `r ≤ R` near `t = 1`. -/
theorem exists_scalarSurplusPower_uniform_local_bound (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in nhds 1,
      ∀ r : ℕ, r ≤ R →
        |scalarSurplusPower r t - 1| ≤ C * |t - 1| := by
  let s : Finset ℕ := Finset.range (R + 1)
  have hsum :
      (fun t : ℝ ↦ ∑ r ∈ s, ‖scalarSurplusPower r t - 1‖) =O[nhds 1]
        (fun t : ℝ ↦ ‖t - 1‖) := by
    have hfun :
        (∑ r ∈ s, fun t : ℝ ↦ ‖scalarSurplusPower r t - 1‖) =
          (fun t : ℝ ↦ ∑ r ∈ s, ‖scalarSurplusPower r t - 1‖) := by
      funext t
      exact Finset.sum_apply t s _
    rw [← hfun]
    exact IsBigO.sum (s := s)
      (fun r _ ↦ scalarSurplusPower_sub_one_isBigO r)
  rw [isBigO_iff] at hsum
  obtain ⟨C0, hC0⟩ := hsum
  let C : ℝ := max C0 1
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hC0] with t ht
  intro r hr
  have hrs : r ∈ s := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
  have hterm :
      ‖scalarSurplusPower r t - 1‖ ≤
        ∑ j ∈ s, ‖scalarSurplusPower j t - 1‖ := by
    exact Finset.single_le_sum
      (fun j _ ↦ norm_nonneg (scalarSurplusPower j t - 1)) hrs
  have hsumNonneg :
      0 ≤ ∑ j ∈ s, ‖scalarSurplusPower j t - 1‖ :=
    Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have ht' :
      (∑ j ∈ s, ‖scalarSurplusPower j t - 1‖) ≤
        C0 * |t - 1| := by
    have htNorm :
        |∑ j ∈ s, ‖scalarSurplusPower j t - 1‖| ≤
          C0 * |t - 1| := by
      simpa only [Real.norm_eq_abs, abs_abs] using ht
    calc
      (∑ j ∈ s, ‖scalarSurplusPower j t - 1‖) =
          |∑ j ∈ s, ‖scalarSurplusPower j t - 1‖| :=
        (abs_of_nonneg hsumNonneg).symm
      _ ≤ C0 * |t - 1| := htNorm
  calc
    |scalarSurplusPower r t - 1| =
        ‖scalarSurplusPower r t - 1‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑ j ∈ s, ‖scalarSurplusPower j t - 1‖ := hterm
    _ ≤ C0 * |t - 1| := ht'
    _ ≤ C * |t - 1| := by
      exact mul_le_mul_of_nonneg_right (le_max_left C0 1) (abs_nonneg _)

end PerronWright.BoundedSurplusScalarPower
