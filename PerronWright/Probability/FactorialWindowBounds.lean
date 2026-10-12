import PerronWright.Probability.FactorialDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Compact

/-!
# Bounds for the literal factorial density on a positive size window

The constants below are obtained from continuity of the actual Wright size
factors on a compact interval and the finite set of allowed surpluses.  No
identification of this density with a stochastic-process law is asserted.
-/

open scoped BigOperators Real

noncomputable section

namespace PerronWright.FactorialDensity

theorem sizeFactor_continuousOn_Icc (beta : ℝ) (r : ℕ) {a b : ℝ}
    (ha : 0 < a) : ContinuousOn (fun x ↦ sizeFactor beta x r) (Set.Icc a b) := by
  unfold sizeFactor
  apply continuousOn_const.mul
  exact continuousOn_id.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1)))

/-- A single positive bound for the finitely many actual surplus factors. -/
theorem exists_sizeFactor_window_bound (beta : ℝ) {a b : ℝ} (ha : 0 < a) (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ≤ R, ∀ x ∈ Set.Icc a b, sizeFactor beta x r ≤ C := by
  have hbound : ∀ r : Fin (R + 1), ∃ B : ℝ,
      ∀ x ∈ Set.Icc a b, sizeFactor beta x r ≤ B := by
    intro r
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
      (sizeFactor_continuousOn_Icc beta r ha)
    exact ⟨B, fun x hx ↦ hB ⟨x, hx, rfl⟩⟩
  choose B hB using hbound
  refine ⟨1 + ∑ r, |B r|, by positivity, ?_⟩
  intro r hr x hx
  let j : Fin (R + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  have hj : |B j| ≤ ∑ k, |B k| :=
    Finset.single_le_sum (fun k _ ↦ abs_nonneg (B k)) (Finset.mem_univ j)
  calc
    sizeFactor beta x r ≤ B j := hB j x hx
    _ ≤ |B j| := le_abs_self _
    _ ≤ ∑ k, |B k| := hj
    _ ≤ 1 + ∑ k, |B k| := by linarith

theorem density_le_window_bound {q : ℕ} (alpha lambda : ℝ) {beta a b C : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (_hC : 0 ≤ C) (R : ℕ)
    (hbound : ∀ r ≤ R, ∀ x ∈ Set.Icc a b, sizeFactor beta x r ≤ C)
    (x : Fin q → ℝ) (r : Fin q → ℕ)
    (hx : ∀ i, x i ∈ Set.Icc a b) (hr : ∀ i, r i ≤ R) :
    density alpha beta lambda x r ≤
      C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
  have hxp : ∀ i, 0 < x i := fun i ↦ lt_of_lt_of_le ha (hx i).1
  have hs : a * q ≤ ∑ i, x i := by
    calc
      a * q = ∑ _i : Fin q, a := by simp [mul_comm]
      _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ ↦ (hx i).1)
  have he : Real.exp (-beta * (∑ i, x i) ^ 3 / 24) ≤
      Real.exp (-beta * (a * q) ^ 3 / 24) := by
    apply Real.exp_le_exp.mpr
    have hc : (a * q) ^ 3 ≤ (∑ i, x i) ^ 3 := by
      gcongr
    nlinarith
  have hp : ∏ i, sizeFactor beta (x i) (r i) ≤ C ^ q := by
    calc
      (∏ i, sizeFactor beta (x i) (r i)) ≤ ∏ _i : Fin q, C :=
        Finset.prod_le_prod (fun i _ ↦ (sizeFactor_pos hbeta (hxp i) (r i)).le)
          (fun i _ ↦ hbound (r i) (hr i) (x i) (hx i))
      _ = C ^ q := by simp
  calc
    density alpha beta lambda x r ≤
        Real.exp (-beta * (∑ i, x i) ^ 3 / 24) *
          ∏ i, sizeFactor beta (x i) (r i) := density_le_cubic_bound alpha lambda hbeta x r hxp
    _ ≤ Real.exp (-beta * (a * q) ^ 3 / 24) * C ^ q :=
      mul_le_mul he hp (Finset.prod_nonneg (fun i _ ↦
        (sizeFactor_pos hbeta (hxp i) (r i)).le)) (Real.exp_pos _).le
    _ = C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := mul_comm _ _

/-- The bound is simultaneous in the order and both critical-window parameters. -/
theorem exists_density_window_bound {beta a b : ℝ} (hbeta : 0 < beta)
    (ha : 0 < a) (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ alpha lambda : ℝ,
      ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, x i ∈ Set.Icc a b) → (∀ i, r i ≤ R) →
      density alpha beta lambda x r ≤ C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
  obtain ⟨C, hC, hbound⟩ := exists_sizeFactor_window_bound beta ha R
  exact ⟨C, hC, fun _ alpha lambda x r hx hr ↦
    density_le_window_bound alpha lambda hbeta ha hC.le R hbound x r hx hr⟩

/-- Absolute summability of the exponential factorial-moment majorant at any
fixed generating-function argument. -/
theorem summable_factorial_window_majorant {beta a C : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (hC : 0 ≤ C) (z : ℝ) :
    Summable (fun q : ℕ ↦ |z| ^ q * C ^ q *
      Real.exp (-beta * (a * q) ^ 3 / 24) / (q.factorial : ℝ)) := by
  apply (Real.summable_pow_div_factorial (|z| * C)).of_nonneg_of_le
  · intro q
    positivity
  · intro q
    have he : Real.exp (-beta * (a * q) ^ 3 / 24) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hn : 0 ≤ beta * (a * q) ^ 3 / 24 := by positivity
      linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      |z| ^ q * C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) ≤
          |z| ^ q * C ^ q * 1 := mul_le_mul_of_nonneg_left he (by positivity)
      _ = (|z| * C) ^ q := by rw [mul_one, mul_pow]

/-- Cubic decay dominates any fixed exponential growth, even without a
factorial denominator. -/
theorem summable_pow_mul_exp_neg_cubic {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Summable (fun q : ℕ ↦ A ^ q * Real.exp (-c * (q : ℝ) ^ 3)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((A + 1) / c)
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨max N 1, fun q hq ↦ hq⟩] with q hq
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (le_trans (le_max_right N 1) hq)
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast (le_trans (le_max_left N 1) hq)
  have hcq : A + 1 ≤ c * q := by
    have hdiv : (A + 1) / c ≤ q := hN.le.trans hNq
    have := (div_le_iff₀ hc).mp hdiv
    linarith
  have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have h1 : (A + 1) * (q : ℝ) ^ 2 ≤ c * q * (q : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hcq (sq_nonneg _)
  have h2 : (A + 1) * q ≤ (A + 1) * (q : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hq2 (by linarith)
  have he : A * q - c * (q : ℝ) ^ 3 ≤ -(q : ℝ) := by nlinarith
  have hAe : A ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    A ^ q * Real.exp (-c * (q : ℝ) ^ 3) ≤
        (Real.exp A) ^ q * Real.exp (-c * (q : ℝ) ^ 3) := by
      gcongr
    _ = Real.exp (A * q - c * (q : ℝ) ^ 3) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(q : ℝ)) := Real.exp_le_exp.mpr he

/-- All fixed exponential weights of the actual window majorant are summable. -/
theorem summable_window_majorant {beta a C : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hC : 0 ≤ C) (z : ℝ) :
    Summable (fun q : ℕ ↦ |z| ^ q * C ^ q *
      Real.exp (-beta * (a * q) ^ 3 / 24)) := by
  have hs := summable_pow_mul_exp_neg_cubic
    (A := |z| * C) (c := beta * a ^ 3 / 24) (by positivity) (by positivity)
  convert hs using 1
  ext q
  rw [mul_pow]
  congr 2 <;> ring

end PerronWright.FactorialDensity
