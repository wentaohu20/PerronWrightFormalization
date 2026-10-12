import PerronWright.Probability.FactorialWindowBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The integrated mass of the literal density on a bounded window

These integrals and finite surplus sums use the literal formula.  Their
cubic bounds and generating-series summability do not assume that these
integrals are factorial moments of an already constructed process.
-/

open scoped BigOperators Real
open MeasureTheory

noncomputable section

namespace PerronWright.FactorialDensity

def sizeWindow (q : ℕ) (a b : ℝ) : Set (Fin q → ℝ) :=
  Set.Icc (fun _ ↦ a) (fun _ ↦ b)

theorem mem_sizeWindow {q : ℕ} {a b : ℝ} {x : Fin q → ℝ} :
    x ∈ sizeWindow q a b ↔ ∀ i, x i ∈ Set.Icc a b := by
  simp only [sizeWindow, Set.mem_Icc, Pi.le_def]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

theorem density_continuousOn_sizeWindow {q : ℕ} (alpha beta lambda : ℝ)
    (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x ↦ density alpha beta lambda x r) (sizeWindow q a b) := by
  have he : Continuous (fun x : Fin q → ℝ ↦
      Real.exp (-criticalExponent alpha beta lambda (∑ i, x i))) := by
    unfold criticalExponent
    fun_prop
  unfold density
  apply he.continuousOn.mul
  apply continuousOn_finsetProd
  intro i _
  exact (sizeFactor_continuousOn_Icc beta (r i) ha).comp'
    (continuous_apply i).continuousOn (fun x hx ↦ (mem_sizeWindow.mp hx) i)

theorem density_integrableOn_sizeWindow {q : ℕ} (alpha beta lambda : ℝ)
    (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x ↦ density alpha beta lambda x r) (sizeWindow q a b) volume :=
  (density_continuousOn_sizeWindow alpha beta lambda r ha).integrableOn_compact isCompact_Icc

theorem sizeWindow_volume_toReal (q : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (volume (sizeWindow q a b)).toReal = (b - a) ^ q := by
  simpa [sizeWindow] using
    (Real.volume_Icc_pi_toReal (a := fun _ : Fin q ↦ a) (b := fun _ ↦ b) (fun _ ↦ hab))

def fixedSurplusWindowMass {q : ℕ} (alpha beta lambda a b : ℝ) (r : Fin q → ℕ) : ℝ :=
  ∫ x in sizeWindow q a b, density alpha beta lambda x r

theorem fixedSurplusWindowMass_nonneg {q : ℕ} (alpha lambda a b : ℝ)
    {beta : ℝ} (hbeta : 0 < beta) (ha : 0 < a) (r : Fin q → ℕ) :
    0 ≤ fixedSurplusWindowMass alpha beta lambda a b r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (s := sizeWindow q a b) measurableSet_Icc] with x hx
  exact (density_pos alpha lambda hbeta x r
    (fun i ↦ lt_of_lt_of_le ha ((mem_sizeWindow.mp hx) i).1)).le

theorem fixedSurplusWindowMass_le {q : ℕ} (alpha lambda : ℝ) {beta a b C : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C) (R : ℕ)
    (hbound : ∀ r ≤ R, ∀ x ∈ Set.Icc a b, sizeFactor beta x r ≤ C)
    (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R) :
    fixedSurplusWindowMass alpha beta lambda a b r ≤
      ((b - a) * C) ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
  have hnorm : ∀ x ∈ sizeWindow q a b, ‖density alpha beta lambda x r‖ ≤
      C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
    intro x hx
    have hx' := mem_sizeWindow.mp hx
    rw [Real.norm_of_nonneg (density_pos alpha lambda hbeta x r
      (fun i ↦ lt_of_lt_of_le ha (hx' i).1)).le]
    exact density_le_window_bound alpha lambda hbeta ha hC R hbound x r hx' hr
  have hi := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := sizeWindow q a b) isCompact_Icc.measure_lt_top hnorm
  calc
    fixedSurplusWindowMass alpha beta lambda a b r ≤
        ‖fixedSurplusWindowMass alpha beta lambda a b r‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (fixedSurplusWindowMass alpha beta lambda a b r))
    _ ≤ (C ^ q * Real.exp (-beta * (a * q) ^ 3 / 24)) *
        (volume (sizeWindow q a b)).toReal := hi
    _ = ((b - a) * C) ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
      rw [sizeWindow_volume_toReal q hab]
      simp only [mul_pow]
      ring

/-- Lebesgue integration in every size coordinate and counting summation over
every allowed surplus coordinate. -/
def windowMass (q : ℕ) (alpha beta lambda a b : ℝ) (R : ℕ) : ℝ :=
  ∑ r : Fin q → Fin (R + 1),
    fixedSurplusWindowMass alpha beta lambda a b (fun i ↦ (r i : ℕ))

theorem windowMass_nonneg (q : ℕ) (alpha lambda a b : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (R : ℕ) :
    0 ≤ windowMass q alpha beta lambda a b R := by
  exact Finset.sum_nonneg (fun r _ ↦ fixedSurplusWindowMass_nonneg alpha lambda a b hbeta ha _)

theorem windowMass_le (q : ℕ) (alpha lambda : ℝ) {beta a b C : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C) (R : ℕ)
    (hbound : ∀ r ≤ R, ∀ x ∈ Set.Icc a b, sizeFactor beta x r ≤ C) :
    windowMass q alpha beta lambda a b R ≤
      ((R + 1 : ℝ) * (b - a) * C) ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
  unfold windowMass
  calc
    (∑ r : Fin q → Fin (R + 1),
        fixedSurplusWindowMass alpha beta lambda a b (fun i ↦ (r i : ℕ))) ≤
        ∑ _r : Fin q → Fin (R + 1),
          ((b - a) * C) ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
      apply Finset.sum_le_sum
      intro r _
      exact fixedSurplusWindowMass_le alpha lambda hbeta ha hab hC R hbound _
        (fun i ↦ Nat.le_of_lt_succ (r i).isLt)
    _ = ((R + 1 : ℝ) * (b - a) * C) ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      simp only [mul_pow]
      ring

/-- The integrated estimate has one constant for all orders and all critical
parameters; it includes both the box volume and all surplus assignments. -/
theorem exists_windowMass_bound {beta a b : ℝ} (hbeta : 0 < beta)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, ∀ alpha lambda : ℝ,
      0 ≤ windowMass q alpha beta lambda a b R ∧
      windowMass q alpha beta lambda a b R ≤
        D ^ q * Real.exp (-beta * (a * q) ^ 3 / 24) := by
  obtain ⟨C, hC, hbound⟩ := exists_sizeFactor_window_bound beta ha R
  refine ⟨(R + 1 : ℝ) * (b - a) * C, by positivity, ?_⟩
  intro q alpha lambda
  exact ⟨windowMass_nonneg q alpha lambda a b hbeta ha R,
    windowMass_le q alpha lambda hbeta ha hab hC.le R hbound⟩

/-- The actual integrated density masses have absolutely convergent weighted
series at every real argument, even without factorial denominators. -/
theorem summable_windowMass_weighted (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (z : ℝ) :
    Summable (fun q : ℕ ↦ z ^ q * windowMass q alpha beta lambda a b R) := by
  obtain ⟨D, hD, hbound⟩ := exists_windowMass_bound hbeta ha hab R
  apply (summable_window_majorant hbeta ha hD z).of_norm_bounded
  intro q
  obtain ⟨hm0, hm⟩ := hbound q alpha lambda
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg hm0]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (pow_nonneg (abs_nonneg z) q)

/-- In particular, the factorial-moment generating series is absolutely
convergent for the literal window masses at every real argument. -/
theorem summable_windowMass_factorial (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (z : ℝ) :
    Summable (fun q : ℕ ↦ z ^ q * windowMass q alpha beta lambda a b R /
      (q.factorial : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := exists_windowMass_bound hbeta ha hab R
  apply (summable_factorial_window_majorant hbeta.le ha.le hD z).of_norm_bounded
  intro q
  obtain ⟨hm0, hm⟩ := hbound q alpha lambda
  rw [norm_div, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg hm0,
    Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (pow_nonneg (abs_nonneg z) q)

end PerronWright.FactorialDensity
