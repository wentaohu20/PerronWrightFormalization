import PerronWright.Probability.ExactFactorialExpectation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Critical time and size scaling

The nonnegative time convention defines the graph law at every finite `n`;
it equals the paper's literal critical-window time for all sufficiently
large `n`.  The floor-size estimate is uniform in the positive size variable.
-/

open Filter Topology
open scoped Topology Real

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CriticalScaling

/-- Critical-window time, clipped only at finitely many small sizes when needed. -/
def time (lambda : ℝ) (n : ℕ) : ℝ :=
  max (1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) 0

theorem time_nonneg (lambda : ℝ) (n : ℕ) : 0 ≤ time lambda n := le_max_right _ _

theorem raw_time_tendsto (lambda : ℝ) :
    Tendsto (fun n : ℕ ↦ 1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (nhds 1) := by
  simpa only [Function.comp_apply, mul_zero, add_zero] using
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop))

theorem time_eq_raw_eventually (lambda : ℝ) :
    ∀ᶠ n : ℕ in atTop, time lambda n =
      1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  filter_upwards [(raw_time_tendsto lambda).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  exact max_eq_left hn.le

theorem time_tendsto (lambda : ℝ) : Tendsto (time lambda) atTop (nhds 1) := by
  apply (raw_time_tendsto lambda).congr'
  filter_upwards [time_eq_raw_eventually lambda] with n hn
  exact hn.symm

/-- The literal component size used by the local probability theorem. -/
def size (x : ℝ) (n : ℕ) : ℕ := ⌊x * (n : ℝ) ^ (2 / 3 : ℝ)⌋₊

/-- Uniform floor error before division by the size scale. -/
theorem size_floor_error {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |(size x n : ℝ) - x * (n : ℝ) ^ (2 / 3 : ℝ)| ≤ 1 :=
  Nat.abs_floor_sub_le (mul_nonneg hx (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- Uniform floor error on the normalized component-size scale. -/
theorem size_normalized_error {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    |(size x n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) - x| ≤
      1 / (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hs : 0 < (n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have he : (size x n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) - x =
      ((size x n : ℝ) - x * (n : ℝ) ^ (2 / 3 : ℝ)) /
        (n : ℝ) ^ (2 / 3 : ℝ) := by field_simp
  rw [he, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right (size_floor_error hx n) hs.le

/-- The limiting real size is recovered from the literal integer floor. -/
theorem size_normalized_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ ↦ (size x n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (nhds x) := by
  have hs : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (nhds 0) := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(2 / 3 : ℝ)))
        atTop (nhds 0) := by
      have ht : Tendsto (fun y : ℝ ↦ y ^ (-(2 / 3 : ℝ))) atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)
      exact ht.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    simpa only [one_div] using hn.congr'
      (Filter.Eventually.of_forall (fun n ↦ Real.rpow_neg (Nat.cast_nonneg n) (2 / 3 : ℝ)))
  have hlo : Tendsto (fun n : ℕ ↦ x - 1 / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (nhds x) := by simpa only [sub_zero] using tendsto_const_nhds.sub hs
  have hhi : Tendsto (fun n : ℕ ↦ x + 1 / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (nhds x) := by simpa only [add_zero] using tendsto_const_nhds.add hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have he := (abs_le.mp (size_normalized_error hx (by omega : 0 < n))).1
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have he := (abs_le.mp (size_normalized_error hx (by omega : 0 < n))).2
    linarith

end PerronWright.CriticalScaling
