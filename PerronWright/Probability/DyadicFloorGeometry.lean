import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Literal dyadic floor geometry

These deterministic facts are used to extend the constructed rational
Gaussian skeleton. The floor at the next level is exactly an even index
or its successor; this is proved from the actual floor inequalities.
-/

open scoped NNReal

noncomputable section

namespace PerronWright.DyadicFloorGeometry

def index (n : ℕ) (t : ℝ≥0) : ℕ := ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊

def coordinate (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n

theorem index_le_scaled (n : ℕ) (t : ℝ≥0) :
    (index n t : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n :=
  Nat.floor_le (mul_nonneg t.property (by positivity))

theorem scaled_lt_index_add_one (n : ℕ) (t : ℝ≥0) :
    (t : ℝ) * (2 : ℝ) ^ n < (index n t : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem index_succ_bounds (n : ℕ) (t : ℝ≥0) :
    2 * index n t ≤ index (n + 1) t ∧ index (n + 1) t ≤ 2 * index n t + 1 := by
  have h0 := index_le_scaled n t
  have h1 := scaled_lt_index_add_one n t
  have h2 := index_le_scaled (n + 1) t
  have h3 := scaled_lt_index_add_one (n + 1) t
  rw [pow_succ] at h2 h3
  have hlo : (2 * index n t : ℝ) < (index (n + 1) t : ℝ) + 1 := by nlinarith
  have hhi : (index (n + 1) t : ℝ) < (2 * index n t : ℝ) + 2 := by nlinarith
  have hlo' : 2 * index n t < index (n + 1) t + 1 := by exact_mod_cast hlo
  have hhi' : index (n + 1) t < 2 * index n t + 2 := by exact_mod_cast hhi
  omega

theorem index_succ_eq_even_or_odd (n : ℕ) (t : ℝ≥0) :
    index (n + 1) t = 2 * index n t ∨ index (n + 1) t = 2 * index n t + 1 := by
  have h := index_succ_bounds n t
  omega

theorem index_lt_window {M : ℕ} {t : ℝ≥0} (ht : (t : ℝ) < M) (n : ℕ) :
    index n t < M * 2 ^ n := by
  have h := (index_le_scaled n t).trans_lt
    (mul_lt_mul_of_pos_right ht (by positivity : 0 < (2 : ℝ) ^ n))
  exact_mod_cast h

@[simp] theorem coordinate_real (n k : ℕ) :
    (coordinate n k : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by
  simp [coordinate]

theorem coordinate_succ_even (n k : ℕ) :
    coordinate (n + 1) (2 * k) = coordinate n k := by
  apply NNReal.eq
  simp only [coordinate_real, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem scaled_coordinate {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    (coordinate m k : ℝ) * (2 : ℝ) ^ n = (k * 2 ^ (n - m) : ℕ) := by
  rw [coordinate_real, show n = m + (n - m) by omega, pow_add]
  push_cast
  field_simp
  simp only [Nat.add_sub_cancel_left]

theorem index_coordinate {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    index n (coordinate m k) = k * 2 ^ (n - m) := by
  rw [index, scaled_coordinate hmn]
  exact Nat.floor_natCast _

end PerronWright.DyadicFloorGeometry
