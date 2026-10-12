import PerronWright.Probability.CriticalResidualScaling
import PerronWright.Probability.AnnealedTupleResidualCounting

/-!
# Literal floor-size tuples on compact critical-size windows

The floors, positivity, total-size bounds, and actual embeddings below are
proved from the positive real size window.  They are not supplied as local
component-asymptotic interfaces.
-/

open Filter Topology
open scoped Real Topology BigOperators

noncomputable section
set_option maxHeartbeats 600000

namespace PerronWright.CriticalSizeTuple

open CriticalScaling AnnealedTupleResidualCounting

theorem size_le_scaled {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (size x n : ℝ) ≤ x * (n : ℝ)^(2/3 : ℝ) :=
  Nat.floor_le (mul_nonneg hx (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- All literal floors are positive on one common positive size window. -/
theorem eventually_size_pos_on_window (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ m in atTop, ∀ x : ℝ, a ≤ x → 0 < size x (N m) := by
  have ht : Tendsto (fun m ↦ (N m : ℝ)^(2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp
      (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [ht.eventually (eventually_ge_atTop (a⁻¹))] with m hm x hx
  apply Nat.floor_pos.mpr
  have h := mul_le_mul_of_nonneg_left hm ha.le
  rw [mul_inv_cancel₀ ha.ne'] at h
  exact h.trans (mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The uniform floor error also permits a varying real size sequence. -/
theorem size_normalized_varying_tendsto (N : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m) {s : ℝ} (hs : Tendsto x atTop (𝓝 s)) :
    Tendsto (fun m ↦ (size (x m) (N m) : ℝ) / (N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 s) := by
  have he : Tendsto (fun m ↦ 1 / (N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2/3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
    simpa only [Function.comp_def,Real.rpow_neg (Nat.cast_nonneg _),one_div] using hpow
  have hlo := hs.sub he
  have hhi := hs.add he
  simp only [sub_zero,add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact Eventually.of_forall (fun m ↦ by
      have h := (abs_le.mp (size_normalized_error (hx m) (hN m))).1
      linarith)
  · exact Eventually.of_forall (fun m ↦ by
      have h := (abs_le.mp (size_normalized_error (hx m) (hN m))).2
      linarith)

theorem totalSize_le_on_window {q n : ℕ} (x : Fin q → ℝ)
    (b : ℝ) (hx : ∀ i, 0 ≤ x i) (hb : ∀ i, x i ≤ b) :
    ((∑ i, size (x i) n : ℕ) : ℝ) ≤ (q : ℝ) * b * (n : ℝ)^(2/3 : ℝ) := by
  simp only [Nat.cast_sum]
  calc
    ∑ i, (size (x i) n : ℝ) ≤ ∑ _i : Fin q, b * (n : ℝ)^(2/3 : ℝ) := by
      exact Finset.sum_le_sum (fun i _ ↦ (size_le_scaled (hx i) n).trans
        (mul_le_mul_of_nonneg_right (hb i) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
    _ = (q : ℝ) * b * (n : ℝ)^(2/3 : ℝ) := by simp [mul_assoc]

theorem totalSize_normalized_tendsto {q : ℕ} (N : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (hx : ∀ m i, 0 ≤ x m i)
    (s : Fin q → ℝ) (hs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ ((∑ i, size (x m i) (N m) : ℕ) : ℝ) /
      (N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 (∑ i, s i)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦
    size_normalized_varying_tendsto N hN hNt (fun m ↦ x m i) (fun m ↦ hx m i) (hs i))
  simpa only [Nat.cast_sum,Finset.sum_div] using h

/-- A concrete ambient placement exists whenever the true selected total
fits in the graph; this does not assume a labelling correspondence. -/
theorem nonempty_placements_of_total_le {n q : ℕ} (k : Fin q → ℕ)
    (hk : ∑ i, k i ≤ n) : Nonempty (Placements n k) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [SelectedVertices,Fintype.card_sigma,Fintype.card_fin] using hk

/-- In a bounded positive size window the actual floor tuples fit inside
the graph for all sufficiently large sizes. -/
theorem eventually_floor_placements {q : ℕ} (N : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hx : ∀ m i, 0 ≤ x m i) (hxb : ∀ m i, x m i ≤ b) :
    ∀ᶠ m in atTop, Nonempty (Placements (N m) (fun i ↦ size (x m i) (N m))) := by
  let K m := ∑ i, size (x m i) (N m)
  have hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ (q : ℝ)*b*(N m : ℝ)^(2/3 : ℝ) :=
    Eventually.of_forall (fun m ↦ totalSize_le_on_window (x m) b (hx m) (hxb m))
  filter_upwards [FinitePopulationLog.eventually_critical_size_le_half
    N K hN hNt (show (0 : ℝ) ≤ (q : ℝ)*b from mul_nonneg (Nat.cast_nonneg q) hb) hsize] with m hm
  apply nonempty_placements_of_total_le
  have hle : (K m : ℝ) ≤ N m := by
    linarith [(Nat.cast_nonneg (N m) : (0 : ℝ) ≤ N m)]
  exact_mod_cast hle

end PerronWright.CriticalSizeTuple
