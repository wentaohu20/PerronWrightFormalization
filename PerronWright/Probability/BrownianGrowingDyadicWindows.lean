import PerronWright.Probability.BrownianContinuousModification

/-!
# Summable bad events on growing Brownian time windows

The windows have length `2^N` and the permitted amplitude is `3^N`.
Both estimates use the actual Gaussian fourth moments. The resulting
Borel--Cantelli bound controls every dyadic level on every sufficiently
large window, rather than supplying an assumed full-horizon growth law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGrowingDyadicWindows

open BrownianGaussianSkeleton BrownianGaussianMoments BrownianDyadicGrid
open BrownianDyadicModulus

def levelBad (N n : ℕ) : Set (ℕ → ℝ) :=
  ⋃ k : Fin (2 ^ N * 2 ^ n),
    {x | (3 : ℝ) ^ N * decay ^ n ≤ ‖increment n k.val x‖}

def windowBad (N : ℕ) : Set (ℕ → ℝ) := ⋃ n : ℕ, levelBad N n

def baseBad (N : ℕ) : Set (ℕ → ℝ) :=
  ⋃ k : Fin (2 ^ N),
    {x | (3 : ℝ) ^ N ≤
      ‖rationalProcess (dyadicTime 0 k.val) x - rationalProcess (dyadicTime 0 0) x‖}

theorem level_tail_scaling (N n : ℕ) :
    (2 ^ N * 2 ^ n : ℕ) *
      (fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 /
        ((3 : ℝ) ^ N * decay ^ n) ^ 4) =
      fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n := by
  have h := tail_scaling (2 ^ N) n
  have hp : ((3 : ℝ) ^ N) ^ 4 = (81 : ℝ) ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hp]
  calc
    _ = ((2 ^ N * 2 ^ n : ℕ) *
      (fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4)) /
        (81 : ℝ) ^ N := by ring
    _ = (fourthMomentConstant * (2 ^ N : ℕ) * tailRatio ^ n) / (81 : ℝ) ^ N :=
      congrArg (fun z : ℝ ↦ z / (81 : ℝ) ^ N) h
    _ = _ := by simp only [Nat.cast_pow, Nat.cast_ofNat, div_pow]; ring

theorem levelBad_real_bound (N n : ℕ) :
    rationalLaw.real (levelBad N n) ≤
      fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n := by
  calc
    _ ≤ ∑ k : Fin (2 ^ N * 2 ^ n),
      rationalLaw.real {x | (3 : ℝ) ^ N * decay ^ n ≤ ‖increment n k.val x‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin (2 ^ N * 2 ^ n),
      fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 /
        ((3 : ℝ) ^ N * decay ^ n) ^ 4 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [increment, dyadicTime_adjacent_abs] using
        rational_increment_tail_bound (dyadicTime n (k.val + 1)) (dyadicTime n k.val)
          (mul_pos (by positivity) (pow_pos decay_pos n))
    _ = _ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        using level_tail_scaling N n

theorem levelBad_measure_bound (N n : ℕ) :
    rationalLaw (levelBad N n) ≤
      ENNReal.ofReal (fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top rationalLaw (levelBad N n))]
  exact ENNReal.ofReal_le_ofReal (levelBad_real_bound N n)

theorem windowBad_measure_bound (N : ℕ) :
    rationalLaw (windowBad N) ≤
      ENNReal.ofReal (fourthMomentConstant * (2 / 81 : ℝ) ^ N / (1 - tailRatio)) := by
  have hs : Summable (fun n : ℕ ↦
      fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n) :=
    (summable_geometric_of_abs_lt_one
      (by rw [abs_of_pos tailRatio_pos]; exact tailRatio_lt_one)).mul_left _
  calc
    _ ≤ ∑' n : ℕ, rationalLaw (levelBad N n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
      (fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n) :=
      ENNReal.tsum_le_tsum (levelBad_measure_bound N)
    _ = ENNReal.ofReal (∑' n : ℕ,
      fourthMomentConstant * (2 / 81 : ℝ) ^ N * tailRatio ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n ↦
        mul_nonneg (mul_nonneg fourthMomentConstant_nonneg (by positivity))
          (pow_nonneg tailRatio_pos.le n)) hs).symm
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one tailRatio_pos.le tailRatio_lt_one]
      congr 1

theorem windowBad_tsum_ne_top : (∑' N : ℕ, rationalLaw (windowBad N)) ≠ ∞ := by
  have hs : Summable (fun N : ℕ ↦
      fourthMomentConstant * (2 / 81 : ℝ) ^ N / (1 - tailRatio)) := by
    exact ((summable_geometric_of_abs_lt_one (by norm_num : |(2 / 81 : ℝ)| < 1)).mul_left
      fourthMomentConstant).div_const _
  exact ne_of_lt ((ENNReal.tsum_le_tsum windowBad_measure_bound).trans_lt hs.tsum_ofReal_lt_top)

theorem base_tail_scaling (N : ℕ) :
    (2 ^ N : ℕ) * (fourthMomentConstant * ((2 ^ N : ℕ) : ℝ) ^ 2 /
      ((3 : ℝ) ^ N) ^ 4) = fourthMomentConstant * (8 / 81 : ℝ) ^ N := by
  have hp : ((3 : ℝ) ^ N) ^ 4 = (81 : ℝ) ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hq : ((2 : ℝ) ^ N) ^ 3 = (8 : ℝ) ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat, hp, div_pow]
  calc
    _ = fourthMomentConstant * (((2 : ℝ) ^ N) ^ 3 / (81 : ℝ) ^ N) := by ring
    _ = _ := by rw [hq]

theorem baseBad_real_bound (N : ℕ) :
    rationalLaw.real (baseBad N) ≤ fourthMomentConstant * (8 / 81 : ℝ) ^ N := by
  calc
    _ ≤ ∑ k : Fin (2 ^ N), rationalLaw.real {x | (3 : ℝ) ^ N ≤
      ‖rationalProcess (dyadicTime 0 k.val) x - rationalProcess (dyadicTime 0 0) x‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin (2 ^ N),
      fourthMomentConstant * ((2 ^ N : ℕ) : ℝ) ^ 2 / ((3 : ℝ) ^ N) ^ 4 := by
      apply Finset.sum_le_sum
      intro k _
      have ht := rational_increment_tail_bound (dyadicTime 0 k.val) (dyadicTime 0 0)
        (by positivity : 0 < (3 : ℝ) ^ N)
      simp only [dyadicTime_real, pow_zero, div_one, Nat.cast_zero, sub_zero] at ht
      rw [abs_of_nonneg (Nat.cast_nonneg k.val : (0 : ℝ) ≤ k.val)] at ht
      apply ht.trans
      have hk : (k.val : ℝ) ≤ (2 ^ N : ℕ) := by exact_mod_cast k.isLt.le
      have hC := fourthMomentConstant_nonneg
      gcongr
    _ = _ := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        using base_tail_scaling N

theorem baseBad_measure_bound (N : ℕ) :
    rationalLaw (baseBad N) ≤ ENNReal.ofReal (fourthMomentConstant * (8 / 81 : ℝ) ^ N) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top rationalLaw (baseBad N))]
  exact ENNReal.ofReal_le_ofReal (baseBad_real_bound N)

theorem baseBad_tsum_ne_top : (∑' N : ℕ, rationalLaw (baseBad N)) ≠ ∞ := by
  have hs : Summable (fun N : ℕ ↦ fourthMomentConstant * (8 / 81 : ℝ) ^ N) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(8 / 81 : ℝ)| < 1)).mul_left _
  exact ne_of_lt ((ENNReal.tsum_le_tsum baseBad_measure_bound).trans_lt hs.tsum_ofReal_lt_top)

theorem ae_eventually_all_level_bound :
    ∀ᵐ x ∂rationalLaw, ∀ᶠ N in atTop, ∀ n k : ℕ, k < 2 ^ N * 2 ^ n →
      ‖increment n k x‖ ≤ (3 : ℝ) ^ N * decay ^ n := by
  filter_upwards [ae_eventually_notMem windowBad_tsum_ne_top] with x hx
  filter_upwards [hx] with N hN
  intro n k hk
  apply le_of_lt
  apply lt_of_not_ge
  intro hh
  exact hN (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hh⟩⟩)

theorem ae_eventually_base_bound :
    ∀ᵐ x ∂rationalLaw, ∀ᶠ N in atTop, ∀ k : ℕ, k < 2 ^ N →
      ‖rationalProcess (dyadicTime 0 k) x - rationalProcess (dyadicTime 0 0) x‖ ≤
        (3 : ℝ) ^ N := by
  filter_upwards [ae_eventually_notMem baseBad_tsum_ne_top] with x hx
  filter_upwards [hx] with N hN
  intro k hk
  apply le_of_lt
  apply lt_of_not_ge
  intro hh
  exact hN (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hh⟩)

end PerronWright.BrownianGrowingDyadicWindows
