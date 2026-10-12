import PerronWright.Probability.BrownianGaussianMoments
import PerronWright.Probability.BrownianDyadicGrid
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# An actual almost-sure dyadic modulus for the constructed Gaussian law

The event bounds come from the proved fourth moments of the literal
rational Gaussian skeleton. Summability and Borel--Cantelli yield an
all-level neighbor bound, simultaneously on every bounded time window.
This supplies the probabilistic input to a deterministic continuous
extension; no continuous Brownian realization is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianDyadicModulus

open BrownianGaussianSkeleton BrownianGaussianMoments BrownianDyadicGrid

def decay : ℝ := 7 / 8

def tailRatio : ℝ := 1 / (2 * decay ^ 4)

theorem decay_pos : 0 < decay := by norm_num [decay]

theorem decay_lt_one : decay < 1 := by norm_num [decay]

theorem tailRatio_pos : 0 < tailRatio := by norm_num [tailRatio,decay]

theorem tailRatio_lt_one : tailRatio < 1 := by norm_num [tailRatio,decay]

def increment (n k : ℕ) (x : ℕ → ℝ) : ℝ :=
  rationalProcess (dyadicTime n (k + 1)) x - rationalProcess (dyadicTime n k) x

def badLevel (M n : ℕ) : Set (ℕ → ℝ) :=
  ⋃ k : Fin (M * 2 ^ n), {x | decay ^ n ≤ ‖increment n k.val x‖}

theorem measurable_increment (n k : ℕ) : Measurable (increment n k) := by
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem measurableSet_badLevel (M n : ℕ) : MeasurableSet (badLevel M n) := by
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_le measurable_const ((measurable_increment n k.val).norm)

theorem increment_tail_bound (n k : ℕ) :
    rationalLaw.real {x | decay ^ n ≤ ‖increment n k x‖} ≤
      fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4 := by
  simpa only [increment,dyadicTime_adjacent_abs] using
    rational_increment_tail_bound (dyadicTime n (k + 1)) (dyadicTime n k)
      (pow_pos decay_pos n)

theorem tail_scaling (M n : ℕ) :
    (M * 2 ^ n : ℕ) *
      (fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4) =
      fourthMomentConstant * (M : ℝ) * tailRatio ^ n := by
  have hg : decay ≠ 0 := ne_of_gt decay_pos
  have hpow : (decay ^ 4) ^ n = (decay ^ n) ^ 4 := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,tailRatio,div_pow,one_pow,mul_pow,hpow]
  field_simp

/-- The actual union of all adjacent-grid bad increments has a genuine
geometric probability bound; its number of terms is the literal grid size. -/
theorem badLevel_real_bound (M n : ℕ) :
    rationalLaw.real (badLevel M n) ≤ fourthMomentConstant * (M : ℝ) * tailRatio ^ n := by
  calc
    _ ≤ ∑ k : Fin (M * 2 ^ n), rationalLaw.real {x | decay ^ n ≤ ‖increment n k.val x‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin (M * 2 ^ n),
        fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4 :=
      Finset.sum_le_sum (fun k _ ↦ increment_tail_bound n k.val)
    _ = fourthMomentConstant * (M : ℝ) * tailRatio ^ n := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using tail_scaling M n

theorem badLevel_measure_bound (M n : ℕ) :
    rationalLaw (badLevel M n) ≤
      ENNReal.ofReal (fourthMomentConstant * (M : ℝ) * tailRatio ^ n) := by
  calc
    _ = ENNReal.ofReal (rationalLaw.real (badLevel M n)) := by
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (badLevel_real_bound M n)

theorem badLevel_tsum_ne_top (M : ℕ) : (∑' n, rationalLaw (badLevel M n)) ≠ ∞ := by
  have hs : Summable (fun n : ℕ ↦ fourthMomentConstant * (M : ℝ) * tailRatio ^ n) :=
    (summable_geometric_of_abs_lt_one (by rw [abs_of_pos tailRatio_pos]; exact tailRatio_lt_one)).mul_left _
  exact ne_of_lt ((ENNReal.tsum_le_tsum (badLevel_measure_bound M)).trans_lt
    hs.tsum_ofReal_lt_top)

/-- The actual skeleton has eventually small dyadic neighbor increments
on every fixed window, by Borel--Cantelli on the actual law. -/
theorem ae_eventually_neighbor_bound (M : ℕ) :
    ∀ᵐ x ∂rationalLaw, ∀ᶠ n in atTop, ∀ k : ℕ, k < M * 2 ^ n →
      ‖increment n k x‖ ≤ decay ^ n := by
  filter_upwards [ae_eventually_notMem (badLevel_tsum_ne_top M)] with x hx
  filter_upwards [hx] with n hn
  intro k hk
  have hnot : ¬ decay ^ n ≤ ‖increment n k x‖ := by
    intro hh
    exact hn (Set.mem_iUnion.mpr ⟨⟨k,hk⟩,hh⟩)
  exact (lt_of_not_ge hnot).le

/-- A deterministic finite-prefix absorption lemma. Its hypotheses are
plain real sequence bounds, not a stochastic regularity interface. -/
theorem exists_all_level_constant (a : ℕ → ℕ → ℝ) (M : ℕ)
    (h : ∀ᶠ n in atTop, ∀ k : ℕ, k < M * 2 ^ n → ‖a n k‖ ≤ decay ^ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k : ℕ, k < M * 2 ^ n → ‖a n k‖ ≤ C * decay ^ n := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  let C : ℝ := 1 + ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (M * 2 ^ n), ‖a n k‖ / decay ^ n
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (M * 2 ^ n), ‖a n k‖ / decay ^ n := by
    apply Finset.sum_nonneg
    intro n _
    exact Finset.sum_nonneg (fun k _ ↦ div_nonneg (norm_nonneg _) (pow_pos decay_pos n).le)
  have hC : 1 ≤ C := le_add_of_nonneg_right hsum
  refine ⟨C,le_trans (by norm_num) hC,?_⟩
  intro n k hk
  by_cases hn : N ≤ n
  · exact (hN n hn k hk).trans (le_mul_of_one_le_left (pow_pos decay_pos n).le hC)
  · have hn' : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hi : ‖a n k‖ / decay ^ n ≤ ∑ j ∈ Finset.range (M * 2 ^ n), ‖a n j‖ / decay ^ n :=
      Finset.single_le_sum (fun j _ ↦ div_nonneg (norm_nonneg _) (pow_pos decay_pos n).le)
        (Finset.mem_range.mpr hk)
    have ho : (∑ j ∈ Finset.range (M * 2 ^ n), ‖a n j‖ / decay ^ n) ≤
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (M * 2 ^ i), ‖a i j‖ / decay ^ i :=
      Finset.single_le_sum (f := fun i ↦ ∑ j ∈ Finset.range (M * 2 ^ i), ‖a i j‖ / decay ^ i)
        (fun i _ ↦ Finset.sum_nonneg
        (fun j _ ↦ div_nonneg (norm_nonneg _) (pow_pos decay_pos i).le)) hn'
    have hc : ‖a n k‖ / decay ^ n ≤ C :=
      (hi.trans ho).trans (le_add_of_nonneg_left (by norm_num))
    exact (div_le_iff₀ (pow_pos decay_pos n)).1 hc

/-- Terminal probabilistic input for a genuine continuous modification:
simultaneously on every integer time window, all dyadic neighboring
increments obey a sample-dependent geometric bound. -/
theorem ae_all_window_neighbor_bound :
    ∀ᵐ x ∂rationalLaw, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n k : ℕ, k < M * 2 ^ n →
        ‖rationalProcess (dyadicTime n (k + 1)) x - rationalProcess (dyadicTime n k) x‖ ≤
          C * (7 / 8 : ℝ) ^ n := by
  have hh : ∀ᵐ x ∂rationalLaw, ∀ M : ℕ, ∀ᶠ n in atTop,
      ∀ k : ℕ, k < M * 2 ^ n → ‖increment n k x‖ ≤ decay ^ n :=
    ae_all_iff.mpr ae_eventually_neighbor_bound
  filter_upwards [hh] with x hx
  intro M
  simpa only [increment,decay] using exists_all_level_constant (fun n k ↦ increment n k x) M (hx M)

end PerronWright.BrownianDyadicModulus
