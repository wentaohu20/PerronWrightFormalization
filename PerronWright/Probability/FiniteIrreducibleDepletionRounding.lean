import PerronWright.Probability.FiniteIrreducibleDeterministicDepletion

/-! # Actual O(1) population rounding in the leading depletion exponent

The ambient counts are arbitrary natural counts. The deterministic
comparison replaces their quadratic/cubic denominators by the fixed
target weights, with a proved all-profile error tending to zero.
-/

open Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FiniteIrreducibleDepletionRounding

open FiniteIrreducibleDeterministicDepletion

theorem inverse_count_error {c d D : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hlow : d / 2 ≤ c) (herr : |c - d| ≤ D) :
    |1 / c - 1 / d| ≤ 2 * D / d ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans herr
  have heq : 1 / c - 1 / d = (d - c) / (c * d) := by
    field_simp
  have hab : |d - c| ≤ D := by simpa only [abs_sub_comm] using herr
  have hcd : d ^ 2 / 2 ≤ c * d := by nlinarith
  rw [heq, abs_div, abs_of_pos (mul_pos hc hd)]
  calc
    _ ≤ D / (c * d) := div_le_div_of_nonneg_right hab (mul_pos hc hd).le
    _ ≤ D / (d ^ 2 / 2) := by gcongr
    _ = _ := by ring

theorem inverse_sq_count_error {c d D : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hlow : d / 2 ≤ c) (herr : |c - d| ≤ D) :
    |1 / c ^ 2 - 1 / d ^ 2| ≤ 6 * D / d ^ 3 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans herr
  have hinv : 1 / c ≤ 2 / d := by
    apply (div_le_div_iff₀ hc hd).mpr
    linarith
  have hs : |1 / c + 1 / d| ≤ 3 / d := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / c + 1 / d)]
    calc
      _ ≤ 2 / d + 1 / d := by linarith
      _ = _ := by ring
  have heq : 1 / c ^ 2 - 1 / d ^ 2 = (1 / c - 1 / d) * (1 / c + 1 / d) := by ring
  rw [heq, abs_mul]
  exact (mul_le_mul (inverse_count_error hc hd hlow herr) hs (abs_nonneg _)
    (by positivity)).trans_eq (by ring)

theorem quadratic_count_error {c d D K : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hlow : d / 2 ≤ c) (herr : |c - d| ≤ D) :
    |K ^ 2 / (2 * c) - K ^ 2 / (2 * d)| ≤ D * K ^ 2 / d ^ 2 := by
  have heq : K ^ 2 / (2 * c) - K ^ 2 / (2 * d) =
      (K ^ 2 / 2) * (1 / c - 1 / d) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K ^ 2 / 2)]
  exact (mul_le_mul_of_nonneg_left (inverse_count_error hc hd hlow herr)
    (by positivity)).trans_eq (by ring)

theorem cubic_count_error {c d D K : ℝ} (hc : 0 < c) (hd : 0 < d) (hK : 0 ≤ K)
    (hlow : d / 2 ≤ c) (herr : |c - d| ≤ D) :
    |K ^ 3 / (6 * c ^ 2) - K ^ 3 / (6 * d ^ 2)| ≤ D * K ^ 3 / d ^ 3 := by
  have heq : K ^ 3 / (6 * c ^ 2) - K ^ 3 / (6 * d ^ 2) =
      (K ^ 3 / 6) * (1 / c ^ 2 - 1 / d ^ 2) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K ^ 3 / 6)]
  exact (mul_le_mul_of_nonneg_left (inverse_sq_count_error hc hd hlow herr)
    (by positivity)).trans_eq (by ring)

variable {S : Type*} [Fintype S] [DecidableEq S]

def roundingEnvelope (M : FiniteIrreducibleModel S) (D C : ℝ) (n : ℕ) : ℝ :=
  ∑ a, ((D * C ^ 2 / (M.weight a) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) +
    (D * C ^ 3 / (M.weight a) ^ 3) * (n : ℝ) ^ (-1 : ℝ))

theorem roundingEnvelope_tendsto_zero (M : FiniteIrreducibleModel S) (D C : ℝ) :
    Tendsto (roundingEnvelope M D C) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ ∑ a : S,
    ((D * C ^ 2 / (M.weight a) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) +
      (D * C ^ 3 / (M.weight a) ^ 3) * (n : ℝ) ^ (-1 : ℝ))) atTop (𝓝 0)
  have ht (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-x)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hx).comp tendsto_natCast_atTop_atTop
  simpa only [roundingEnvelope, mul_zero, zero_add, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun a _ ↦
      ((ht (2 / 3) (by norm_num)).const_mul (D * C ^ 2 / (M.weight a) ^ 2)).add
        ((ht 1 (by norm_num)).const_mul (D * C ^ 3 / (M.weight a) ^ 3)))

theorem leading_denominator_rounding_error (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (c K : S → ℕ) {D C : ℝ} (hD : 0 ≤ D)
    (hround : ∀ a, |(c a : ℝ) - (n : ℝ) * M.weight a| ≤ D)
    (hlow : ∀ a, (n : ℝ) * M.weight a / 2 ≤ c a)
    (hsize : (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    |(∑ a, (K a : ℝ) ^ 2 / (2 * c a) +
        ∑ a, (K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2)) -
      (∑ a, (K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a) +
        ∑ a, (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2))| ≤
          roundingEnvelope M D C n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp2 : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnR.le,
      ← Real.rpow_natCast _ 2, ← Real.rpow_sub hnR]
    norm_num
  have hp3 : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 / (n : ℝ) ^ 3 =
      (n : ℝ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hnR.le,
      ← Real.rpow_natCast _ 3, ← Real.rpow_sub hnR]
    norm_num
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  dsimp only [roundingEnvelope]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro a _
  have hd : 0 < (n : ℝ) * M.weight a := mul_pos hnR (M.weight_pos a)
  have hc : (0 : ℝ) < c a := lt_of_lt_of_le (half_pos hd) (hlow a)
  have hK : (K a : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) :=
    (Finset.single_le_sum (fun b _ ↦ Nat.cast_nonneg (K b)) (Finset.mem_univ a)).trans hsize
  have hq := quadratic_count_error hc hd (hlow a) (hround a) (K := (K a : ℝ))
  have hu := cubic_count_error hc hd (Nat.cast_nonneg (K a)) (hlow a) (hround a)
  have heq : (K a : ℝ) ^ 2 / (2 * c a) + (K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2) -
      ((K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a) +
        (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)) =
      ((K a : ℝ) ^ 2 / (2 * c a) - (K a : ℝ) ^ 2 / (2 * ((n : ℝ) * M.weight a))) +
        ((K a : ℝ) ^ 3 / (6 * (c a : ℝ) ^ 2) -
          (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)) := by ring
  rw [heq]
  refine (abs_add_le _ _).trans ((add_le_add hq hu).trans ?_)
  have hq' : D * (K a : ℝ) ^ 2 / ((n : ℝ) * M.weight a) ^ 2 ≤
      (D * C ^ 2 / (M.weight a) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    calc
      _ ≤ D * (C * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / ((n : ℝ) * M.weight a) ^ 2 := by
        gcongr
      _ = (D * C ^ 2 / (M.weight a) ^ 2) *
          (((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by ring
      _ = _ := by rw [hp2]
  have hu' : D * (K a : ℝ) ^ 3 / ((n : ℝ) * M.weight a) ^ 3 ≤
      (D * C ^ 3 / (M.weight a) ^ 3) * (n : ℝ) ^ (-1 : ℝ) := by
    calc
      _ ≤ D * (C * (n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 / ((n : ℝ) * M.weight a) ^ 3 := by
        gcongr
      _ = (D * C ^ 3 / (M.weight a) ^ 3) *
          (((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 / (n : ℝ) ^ 3) := by ring
      _ = _ := by rw [hp3]
  exact add_le_add hq' hu'

/-- The full rounded-population expansion in fixed target μ coordinates.
Its vanishing remainder is uniform over all integer profiles on the
critical size window, including profiles far from the Perron mean. -/
theorem normalizedDepletion_uniform_target_remainder (M : FiniteIrreducibleModel S)
    (c : ℕ → S → ℕ) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ K : S → ℕ,
        (∑ a, (K a : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
        0 < normalizedDepletion (c n) K ∧
        |Real.log (normalizedDepletion (c n) K) +
          ∑ a, (K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a) +
          ∑ a, (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)| ≤ err n := by
  obtain ⟨err, ht, hb⟩ := normalizedDepletion_uniform_leading_remainder M c D C hC hround
  refine ⟨fun n ↦ err n + roundingEnvelope M D C n,
    by simpa only [zero_add] using ht.add (roundingEnvelope_tendsto_zero M D C), ?_⟩
  filter_upwards [hb, hround, eventually_count_ratio_domain M c D hround] with n hn hr hd
  intro K hsize
  have hlow : ∀ a, (n : ℝ) * M.weight a / 2 ≤ c n a := by
    intro a
    have hμ := mul_pos (Nat.cast_pos.mpr hd.1 : (0 : ℝ) < n) (M.weight_pos a)
    have hD' := (div_le_iff₀ hμ).mp (hd.2.2 a)
    have hh := (abs_le.mp (hr a)).1
    linarith
  have hg := leading_denominator_rounding_error M hd.1 (c n) K hD hr hlow hsize
  have hh := hn K hsize
  refine ⟨hh.1, ?_⟩
  let A : ℝ := ∑ a, (K a : ℝ) ^ 2 / (2 * c n a) +
    ∑ a, (K a : ℝ) ^ 3 / (6 * (c n a : ℝ) ^ 2)
  let B : ℝ := ∑ a, (K a : ℝ) ^ 2 / (2 * (n : ℝ) * M.weight a) +
    ∑ a, (K a : ℝ) ^ 3 / (6 * ((n : ℝ) * M.weight a) ^ 2)
  have heq : Real.log (normalizedDepletion (c n) K) + B =
      (Real.log (normalizedDepletion (c n) K) + A) + (B - A) := by ring
  rw [add_assoc]
  change |Real.log (normalizedDepletion (c n) K) + B| ≤ _
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (by simpa only [A, add_assoc] using hh.2)
    (by simpa only [A, B, abs_sub_comm] using hg))

end PerronWright.FiniteIrreducibleDepletionRounding
