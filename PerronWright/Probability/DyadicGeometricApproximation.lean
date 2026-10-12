import PerronWright.Probability.DyadicFloorGeometry

/-!
# A genuine deterministic limit from compatible dyadic samples

This file constructs the real-valued limit of floor samples and proves
its geometric error bound and its exact values at every dyadic point.
The subsequent extension lemma proves continuity. The probability file
will supply the bounds from the actual Gaussian law, rather than assume
regularity of the final Brownian process.
-/

open Filter Topology
open scoped Topology NNReal

noncomputable section

namespace PerronWright.DyadicGeometricApproximation

open DyadicFloorGeometry

def ratio : ℝ := 7 / 8

theorem ratio_nonneg : 0 ≤ ratio := by norm_num [ratio]
theorem ratio_lt_one : ratio < 1 := by norm_num [ratio]

def Compatible (a : ℕ → ℕ → ℝ) : Prop := ∀ n k, a (n + 1) (2 * k) = a n k

def LocalBound (a : ℕ → ℕ → ℝ) : Prop := ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ n k : ℕ, k < M * 2 ^ n → ‖a n (k + 1) - a n k‖ ≤ C * ratio ^ n

def samples (a : ℕ → ℕ → ℝ) (t : ℝ≥0) (n : ℕ) : ℝ := a n (index n t)

def extension (a : ℕ → ℕ → ℝ) (t : ℝ≥0) : ℝ := limUnder atTop (samples a t)

theorem samples_step_bound {a : ℕ → ℕ → ℝ} (hc : Compatible a)
    {M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n k : ℕ, k < M * 2 ^ n → ‖a n (k + 1) - a n k‖ ≤ C * ratio ^ n)
    {t : ℝ≥0} (ht : (t : ℝ) < M) (n : ℕ) :
    dist (samples a t n) (samples a t (n + 1)) ≤ C * ratio ^ n := by
  rcases index_succ_eq_even_or_odd n t with heven | hodd
  · simp only [samples, heven, hc n, dist_self]
    exact mul_nonneg hC (pow_nonneg ratio_nonneg _)
  · have hk : 2 * index n t < M * 2 ^ (n + 1) := by
      have h := index_lt_window ht (n + 1)
      rw [hodd] at h
      omega
    have h := hb (n + 1) (2 * index n t) hk
    have hstep : dist (samples a t n) (samples a t (n + 1)) ≤ C * ratio ^ (n + 1) := by
      simpa only [samples, hodd, dist_eq_norm, hc n, norm_sub_rev] using h
    apply hstep.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (pow_nonneg ratio_nonneg n) ratio_lt_one.le) hC

theorem samples_cauchy {a : ℕ → ℕ → ℝ} (hc : Compatible a) (hb : LocalBound a)
    (t : ℝ≥0) : CauchySeq (samples a t) := by
  obtain ⟨M, ht⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨C, hC, hbound⟩ := hb M
  exact cauchySeq_of_le_geometric ratio C ratio_lt_one
    (samples_step_bound hc hC hbound ht)

theorem samples_tendsto_extension {a : ℕ → ℕ → ℝ}
    (hc : Compatible a) (hb : LocalBound a) (t : ℝ≥0) :
    Tendsto (samples a t) atTop (𝓝 (extension a t)) :=
  (samples_cauchy hc hb t).tendsto_limUnder

theorem samples_extension_distance {a : ℕ → ℕ → ℝ}
    (hc : Compatible a) (hb : LocalBound a)
    {M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n k : ℕ, k < M * 2 ^ n → ‖a n (k + 1) - a n k‖ ≤ C * ratio ^ n)
    {t : ℝ≥0} (ht : (t : ℝ) < M) (n : ℕ) :
    dist (samples a t n) (extension a t) ≤ C * ratio ^ n / (1 - ratio) :=
  dist_le_of_le_geometric_of_tendsto ratio C ratio_lt_one
    (samples_step_bound hc hC hbound ht) (samples_tendsto_extension hc hb t) n

theorem compatible_refinement {a : ℕ → ℕ → ℝ} (hc : Compatible a) (m k j : ℕ) :
    a (m + j) (k * 2 ^ j) = a m k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : k * 2 ^ (j + 1) = 2 * (k * 2 ^ j) := by rw [pow_succ]; ring
    rw [he, show m + (j + 1) = (m + j) + 1 by omega, hc, ih]

theorem samples_dyadic_eventually {a : ℕ → ℕ → ℝ} (hc : Compatible a) (m k : ℕ) :
    samples a (coordinate m k) =ᶠ[atTop] (fun _ ↦ a m k) := by
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [samples, index_coordinate hn]
  have h := compatible_refinement hc m k (n - m)
  simpa only [Nat.add_sub_of_le hn] using h

theorem extension_dyadic {a : ℕ → ℕ → ℝ} (hc : Compatible a) (hb : LocalBound a)
    (m k : ℕ) : extension a (coordinate m k) = a m k :=
  tendsto_nhds_unique (samples_tendsto_extension hc hb _)
    (tendsto_const_nhds.congr' (samples_dyadic_eventually hc m k).symm)

end PerronWright.DyadicGeometricApproximation
