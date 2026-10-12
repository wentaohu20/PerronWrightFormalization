import PerronWright.Probability.DyadicGeometricApproximation

/-!
# Continuous extension of compatible dyadic samples

Continuity is proved from the actual floor inequalities and the geometric
neighbor bound. No continuity of the limit is included in the assumptions.
The Gaussian-law construction supplies both deterministic hypotheses.
-/

open Filter Topology
open scoped Topology NNReal

noncomputable section

namespace PerronWright.DyadicGeometricExtension

open DyadicFloorGeometry DyadicGeometricApproximation

theorem index_near {n : ℕ} {t s : ℝ≥0}
    (h : |(t : ℝ) - (s : ℝ)| * (2 : ℝ) ^ n < 1) :
    index n t = index n s ∨ index n t + 1 = index n s ∨
      index n s + 1 = index n t := by
  have hp : 0 ≤ (2 : ℝ) ^ n := by positivity
  have ht := index_le_scaled n t
  have hs := index_le_scaled n s
  have ht' := scaled_lt_index_add_one n t
  have hs' := scaled_lt_index_add_one n s
  have habs0 := neg_abs_le ((t : ℝ) - (s : ℝ))
  have habs1 := le_abs_self ((t : ℝ) - (s : ℝ))
  have hlo : (index n t : ℝ) < (index n s : ℝ) + 2 := by nlinarith
  have hhi : (index n s : ℝ) < (index n t : ℝ) + 2 := by nlinarith
  have hlo' : index n t < index n s + 2 := by exact_mod_cast hlo
  have hhi' : index n s < index n t + 2 := by exact_mod_cast hhi
  omega

theorem samples_near_bound {a : ℕ → ℕ → ℝ} {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ n k : ℕ, k < M * 2 ^ n → ‖a n (k + 1) - a n k‖ ≤ C * ratio ^ n)
    {n : ℕ} {t s : ℝ≥0} (ht : (t : ℝ) < M) (hs : (s : ℝ) < M)
    (h : |(t : ℝ) - (s : ℝ)| * (2 : ℝ) ^ n < 1) :
    dist (samples a t n) (samples a s n) ≤ C * ratio ^ n := by
  rcases index_near h with he | he | he
  · simp only [samples, he, dist_self]
    exact mul_nonneg hC (pow_nonneg ratio_nonneg _)
  · have hh := hb n (index n t) (index_lt_window ht n)
    simpa only [samples, ← he, dist_eq_norm, norm_sub_rev] using hh
  · have hh := hb n (index n s) (index_lt_window hs n)
    simpa only [samples, ← he, dist_eq_norm] using hh

theorem continuous_extension {a : ℕ → ℕ → ℝ}
    (hc : Compatible a) (hb : LocalBound a) : Continuous (extension a) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt ((t : ℝ) + 1)
  obtain ⟨C, hC, hbound⟩ := hb M
  let D : ℝ := C * (1 + 2 / (1 - ratio))
  have hlim : Tendsto (fun n : ℕ ↦ D * ratio ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_nonneg ratio_lt_one).const_mul D
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  let δ : ℝ := min 1 (1 / (2 : ℝ) ^ n)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hdist : dist s t = |(s : ℝ) - (t : ℝ)| := rfl
  have hsmall : |(s : ℝ) - (t : ℝ)| < 1 := by
    rw [hdist] at hs
    exact hs.trans_le (min_le_left _ _)
  have hsm : (s : ℝ) < M := by
    have ha := le_abs_self ((s : ℝ) - (t : ℝ))
    linarith
  have htm : (t : ℝ) < M := by linarith
  have hscaled : |(s : ℝ) - (t : ℝ)| * (2 : ℝ) ^ n < 1 := by
    have hh : |(s : ℝ) - (t : ℝ)| < 1 / (2 : ℝ) ^ n := by
      rw [hdist] at hs
      exact hs.trans_le (min_le_right _ _)
    exact (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).mp hh
  have hsbound := samples_extension_distance hc hb hC hbound hsm n
  have htbound := samples_extension_distance hc hb hC hbound htm n
  have hnbound := samples_near_bound hC hbound hsm htm hscaled
  calc
    dist (extension a s) (extension a t) ≤
        dist (extension a s) (samples a s n) +
          dist (samples a s n) (samples a t n) +
          dist (samples a t n) (extension a t) := dist_triangle4 _ _ _ _
    _ ≤ C * ratio ^ n / (1 - ratio) + C * ratio ^ n +
        C * ratio ^ n / (1 - ratio) := by
      rw [dist_comm (extension a s)]
      exact add_le_add (add_le_add hsbound hnbound) htbound
    _ = D * ratio ^ n := by dsimp [D]; ring
    _ < ε := hn

/-- A proved continuous realization matching every prescribed dyadic value. -/
theorem exists_continuous_extension {a : ℕ → ℕ → ℝ}
    (hc : Compatible a) (hb : LocalBound a) :
    ∃ F : ℝ≥0 → ℝ, Continuous F ∧ ∀ n k, F (coordinate n k) = a n k :=
  ⟨extension a, continuous_extension hc hb, extension_dyadic hc hb⟩

end PerronWright.DyadicGeometricExtension
