import PerronWright.Probability.ProjectiveExponential

/-!
# Literal BJR scale for the proved projective exponential moments

The arithmetic implications of `k ≤ C₀ n^(2/3)` are proved explicitly,
including the case of bounded or mixed component sizes.
-/

open MeasureTheory Filter Topology
open scoped Topology Real

noncomputable section

namespace PerronWright.ProfileScaleMatched

open ConnectedTypeLaw ProjectiveKernel ProjectiveExponential

/-- The two elementary bounds needed by scale matching. -/
theorem coefficient_bounds {k n C₀ A : ℝ} (hk : 0 < k) (hn : 0 < n)
    (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hsize : k ≤ C₀ * n ^ (2 / 3 : ℝ)) :
    A * k / n ≤ (A * C₀) * n ^ (-(1 / 3 : ℝ)) ∧
      A * k / n ≤ (A * C₀ ^ (3 / 2 : ℝ)) / Real.sqrt k := by
  have hfirst := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsize hA) hn.le
  have hexp : n ^ (2 / 3 : ℝ) / n = n ^ (-(1 / 3 : ℝ)) := by
    have he := Real.rpow_sub hn (2 / 3 : ℝ) 1
    norm_num only [Real.rpow_one] at he
    convert he.symm using 1
  have hfirst' : A * k / n ≤ (A * C₀) * n ^ (-(1 / 3 : ℝ)) := by
    calc
      _ ≤ A * (C₀ * n ^ (2 / 3 : ℝ)) / n := hfirst
      _ = (A * C₀) * (n ^ (2 / 3 : ℝ) / n) := by ring
      _ = _ := by rw [hexp]
  have hpow := Real.rpow_le_rpow hk.le hsize (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow hC₀ (Real.rpow_nonneg hn.le _),
    ← Real.rpow_mul hn.le] at hpow
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hpow
  have hkpow : k ^ (3 / 2 : ℝ) = k * Real.sqrt k := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hkpow] at hpow
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  refine ⟨hfirst', (le_div_iff₀ hsqrt).mpr ?_⟩
  calc
    (A * k / n) * Real.sqrt k = A * (k * Real.sqrt k) / n := by ring
    _ ≤ A * (C₀ ^ (3 / 2 : ℝ) * n) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA) hn.le
    _ = A * C₀ ^ (3 / 2 : ℝ) := by field_simp

/-- Actual projective exponential control at `A k/n`, with no
requirement that the component sizes themselves diverge. -/
theorem componentQuadratic_exponential_tendsto_one_bjr_scale
    {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) (L A B C₀ : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (k r N : ℕ → ℕ) (g : ℕ → C(S, ℝ))
    (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → C(S, ℝ))
    (hk : ∀ n, 0 < k n) (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (hs : ∀ n, Summable (fun j ↦ |a n j| * ‖f n j‖ ^ 2))
    (hbudget : ∀ n, ∑' j, |a n j| * ‖f n j‖ ^ 2 ≤ B)
    (hsize : ∀ᶠ n in atTop, (k n : ℝ) ≤ C₀ * (N n : ℝ) ^ (2 / 3 : ℝ))
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n)) :
    Tendsto (fun n ↦ ∫ p, Real.exp ((A * (k n : ℝ) / (N n : ℝ)) *
      |componentQuadratic M hM (hk n) (∑' j, a n j • square (f n j)) p|)
        ∂law M (g n) (k n) (r n) (hC n)) atTop (𝓝 1) := by
  let γ : ℕ → ℝ := fun n ↦ A * (k n : ℝ) / (N n : ℝ)
  have hγ (n : ℕ) : 0 ≤ γ n := by dsimp [γ]; positivity
  have hcoeff : ∀ᶠ n in atTop,
      γ n ≤ (A * C₀) * (N n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      γ n ≤ (A * C₀ ^ (3 / 2 : ℝ)) / Real.sqrt (k n : ℝ) := by
    filter_upwards [hsize] with n hn
    exact coefficient_bounds (by exact_mod_cast hk n) (by exact_mod_cast hN n)
      hC₀ hA hn
  have hup : Tendsto (fun n ↦ (A * C₀) * (N n : ℝ) ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul hp
  have hγt : Tendsto γ atTop (𝓝 0) := squeeze_zero'
    (Eventually.of_forall hγ) (hcoeff.mono (fun _ hn ↦ hn.1)) hup
  exact componentQuadratic_exponential_tendsto_one_scale_matched M hM R L
    (A * C₀ ^ (3 / 2 : ℝ)) B hL (mul_nonneg hA (Real.rpow_nonneg hC₀ _)) hB
    k r g a f γ hk hr hg hs hbudget hγ hγt (hcoeff.mono (fun _ hn ↦ hn.2)) hC

end PerronWright.ProfileScaleMatched
