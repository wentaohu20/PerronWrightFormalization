import PerronWright.Probability.CriticalTuplePrefactor
import PerronWright.Probability.CriticalScalarField

/-!
# Exact critical-size scaling for the finite deterministic prefactor

The raw paper time is used, without clipping. Uniform lower size windows
supply the component-size thresholds. All statements here are scalar
algebra, real analysis, or finite-product estimates, independent of a model.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FiniteIrreducibleCriticalPrefactorScaling

def rawTime (lambda : ℝ) (n : ℕ) : ℝ :=
  1 + lambda * (n : ℝ) ^ (-(1/3 : ℝ))

def normalizedSize (n k : ℕ) : ℝ := (k : ℝ) / (n : ℝ) ^ (2/3 : ℝ)

theorem rawTime_tendsto (lambda : ℝ) :
    Tendsto (rawTime lambda) atTop (𝓝 1) :=
  CriticalScaling.raw_time_tendsto lambda

theorem rawTime_pos_eventually (lambda : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < rawTime lambda n :=
  (rawTime_tendsto lambda).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))

theorem normalizedSize_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < normalizedSize n k :=
  div_pos (Nat.cast_pos.mpr hk) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)

theorem size_upper_of_normalized {n k : ℕ} (hn : 0 < n) {b : ℝ}
    (hb : normalizedSize n k ≤ b) :
    (k : ℝ) ≤ b * (n : ℝ) ^ (2/3 : ℝ) :=
  (div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)).mp hb

theorem size_lower_of_normalized {n k : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : a ≤ normalizedSize n k) :
    a * (n : ℝ) ^ (2/3 : ℝ) ≤ (k : ℝ) :=
  (le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)).mp ha

/-- One common threshold covers every integer size in a positive normalized
window, not just a specified floor sequence. -/
theorem eventually_all_sizes_ge (a : ℝ) (ha : 0 < a) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ normalizedSize n k → K ≤ k := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop ((K : ℝ) / a)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 k hk
  have h := mul_le_mul_of_nonneg_left hn ha.le
  rw [mul_div_cancel₀ _ ha.ne'] at h
  exact_mod_cast h.trans (size_lower_of_normalized (by omega) hk)

/-- The exact Gaussian exponent on the normalized integer-size scale. -/
theorem rawTime_square_size (lambda : ℝ) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (rawTime lambda n - 1)^2 * (k : ℝ) = lambda^2 * normalizedSize n k := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA : (n : ℝ)^(2/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
  have hp := CriticalScalarField.twoThird_mul_negativeThird_sq hnR
  have hscale : ((n : ℝ)^(-(1/3 : ℝ)))^2 = ((n : ℝ)^(2/3 : ℝ))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hA).mpr
    simpa only [mul_comm] using hp
  unfold rawTime normalizedSize
  rw [show 1 + lambda*(n : ℝ)^(-(1/3 : ℝ))-1 =
    lambda*(n : ℝ)^(-(1/3 : ℝ)) by ring, mul_pow, hscale]
  ring

/-- The enumeration square-root time window follows from the actual
integer size bound and literal critical time. -/
theorem rawTime_sqrt_bound (lambda b : ℝ) (hb : 0 ≤ b)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : normalizedSize n k ≤ b) :
    Real.sqrt (k : ℝ) * |rawTime lambda n - 1| ≤ Real.sqrt b * |lambda| := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : |rawTime lambda n - 1| = |lambda| * (n : ℝ)^(-(1/3 : ℝ)) := by
    unfold rawTime
    simp only [add_sub_cancel_left, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hnR _)]
  have hp := CriticalScalarField.twoThird_mul_negativeThird_sq hnR
  have hsquare : (Real.sqrt (k : ℝ) * |rawTime lambda n - 1|)^2 ≤
      (Real.sqrt b * |lambda|)^2 := by
    rw [ht, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), mul_pow, Real.sq_sqrt hb]
    calc
      (k : ℝ) * (|lambda|^2 * ((n : ℝ)^(-(1/3 : ℝ)))^2) ≤
          b*(n : ℝ)^(2/3 : ℝ) * (|lambda|^2 * ((n : ℝ)^(-(1/3 : ℝ)))^2) :=
        mul_le_mul_of_nonneg_right (size_upper_of_normalized hn hk) (by positivity)
      _ = b * |lambda|^2 := by
        calc
          _ = b * |lambda|^2 * ((n : ℝ)^(2/3 : ℝ) *
            ((n : ℝ)^(-(1/3 : ℝ)))^2) := by ring
          _ = _ := by rw [hp, mul_one]
  nlinarith [Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg b, abs_nonneg lambda,
    mul_nonneg (Real.sqrt_nonneg (k : ℝ)) (abs_nonneg (rawTime lambda n - 1)),
    mul_nonneg (Real.sqrt_nonneg b) (abs_nonneg lambda)]

/-- A finite product estimate, with no positivity assumption on its factors. -/
theorem abs_prod_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : ∀ i ∈ s, |f i - 1| ≤ δ) :
    |(∏ i ∈ s, f i) - 1| ≤ (1+δ)^s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hrest := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      have hfa : |f i| ≤ 1+δ := by
        have h := abs_add_le (f i - 1) 1
        simp only [sub_add_cancel, abs_one] at h
        linarith
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      calc
        |f i * (∏ j ∈ s, f j) - 1| =
            |f i * ((∏ j ∈ s, f j) - 1) + (f i - 1)| := by congr 1; ring
        _ ≤ |f i| * |(∏ j ∈ s, f j) - 1| + |f i - 1| := by
          simpa only [abs_mul] using abs_add_le
            (f i * ((∏ j ∈ s, f j) - 1)) (f i - 1)
        _ ≤ (1+δ) * ((1+δ)^s.card-1) + δ :=
          add_le_add (mul_le_mul hfa hrest (abs_nonneg _) (by linarith)) hfi
        _ = (1+δ)^(s.card+1)-1 := by rw [pow_succ]; ring

/-- A tolerance for all q factors is selected before any size or surplus. -/
theorem exists_product_tolerance (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : Fin q → ℝ, (∀ i, |f i-1| ≤ δ) →
      |(∏ i, f i)-1| ≤ ε := by
  have ht : Tendsto (fun δ : ℝ ↦ (1+δ)^q-1) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ ↦ (1+δ)^q-1) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto
  obtain ⟨d, hd, hdball⟩ := Metric.eventually_nhds_iff.mp
    (ht.eventually (Iio_mem_nhds hε))
  refine ⟨d/2, by linarith, ?_⟩
  intro f hf
  have hsmall : (1+d/2)^q-1 < ε := hdball (by
    simp only [Real.dist_eq, sub_zero, abs_of_pos (show (0 : ℝ) < d/2 by linarith)]
    linarith)
  exact (abs_prod_sub_one_le Finset.univ f (by linarith)
    (fun i _ ↦ hf i)).trans (by simpa using hsmall.le)

end PerronWright.FiniteIrreducibleCriticalPrefactorScaling

