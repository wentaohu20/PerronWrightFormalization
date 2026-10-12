import PerronWright.Probability.FiniteIrreducibleNativeProfileAveraging
import PerronWright.Probability.FiniteIrreducibleCriticalPrefactorScaling

/-! # Actual varying critical times and native finite fields

The parameter is a genuine convergent real sequence. Its eventual boundedness
gives the square-root field bound on every integer size in the critical window.
The finite data adapter here supplies only its literal scalar field; no compact
regular-critical or positive-power assumption is used.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleVaryingCriticalTime

open FiniteIrreducibleCriticalPrefactorScaling

theorem eventually_parameter_bound (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, |ell n| ≤ |lambda| + 1 := by
  filter_upwards [hl.eventually (Metric.ball_mem_nhds lambda (by norm_num : (0 : ℝ) < 1))]
    with n hn
  have hd : |ell n - lambda| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have hh := abs_sub_le (ell n) lambda 0
  simp only [sub_zero] at hh
  linarith

theorem rawTime_tendsto (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) :
    Tendsto (fun n ↦ rawTime (ell n) n) atTop (𝓝 1) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_natCast_atTop_atTop
  simpa only [rawTime, Function.comp_apply, mul_zero, add_zero] using tendsto_const_nhds.add (hl.mul hp)

theorem eventually_time_eq_raw (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, CriticalScaling.time (ell n) n = rawTime (ell n) n := by
  filter_upwards [(rawTime_tendsto ell lambda hl).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  exact max_eq_left hn.le

theorem time_tendsto (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) :
    Tendsto (fun n ↦ CriticalScaling.time (ell n) n) atTop (𝓝 1) := by
  apply (rawTime_tendsto ell lambda hl).congr'
  exact (eventually_time_eq_raw ell lambda hl).mono (fun _ h ↦ h.symm)

theorem eventually_time_abs_le_two (ell : ℕ → ℝ) (lambda : ℝ)
    (hl : Tendsto ell atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, |CriticalScaling.time (ell n) n| ≤ 2 := by
  have hh := (time_tendsto ell lambda hl).abs
  simp only [abs_one] at hh
  exact (hh.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ h ↦ h.le)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The actual native field stays in a fixed enumeration scale. -/
theorem exists_native_scalarField_bound (M : FiniteIrreducibleModel S)
    (ell : ℕ → ℝ) (lambda C : ℝ) (hl : Tendsto ell atTop (𝓝 lambda)) (hC : 0 ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      Real.sqrt (k : ℝ) * ‖M.bjrModel.scalarField (CriticalScaling.time (ell n) n)‖ ≤ L := by
  obtain ⟨δ, A, hδ, hA, hbound⟩ := CriticalScalarField.exists_scalarField_norm_bound M.bjrModel
  refine ⟨A * (Real.sqrt C * (|lambda| + 1)), by positivity, ?_⟩
  filter_upwards [(time_tendsto ell lambda hl).eventually (Metric.ball_mem_nhds 1 hδ),
    eventually_time_eq_raw ell lambda hl, eventually_parameter_bound ell lambda hl,
    eventually_ge_atTop (1 : ℕ)] with n hn hraw hpar hn1
  intro k hk
  have hnpos : 0 < n := by omega
  have ht : |CriticalScaling.time (ell n) n - 1| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have hkn : normalizedSize n k ≤ C :=
    (div_le_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _)).mpr hk
  have hs := rawTime_sqrt_bound (ell n) C hC hnpos k hkn
  rw [← hraw] at hs
  calc
    _ ≤ Real.sqrt (k : ℝ) * (A * |CriticalScaling.time (ell n) n - 1|) :=
      mul_le_mul_of_nonneg_left (hbound _ ht) (Real.sqrt_nonneg _)
    _ = A * (Real.sqrt (k : ℝ) * |CriticalScaling.time (ell n) n - 1|) := by ring
    _ ≤ A * (Real.sqrt C * |ell n|) := mul_le_mul_of_nonneg_left hs hA.le
    _ ≤ _ := by gcongr

end PerronWright.FiniteIrreducibleVaryingCriticalTime
