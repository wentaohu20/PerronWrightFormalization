import PerronWright.Probability.CriticalSizeTuple
import PerronWright.Enumeration.FieldWeight
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Actual scalar fields on the literal critical time and size scales -/

open Filter Topology Asymptotics
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalScalarField

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual field `log t - (t-1)d` has a uniform linear norm bound
near one, obtained from the real logarithm derivative. -/
theorem exists_scalarField_norm_bound (M : CompactBJRModel S) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ t : ℝ, |t-1| < δ →
      ‖M.scalarField t‖ ≤ A * |t-1| := by
  have hO : (fun t : ℝ ↦ Real.log t - Real.log 1) =O[𝓝 (1 : ℝ)]
      (fun t : ℝ ↦ t-1) := (Real.differentiableAt_log (by norm_num)).isBigO_sub
  obtain ⟨C,hC⟩ := isBigO_iff.mp hO
  let A : ℝ := max C 1 + ‖M.degreeFunction‖
  have hA : 0 < A := by
    dsimp only [A]
    linarith [le_max_right C 1,norm_nonneg M.degreeFunction]
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨δ,A,hδ,hA,?_⟩
  intro t ht
  have hl : |Real.log t| ≤ max C 1 * |t-1| := by
    have h := hball (by simpa only [Real.dist_eq] using ht)
    simp only [Real.log_one,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (abs_nonneg _))
  apply (ContinuousMap.norm_le _ (mul_nonneg hA.le (abs_nonneg _))).mpr
  intro x
  rw [CompactBJRModel.scalarField_apply,Real.norm_eq_abs]
  have hd : |M.degreeFunction x| ≤ ‖M.degreeFunction‖ := by
    simpa only [Real.norm_eq_abs] using (M.degreeFunction.norm_coe_le_norm x)
  calc
    |Real.log t - (t-1)*M.degreeFunction x| ≤ |Real.log t| + |t-1| * |M.degreeFunction x| := by
      simpa only [Real.norm_eq_abs,abs_mul] using
        norm_sub_le (Real.log t) ((t-1)*M.degreeFunction x)
    _ ≤ max C 1 * |t-1| + |t-1| * ‖M.degreeFunction‖ :=
      add_le_add hl (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = A * |t-1| := by dsimp only [A]; ring

theorem twoThird_mul_negativeThird_sq {x : ℝ} (hx : 0 < x) :
    x^(2/3 : ℝ) * (x^(-(1/3 : ℝ)))^2 = 1 := by
  rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hx.le,← Real.rpow_add hx]
  norm_num

/-- A literal critical time stays in the enumeration's square-root
field scale uniformly over all bounded critical component sizes. -/
theorem sqrt_time_bound_eventually (N : ℕ → ℕ) (hN : ∀ m, 0 < N m)
    (hNt : Tendsto N atTop atTop) (lambda b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ m in atTop, ∀ k : ℕ, (k : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ) →
      Real.sqrt (k : ℝ) * |CriticalScaling.time lambda (N m)-1| ≤ Real.sqrt b * |lambda| := by
  filter_upwards [hNt.eventually (CriticalScaling.time_eq_raw_eventually lambda)] with m hm k hk
  have hn : (0 : ℝ) < N m := Nat.cast_pos.mpr (hN m)
  have ht : |CriticalScaling.time lambda (N m)-1| =
      |lambda| * (N m : ℝ)^(-(1/3 : ℝ)) := by
    rw [hm]
    simp only [add_sub_cancel_left,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hn _)]
  have hp := twoThird_mul_negativeThird_sq hn
  have hsquare : (Real.sqrt (k : ℝ) * |CriticalScaling.time lambda (N m)-1|)^2 ≤
      (Real.sqrt b * |lambda|)^2 := by
    rw [ht,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg k),mul_pow,Real.sq_sqrt hb]
    calc
      (k : ℝ) * (|lambda|^2 * ((N m : ℝ)^(-(1/3 : ℝ)))^2) ≤
          b*(N m : ℝ)^(2/3 : ℝ) * (|lambda|^2 * ((N m : ℝ)^(-(1/3 : ℝ)))^2) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = b * |lambda|^2 := by
        calc
          _ = b * |lambda|^2 * ((N m : ℝ)^(2/3 : ℝ) *
            ((N m : ℝ)^(-(1/3 : ℝ)))^2) := by ring
          _ = _ := by rw [hp,mul_one]
  nlinarith [Real.sqrt_nonneg (k : ℝ),Real.sqrt_nonneg b,abs_nonneg lambda,
    mul_nonneg (Real.sqrt_nonneg (k : ℝ)) (abs_nonneg (CriticalScaling.time lambda (N m)-1)),
    mul_nonneg (Real.sqrt_nonneg b) (abs_nonneg lambda)]

/-- No square-root field-radius condition is assumed for the physical
scalar field: it follows on the actual critical time and size window. -/
theorem exists_sqrt_scalarField_bound (M : CompactBJRModel S)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (lambda b : ℝ) (hb : 0 ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ m in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ) →
      Real.sqrt (k : ℝ) * ‖M.scalarField (CriticalScaling.time lambda (N m))‖ ≤ L := by
  obtain ⟨δ,A,hδ,hA,hbound⟩ := exists_scalarField_norm_bound M
  refine ⟨A * (Real.sqrt b * |lambda|),by positivity,?_⟩
  have htime := (CriticalScaling.time_tendsto lambda).comp hNt
  filter_upwards [htime.eventually (Metric.ball_mem_nhds 1 hδ),
    sqrt_time_bound_eventually N hN hNt lambda b hb] with m hm hscale k hk
  have ht : |CriticalScaling.time lambda (N m)-1| < δ := by
    simpa only [Metric.mem_ball,Real.dist_eq,Function.comp_def] using hm
  calc
    _ ≤ Real.sqrt (k : ℝ) * (A * |CriticalScaling.time lambda (N m)-1|) :=
      mul_le_mul_of_nonneg_left (hbound _ ht) (Real.sqrt_nonneg _)
    _ = A * (Real.sqrt (k : ℝ) * |CriticalScaling.time lambda (N m)-1|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hscale k hk) hA.le

end PerronWright.CriticalScalarField
