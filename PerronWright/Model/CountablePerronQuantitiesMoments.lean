import PerronWright.Model.CountablePerronQuantitiesApproximation

/-!
# Convergence of literal finite-law Perron moments

The actual finite-law normalized positive functions are uniformly bounded
by the literal upper/lower kernel ratio.  Dominated convergence for the
original measure and the full atomic absolute-variation estimate give
convergence of every power moment, in particular the paper's `α` and `β`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

namespace PerronWright.CountableKernel

theorem summable_weighted_bounded_pow (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (f : ℕ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ C) (m : ℕ) :
    Summable (fun a ↦ w a * f a ^ m) := by
  apply (hs.summable.mul_left (C ^ m)).of_nonneg_of_le
  · intro a
    exact mul_nonneg (hw a) (pow_nonneg (hf a).1 m)
  · intro a
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hf a).1 (hf a).2 m) (hw a)

theorem atomic_bounded_moment_error_le (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (f : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ C) (m : ℕ) :
    |(∑' a, w a * f a ^ m) - ∫ a, f a ^ m ∂M.mu| ≤
      C ^ m * ∑' a, |w a - M.mu.real {a}| := by
  have habs := (hs.summable.sub M.atomMass_hasSum.summable).abs
  have hdom := habs.mul_left (C ^ m)
  have hb : ∀ a, ‖(w a - M.mu.real {a}) * f a ^ m‖ ≤ C ^ m * |w a - M.mu.real {a}| := by
    intro a
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg (hf a).1 m)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hf a).1 (hf a).2 m) (abs_nonneg (w a - M.mu.real {a}))
  have hd : Summable (fun a ↦ ‖(w a - M.mu.real {a}) * f a ^ m‖) :=
    hdom.of_nonneg_of_le (fun a ↦ norm_nonneg _) hb
  have hwf := summable_weighted_bounded_pow w hw hs f hC hf m
  have hmf := summable_weighted_bounded_pow (fun a ↦ M.mu.real {a})
    (fun a ↦ (M.atomMass_pos a).le) M.atomMass_hasSum f hC hf m
  rw [M.integral_eq_tsum_atom, ← hwf.tsum_sub hmf]
  simp_rw [← sub_mul]
  calc
    |∑' a, (w a - M.mu.real {a}) * f a ^ m| ≤
        ∑' a, ‖(w a - M.mu.real {a}) * f a ^ m‖ := norm_tsum_le_tsum_norm hd
    _ ≤ ∑' a, C ^ m * |w a - M.mu.real {a}| := hd.tsum_le_tsum hb hdom
    _ = C ^ m * ∑' a, |w a - M.mu.real {a}| := tsum_mul_left

theorem atomic_bounded_moments_tendsto (M : CountableKernel) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0))
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n a, 0 ≤ f n a ∧ f n a ≤ C)
    (ht : ∀ a, Tendsto (fun n ↦ f n a) atTop (nhds (g a))) (m : ℕ) :
    Tendsto (fun n ↦ ∑' a, w n a * f n a ^ m) atTop (nhds (∫ a, g a ^ m ∂M.mu)) := by
  have hi : Tendsto (fun n ↦ ∫ a, f n a ^ m ∂M.mu) atTop (nhds (∫ a, g a ^ m ∂M.mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ C ^ m)
      (fun n ↦ (measurable_of_countable _).aestronglyMeasurable) (integrable_const _) _ _
    · intro n
      filter_upwards [] with a
      rw [Real.norm_of_nonneg (pow_nonneg (hf n a).1 m)]
      exact pow_le_pow_left₀ (hf n a).1 (hf n a).2 m
    · filter_upwards [] with a
      exact (ht a).pow m
  have he : Tendsto (fun n ↦ (∑' a, w n a * f n a ^ m) - ∫ a, f n a ^ m ∂M.mu)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n ↦ norm_nonneg _)
      (fun n ↦ M.atomic_bounded_moment_error_le (w n) (hw n) (hs n) (f n) hC (hf n) m)
      (by simpa using herr.const_mul (C ^ m))
  have h := he.add hi
  simpa only [sub_add_cancel, zero_add] using h

def finitePerronMoment (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (m : ℕ) : ℝ :=
  ∑' a, w a * M.finitePerronFunction w hw hs s hzero hlower hlo a ^ m

/-- All literal finite-law Perron power moments converge, not merely a
chosen moment sequence supplied as an approximation interface. -/
theorem finitePerronMoment_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0)) (m : ℕ) :
    Tendsto (fun n ↦ M.finitePerronMoment (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo m)
      atTop (nhds (∫ a, (M.perronVector hM a) ^ m ∂M.mu)) := by
  apply M.atomic_bounded_moments_tendsto w hw hs herr _ _
    (div_nonneg M.upper_nonneg hlower.le)
  · intro n a
    have hb := M.finitePerronFunction_bounds (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo a
    exact ⟨hb.1.le, hb.2⟩
  · exact M.finitePerronFunction_tendsto hM w hw hs s hzero hlower hlo herr

theorem finitePerronAlpha_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0)) :
    Tendsto (fun n ↦ M.finitePerronMoment (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo 2)
      atTop (nhds (M.alpha hM)) := M.finitePerronMoment_tendsto hM w hw hs s hzero hlower hlo herr 2

theorem finitePerronBeta_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0)) :
    Tendsto (fun n ↦ M.finitePerronMoment (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo 3)
      atTop (nhds (M.beta hM)) := M.finitePerronMoment_tendsto hM w hw hs s hzero hlower hlo herr 3

end PerronWright.CountableKernel
