import PerronWright.Probability.BrownianKilledAreaSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Literal area-power insertion on continuous surviving paths

The first identity is a pathwise polynomial fundamental theorem of calculus.
Its application to the actual boundary-shifted Brownian path integral is
then expressed using nonnegative integrals, without a moment-finiteness
condition.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentGeometry

open BrownianPathLaw BrownianPathIndependentIncrements BrownianBridgeCyclicArea
open ContinuousPathFirstPassage BrownianKilledAreaGeometry BrownianKilledSemigroup

theorem continuous_tailIntegral {g : ℝ → ℝ} (hg : Continuous g) (T : ℝ) :
    Continuous (fun s : ℝ ↦ ∫ r in s..T, g r) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable s T)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).continuousAt

theorem continuous_integral_power_insertion {g : ℝ → ℝ} (hg : Continuous g)
    (T : ℝ) (n : ℕ) :
    (∫ r in (0 : ℝ)..T, g r) ^ (n + 1) =
      ((n + 1 : ℕ) : ℝ) *
        ∫ s in (0 : ℝ)..T, g s * (∫ r in s..T, g r) ^ n := by
  have hc := continuous_tailIntegral hg T
  have hd (s : ℝ) : HasDerivAt
      (fun s : ℝ ↦ (∫ r in s..T, g r) ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * (g s * (∫ r in s..T, g r) ^ n)) s := by
    have h := (intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable s T)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).pow (n + 1)
    apply h.congr_deriv
    simp only [Nat.add_sub_cancel]
    ring
  have hi : IntervalIntegrable
      (fun s : ℝ ↦ -((n + 1 : ℕ) : ℝ) * (g s * (∫ r in s..T, g r) ^ n))
      volume 0 T :=
    (continuous_const.mul (hg.mul (hc.pow n))).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s) hi
  rw [intervalIntegral.integral_const_mul] at h
  have hn : n + 1 ≠ 0 := by omega
  simp only [intervalIntegral.integral_same,zero_pow hn,zero_sub] at h
  linarith only [h]

theorem shiftedArea_eq_intervalIntegral (level x : ℝ) (T : ℝ≥0) (f : Path) :
    shiftedArea level x T f =
      ∫ r in (0 : ℝ)..(T : ℝ), (x-level)+f (Real.toNNReal r) := by
  have hc : Continuous (fun r : ℝ ↦ f (Real.toNNReal r)) :=
    (continuous_path f).comp continuous_real_toNNReal
  unfold shiftedArea pathArea
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (hc.intervalIntegrable 0 T),intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul]

def remainingArea (level x : ℝ) (T : ℝ≥0) (f : Path) (s : ℝ) : ℝ :=
  ∫ r in s..(T : ℝ), (x-level)+f (Real.toNNReal r)

theorem continuous_remainingArea (level x : ℝ) (T : ℝ≥0) (f : Path) :
    Continuous (remainingArea level x T f) :=
  continuous_tailIntegral
    (continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)) T

theorem remainingArea_eq_difference (level x : ℝ) (T : ℝ≥0) (f : Path)
    {s : ℝ} (hs : 0 ≤ s) :
    remainingArea level x T f s =
      shiftedArea level x T f-shiftedArea level x (Real.toNNReal s) f := by
  have hc : Continuous (fun r : ℝ ↦ (x-level)+f (Real.toNNReal r)) :=
    continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)
  rw [shiftedArea_eq_intervalIntegral,shiftedArea_eq_intervalIntegral,Real.coe_toNNReal _ hs]
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s T)
  change (∫ r in s..(T : ℝ), (x-level)+f (Real.toNNReal r)) = _
  linarith only [h]

theorem remainingArea_eq_future (level x : ℝ) (s t : ℝ≥0) (f : Path) :
    remainingArea level x (s+t) f s =
      shiftedArea level (x+f s) t (futurePath s f) := by
  rw [remainingArea_eq_difference level x (s+t) f s.coe_nonneg,
    Real.toNNReal_coe,shiftedArea_add]
  ring

theorem remainingArea_nonneg_of_survival (level x : ℝ) (T : ℝ≥0) (f : Path)
    (hf : f ∈ survival (level-x) T) {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) :
    0 ≤ remainingArea level x T f s := by
  apply intervalIntegral.integral_nonneg hs.2
  intro r hr
  have hs' := ((mem_survival_iff (level-x) T f).mp hf) (Real.toNNReal r)
    (Real.toNNReal_le_iff_le_coe.mpr hr.2)
  change 0 ≤ (x-level)+f (Real.toNNReal r)
  linarith

theorem shiftedArea_power_insertion (level x : ℝ) (T : ℝ≥0) (f : Path) (n : ℕ) :
    shiftedArea level x T f ^ (n + 1) =
      ((n + 1 : ℕ) : ℝ) * ∫ s in (0 : ℝ)..(T : ℝ),
        ((x-level)+f (Real.toNNReal s)) * remainingArea level x T f s ^ n := by
  rw [shiftedArea_eq_intervalIntegral]
  exact continuous_integral_power_insertion
    (continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)) T n

/-- The pathwise insertion formula as a nonnegative integral, on the
actual survival event.  Only continuous deterministic path functions are
integrated in the intermediate real-valued calculation. -/
theorem ofReal_shiftedArea_power_insertion (level x : ℝ) (T : ℝ≥0) (f : Path) (n : ℕ)
    (hf : f ∈ survival (level-x) T) :
    ENNReal.ofReal (shiftedArea level x T f) ^ (n + 1) =
      ((n + 1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal ((x-level)+f (Real.toNNReal s)) *
          ENNReal.ofReal (remainingArea level x T f s) ^ n := by
  have hh {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (T : ℝ)) :
      0 ≤ (x-level)+f (Real.toNNReal s) := by
    have h := ((mem_survival_iff (level-x) T f).mp hf) (Real.toNNReal s)
      (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    linarith
  have hc : Continuous (fun s : ℝ ↦
      ((x-level)+f (Real.toNNReal s))*remainingArea level x T f s ^ n) :=
    (continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)).mul
      ((continuous_remainingArea level x T f).pow n)
  have hi : IntegrableOn (fun s : ℝ ↦
      ((x-level)+f (Real.toNNReal s))*remainingArea level x T f s ^ n)
      (Ioc (0 : ℝ) (T : ℝ)) volume := (hc.intervalIntegrable 0 T).1
  have hnn : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      0 ≤ ((x-level)+f (Real.toNNReal s))*remainingArea level x T f s ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (hh hs) (pow_nonneg
      (remainingArea_nonneg_of_survival level x T f hf ⟨hs.1.le,hs.2⟩) n)
  rw [← ENNReal.ofReal_pow (shiftedArea_nonneg_of_survival level x T f hf) (n+1),
    shiftedArea_power_insertion,ENNReal.ofReal_mul (Nat.cast_nonneg (n+1)),
    ENNReal.ofReal_natCast,intervalIntegral.integral_of_le T.coe_nonneg,
    ofReal_integral_eq_lintegral_ofReal hi hnn]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [ENNReal.ofReal_mul (hh hs),ENNReal.ofReal_pow
    (remainingArea_nonneg_of_survival level x T f hf ⟨hs.1.le,hs.2⟩) n]

theorem ofReal_shiftedArea_power_insertion_difference
    (level x : ℝ) (T : ℝ≥0) (f : Path) (n : ℕ)
    (hf : f ∈ survival (level-x) T) :
    ENNReal.ofReal (shiftedArea level x T f) ^ (n + 1) =
      ((n + 1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal ((x-level)+f (Real.toNNReal s)) *
          ENNReal.ofReal (shiftedArea level x T f-
            shiftedArea level x (Real.toNNReal s) f) ^ n := by
  rw [ofReal_shiftedArea_power_insertion level x T f n hf]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [remainingArea_eq_difference level x T f hs.1.le]

end PerronWright.BrownianKilledAreaMomentGeometry
