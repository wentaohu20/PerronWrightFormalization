import PerronWright.Probability.BrownianKilledAreaMomentDensityLaw
import PerronWright.Probability.BrownianKilledAreaMomentFiniteness

/-! # Genuine boundary support and finite mass of all moment densities

The canonical Gaussian-insertion density vanishes pointwise at every
nonpositive target. It also vanishes at every nonpositive initial state
for positive duration. Its total integral is finite because it is the
proved density of the actual finite Brownian path moment measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentDensityBoundary

open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentDensity
open BrownianKilledAreaMomentDensityLaw BrownianKilledAreaMomentFiniteness

theorem density_zero_of_nonpos_target (n : ℕ) (T : ℝ≥0) (x y : ℝ) (hy : y ≤ 0) :
    density n (T,(x,y)) = 0 := by
  induction n generalizing T x with
  | zero =>
    simp only [density_zero,BrownianPositiveKilledEndpoint.density,
      BrownianPositiveKilledEndpoint.densityReal,
      indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from not_lt.mpr hy),ENNReal.ofReal_zero]
  | succ n ih =>
    rw [density_succ]
    simp only [ih,mul_zero,lintegral_zero]

theorem density_zero_of_nonpos_initial (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (x y : ℝ) (hx : x ≤ 0) : density n (T,(x,y)) = 0 := by
  cases n with
  | zero =>
    rw [density_zero,BrownianPositiveKilledKernel.density_eq_zero_of_nonpos x hx T hT]
    rfl
  | succ n =>
    rw [density_succ]
    suffices he : (∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          density n (T-Real.toNNReal r,(z,y))) = 0 by rw [he,mul_zero]
    rw [← lintegral_zero (μ := volume.restrict (Ioo (0 : ℝ) (T : ℝ)))]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [BrownianPositiveKilledKernel.density_eq_zero_of_nonpos x hx _
      (Real.toNNReal_pos.mpr hr.1)]
    simp only [Pi.zero_apply,zero_mul,lintegral_zero]

theorem density_totalMass (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    (∫⁻ y, density n (T,(x,y))) = momentLaw 0 n T x univ := by
  have he := momentLaw_lintegral_eq_density n T hT x
    (measurable_const : Measurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)))
  simpa only [lintegral_one,mul_one] using he.symm

theorem density_lintegral_ne_top (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    (∫⁻ y, density n (T,(x,y))) ≠ ∞ := by
  rw [density_totalMass n T hT x]
  exact measure_ne_top (momentLaw 0 n T x) univ

end PerronWright.BrownianKilledAreaMomentDensityBoundary
