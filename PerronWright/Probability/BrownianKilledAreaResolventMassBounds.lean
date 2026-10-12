import PerronWright.Probability.BrownianRawAreaMomentBounds
import PerronWright.Probability.BrownianKilledAreaMomentResolvent
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Actual finite duration-resolvent moment measures

The raw Gaussian area scaling gives polynomial moment-mass bounds.
Positive duration Laplace weights integrate those bounds by the Gamma
integral. Thus every actual killed area moment resolvent has finite total
state mass, without a Green formula or pointwise resolvent hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledAreaResolventMassBounds

open BrownianRawAreaMomentBounds BrownianKilledAreaMomentKernel
open BrownianKilledAreaMomentResolvent PositiveTimeConvolutionLaplace

theorem integrable_power_laplace (q : ℝ) (hq : 0 ≤ q) (p : ℝ) (hp : 0 < p) :
    Integrable (fun t : ℝ ↦ t^q*Real.exp (-p*t)) (volume.restrict (Ioi 0)) := by
  by_contra hi
  have he : (∫ t : ℝ in Ioi 0, t^q*Real.exp (-p*t)) =
      (1/p)^(q+1)*Real.Gamma (q+1) := by
    simpa only [add_sub_cancel_right,← neg_mul] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < q+1 by linarith) hp
  rw [integral_undef hi] at he
  have hpos : 0 < (1/p)^(q+1)*Real.Gamma (q+1) :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith))
  linarith

def weightedMassBound (n : ℕ) (p x t : ℝ) : ℝ :=
  Real.exp (-p*t)*(2 : ℝ)^(n-1)*
    (t^n*|x|^n+(t^(3/2 : ℝ))^n*rawAbsoluteMoment n)

theorem weightedMassBound_nonneg (n : ℕ) (p x t : ℝ) (ht : 0 ≤ t) :
    0 ≤ weightedMassBound n p x t := by
  unfold weightedMassBound
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (by positivity))
    (add_nonneg (mul_nonneg (pow_nonneg ht _) (by positivity))
      (mul_nonneg (pow_nonneg (Real.rpow_nonneg ht _) _) (rawAbsoluteMoment_nonneg n)))

theorem integrable_weightedMassBound (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    Integrable (weightedMassBound n p x) (volume.restrict (Ioi 0)) := by
  have h1 := (integrable_power_laplace (n : ℝ) (by positivity) p hp).const_mul (|x|^n)
  have h2 := (integrable_power_laplace ((3/2 : ℝ)*(n : ℝ)) (by positivity) p hp).const_mul
    (rawAbsoluteMoment n)
  apply ((h1.add h2).const_mul ((2 : ℝ)^(n-1))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (2 : ℝ)^(n-1)*(|x|^n*(t^(n : ℝ)*Real.exp (-p*t))+
    rawAbsoluteMoment n*(t^((3/2 : ℝ)*(n : ℝ))*Real.exp (-p*t))) =
      weightedMassBound n p x t
  rw [Real.rpow_natCast,Real.rpow_mul_natCast ht.le]
  unfold weightedMassBound
  ring

theorem moment_mass_enn_bound (n : ℕ) (x : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    momentLaw 0 n T x univ ≤ ENNReal.ofReal ((2 : ℝ)^(n-1)*
      ((T : ℝ)^n*|x|^n+((T : ℝ)^(3/2 : ℝ))^n*rawAbsoluteMoment n)) := by
  have he := ENNReal.ofReal_le_ofReal (momentLaw_real_mass_bound 0 x T hT n)
  simp only [sub_zero,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
  exact he

theorem resolvent_total_mass_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    (∫⁻ y : ℝ, resolvent n p x y) ≠ ⊤ := by
  have he := resolvent_lintegral_eq_actual_momentLaw n p x
    (measurable_const : Measurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)))
  simp only [mul_one,lintegral_one] at he
  rw [he]
  have hb : (∫⁻ T : ℝ in Ioi 0, laplaceWeight p T*momentLaw 0 n (Real.toNNReal T) x univ) ≤
      ∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (weightedMassBound n p x T) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have h := mul_le_mul' (le_rfl : laplaceWeight p T ≤ laplaceWeight p T)
      (moment_mass_enn_bound n x (Real.toNNReal T)
      (Real.toNNReal_pos.mpr hT))
    simpa only [laplaceWeight,← ENNReal.ofReal_mul (Real.exp_nonneg _),
      Real.coe_toNNReal _ hT.le,weightedMassBound,mul_assoc] using h
  have hf : (∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (weightedMassBound n p x T)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weightedMassBound n p hp x)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
          exact weightedMassBound_nonneg n p x T hT.le)]
    exact ENNReal.ofReal_ne_top
  exact ne_of_lt (hb.trans_lt (lt_top_iff_ne_top.mpr hf))

def resolventMeasure (n : ℕ) (p x : ℝ) : Measure ℝ :=
  volume.withDensity (fun y ↦ resolvent n p x y)

theorem resolventMeasure_isFinite (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    IsFiniteMeasure (resolventMeasure n p x) :=
  isFiniteMeasure_withDensity (resolvent_total_mass_ne_top n p hp x)

end PerronWright.BrownianKilledAreaResolventMassBounds
