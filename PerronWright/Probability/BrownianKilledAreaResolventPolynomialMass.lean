import PerronWright.Probability.BrownianKilledAreaResolventMassBounds

/-! # Actual polynomial state-mass bounds for killed-area resolvents

The proved Gaussian moment bound is integrated explicitly in duration.
It gives a polynomial in the initial state, and every positive exponential
state weight integrates that true mass. No two-state integrability premise
or Green-moment formula is introduced.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledAreaResolventPolynomialMass

open BrownianKilledAreaResolventMassBounds BrownianKilledAreaMomentResolvent
open BrownianKilledAreaMomentKernel BrownianRawAreaMomentBounds PositiveTimeConvolutionLaplace

def massPolynomialBound (n : ℕ) (p x : ℝ) : ℝ :=
  (2 : ℝ)^(n-1)*((1/p)^((n : ℝ)+1)*Real.Gamma ((n : ℝ)+1)*|x|^n+
    rawAbsoluteMoment n*(1/p)^((3/2 : ℝ)*(n : ℝ)+1)*Real.Gamma ((3/2 : ℝ)*(n : ℝ)+1))

theorem integral_weightedMassBound_eq (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    (∫ t : ℝ in Ioi 0, weightedMassBound n p x t) = massPolynomialBound n p x := by
  have h1 := (integrable_power_laplace (n : ℝ) (by positivity) p hp).const_mul (|x|^n)
  have h2 := (integrable_power_laplace ((3/2 : ℝ)*(n : ℝ)) (by positivity) p hp).const_mul
    (rawAbsoluteMoment n)
  calc
    _ = (2 : ℝ)^(n-1)*∫ t : ℝ in Ioi 0,
        |x|^n*(t^(n : ℝ)*Real.exp (-p*t))+
        rawAbsoluteMoment n*(t^((3/2 : ℝ)*(n : ℝ))*Real.exp (-p*t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.rpow_natCast,Real.rpow_mul_natCast ht.le]
      unfold weightedMassBound
      ring
    _ = _ := by
      rw [integral_add h1 h2,integral_const_mul,integral_const_mul]
      rw [show (∫ t : ℝ in Ioi 0, t^(n : ℝ)*Real.exp (-p*t)) =
        (1/p)^((n : ℝ)+1)*Real.Gamma ((n : ℝ)+1) by
          simpa only [add_sub_cancel_right,← neg_mul] using
            Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0 < (n : ℝ)+1) hp]
      rw [show (∫ t : ℝ in Ioi 0, t^((3/2 : ℝ)*(n : ℝ))*Real.exp (-p*t)) =
        (1/p)^((3/2 : ℝ)*(n : ℝ)+1)*Real.Gamma ((3/2 : ℝ)*(n : ℝ)+1) by
          simpa only [add_sub_cancel_right,← neg_mul] using
            Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0 < (3/2 : ℝ)*(n : ℝ)+1) hp]
      unfold massPolynomialBound
      ring

theorem massPolynomialBound_nonneg (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    0 ≤ massPolynomialBound n p x := by
  rw [← integral_weightedMassBound_eq n p hp x]
  exact integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact weightedMassBound_nonneg n p x t ht.le)

theorem resolvent_total_mass_le (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    (∫⁻ y : ℝ, resolvent n p x y) ≤ ENNReal.ofReal (massPolynomialBound n p x) := by
  have he := resolvent_lintegral_eq_actual_momentLaw n p x
    (measurable_const : Measurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)))
  simp only [mul_one,lintegral_one] at he
  rw [he,← integral_weightedMassBound_eq n p hp x,
    ofReal_integral_eq_lintegral_ofReal (integrable_weightedMassBound n p hp x)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact weightedMassBound_nonneg n p x t ht.le)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  have h := mul_le_mul' (le_rfl : laplaceWeight p T ≤ laplaceWeight p T)
    (moment_mass_enn_bound n x (Real.toNNReal T) (Real.toNNReal_pos.mpr hT))
  simpa only [laplaceWeight,← ENNReal.ofReal_mul (Real.exp_nonneg _),
    Real.coe_toNNReal _ hT.le,weightedMassBound,mul_assoc] using h

theorem integrable_exponentially_weighted_massPolynomialBound (n : ℕ) (p : ℝ) (_hp : 0 < p)
    (q : ℝ) (hq : 0 ≤ q) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ ↦ x^q*Real.exp (-s*x)*massPolynomialBound n p x)
      (volume.restrict (Ioi 0)) := by
  let A := (1/p)^((n : ℝ)+1)*Real.Gamma ((n : ℝ)+1)
  let B := rawAbsoluteMoment n*(1/p)^((3/2 : ℝ)*(n : ℝ)+1)*
    Real.Gamma ((3/2 : ℝ)*(n : ℝ)+1)
  have h1 := (integrable_power_laplace (q+(n : ℝ)) (by positivity) s hs).const_mul A
  have h2 := (integrable_power_laplace q hq s hs).const_mul B
  apply ((h1.add h2).const_mul ((2 : ℝ)^(n-1))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (2 : ℝ)^(n-1)*(A*(x^(q+(n : ℝ))*Real.exp (-s*x))+
    B*(x^q*Real.exp (-s*x))) = x^q*Real.exp (-s*x)*massPolynomialBound n p x
  rw [Real.rpow_add hx,Real.rpow_natCast]
  dsimp only [A,B,massPolynomialBound]
  rw [abs_of_pos hx]
  ring

theorem exponential_weighted_total_mass_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p)
    (q : ℝ) (hq : 0 ≤ q) (s : ℝ) (hs : 0 < s) :
    (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (x^q*Real.exp (-s*x))*
      ∫⁻ y : ℝ, resolvent n p x y) ≠ ⊤ := by
  have hb : (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (x^q*Real.exp (-s*x))*
      ∫⁻ y : ℝ, resolvent n p x y) ≤ ∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (x^q*Real.exp (-s*x)*massPolynomialBound n p x) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := mul_le_mul' (le_rfl : ENNReal.ofReal (x^q*Real.exp (-s*x)) ≤ _)
      (resolvent_total_mass_le n p hp x)
    rw [← ENNReal.ofReal_mul' (massPolynomialBound_nonneg n p hp x)] at h
    exact h
  have hf : (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (x^q*Real.exp (-s*x)*massPolynomialBound n p x)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exponentially_weighted_massPolynomialBound n p hp q hq s hs)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _))
            (massPolynomialBound_nonneg n p hp x))]
    exact ENNReal.ofReal_ne_top
  exact ne_of_lt (hb.trans_lt (lt_top_iff_ne_top.mpr hf))

end PerronWright.BrownianKilledAreaResolventPolynomialMass
