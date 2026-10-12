import PerronWright.Probability.BrownianPositiveBridgeAreaExponentialTails
import PerronWright.Probability.BrownianEntranceAreaWrightMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The true entrance-area mgf is the full Wright power series

Absolute exponential integrability controls the actual integrated series,
including negative real parameters. Every coefficient is the already
proved literal Wright constant. No transform identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceAreaWrightGeneratingFunction

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeAreaLawIdentification
open BrownianPositiveBridgeAreaExponentialTails BrownianEntranceAreaWrightMoments
open PerronWrightFormulaMainTerm

private def seriesTerm (T : ℝ≥0) (u : ℝ) (n : ℕ) (f : Path) : ℝ :=
  (u*pathArea T f)^n/(n.factorial : ℝ)

private theorem exp_nonnegative_enn_series (z : ℝ) (hz : 0 ≤ z) :
    ENNReal.ofReal (Real.exp z) = ∑' n : ℕ, ENNReal.ofReal (z^n/(n.factorial : ℝ)) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (Real.summable_pow_div_factorial z)]
  congr 1
  rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]

private theorem seriesTerm_integrable (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (n : ℕ) :
    Integrable (seriesTerm T u n) (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  convert! (entrance_area_pow_integrable T hT n).const_mul (u^n/(n.factorial : ℝ)) using 1
  funext f
  dsimp [seriesTerm]
  rw [mul_pow]
  ring

private theorem integrated_norm_series_ne_top (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∑' n : ℕ, ∫⁻ f : Path, ‖seriesTerm T u n f‖ₑ
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) ≠ ⊤ := by
  have he : (∑' n : ℕ, ∫⁻ f : Path, ‖seriesTerm T u n f‖ₑ
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      ∫⁻ f : Path, ENNReal.ofReal (Real.exp (|u| * pathArea T f))
        ∂BrownianEntranceContinuousRealization.pathLaw T hT := by
    rw [← lintegral_tsum (fun n ↦ (seriesTerm_integrable T hT u n).1.enorm)]
    apply lintegral_congr_ae
    filter_upwards [ae_entrance_pathArea_nonneg T hT] with f hf
    have hnorm (n : ℕ) : ‖seriesTerm T u n f‖ₑ =
        ENNReal.ofReal ((|u| * pathArea T f)^n/(n.factorial : ℝ)) := by
      simp only [seriesTerm,← ofReal_norm,Real.norm_eq_abs,abs_div,abs_pow,abs_mul,
        abs_of_nonneg hf,abs_of_nonneg (show (0:ℝ) ≤ (n.factorial:ℝ) from Nat.cast_nonneg _)]
    simp_rw [hnorm]
    exact (exp_nonnegative_enn_series (|u| * pathArea T f) (mul_nonneg (abs_nonneg u) hf)).symm
  rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mp
    (entrance_area_exp_integrable T hT |u|).2).ne

private theorem integral_seriesTerm (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (n : ℕ) :
    (∫ f : Path, seriesTerm T u n f ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      wrightConstant n*(u*(T : ℝ)^(3/2 : ℝ))^n := by
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = (u^n/(n.factorial : ℝ))*(∫ f : Path, pathArea T f^n
        ∂BrownianEntranceContinuousRealization.pathLaw T hT) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro f
      dsimp [seriesTerm]
      rw [mul_pow]
      ring
    _ = _ := by
      rw [entrance_area_real_moment_eq_time_kernel_integral,
        entranceAreaMoment_duration_eq_wrightConstant T hT n,mul_pow]
      field_simp

theorem hasSum_actual_entrance_area_mgf_wright (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    HasSum (fun n : ℕ ↦ wrightConstant n*(u*(T : ℝ)^(3/2 : ℝ))^n)
      (∫ f : Path, Real.exp (u*pathArea T f)
        ∂BrownianEntranceContinuousRealization.pathLaw T hT) := by
  have hsum : Summable (fun n : ℕ ↦ ∫ f : Path, ‖seriesTerm T u n f‖
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) := by
    have h := ENNReal.summable_toReal (integrated_norm_series_ne_top T hT u)
    convert! h using 1
    funext n
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ norm_nonneg _))
      (seriesTerm_integrable T hT u n).norm.1]
    simp only [ofReal_norm]
  have h := hasSum_integral_of_summable_integral_norm (seriesTerm_integrable T hT u) hsum
  have he : (∫ f : Path, (∑' n : ℕ, seriesTerm T u n f)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      ∫ f : Path, Real.exp (u*pathArea T f)
        ∂BrownianEntranceContinuousRealization.pathLaw T hT := by
    apply integral_congr_ae
    apply ae_of_all
    intro f
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    rfl
  rw [he] at h
  simpa only [integral_seriesTerm T hT u] using h

theorem summable_wright_area_mgf_series (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Summable (fun n : ℕ ↦ wrightConstant n*(u*(T : ℝ)^(3/2 : ℝ))^n) :=
  (hasSum_actual_entrance_area_mgf_wright T hT u).summable

theorem actual_entrance_area_mgf_eq_wright_series (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f : Path, Real.exp (u*pathArea T f)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      ∑' n : ℕ, wrightConstant n*(u*(T : ℝ)^(3/2 : ℝ))^n :=
  (hasSum_actual_entrance_area_mgf_wright T hT u).tsum_eq.symm

end PerronWright.BrownianEntranceAreaWrightGeneratingFunction
