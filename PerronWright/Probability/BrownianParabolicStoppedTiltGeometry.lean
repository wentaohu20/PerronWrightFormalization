import PerronWright.Probability.BrownianParabolicDriftTilt
import PerronWright.Probability.BrownianKilledAreaGeometry
import PerronWright.Probability.ContinuousPathAreaContinuity
import PerronWright.Probability.BrownianFactorialDensityDeletion

/-! # Actual parabolic density cocycle, including zero remaining duration

The score is cut using the literal interval-area identity. Its polynomial
energy obeys the proved deletion cocycle. The zero-duration normalization
uses the actual Brownian zero initial value, not an omitted positive-time
boundary premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicStoppedTiltGeometry

open BrownianPathLaw BrownianPathIndependentIncrements BrownianBridgeCyclicArea
open BrownianParabolicDriftTiltGeometry BrownianParabolicDriftTilt
open BrownianKilledAreaGeometry ContinuousPathAreaContinuity

theorem continuous_joint_score :
    Continuous (fun p : ℝ × (ℝ≥0 × Path) ↦ score p.1 p.2.1 p.2.2) :=
  ((continuous_fst.sub (NNReal.continuous_coe.comp continuous_snd.fst)).mul
    (continuous_joint_eval.comp (continuous_snd.snd.prodMk continuous_snd.fst))).add
      (continuous_joint_pathArea.comp continuous_snd)

theorem continuous_joint_energy :
    Continuous (fun p : ℝ × ℝ≥0 ↦ energy p.1 p.2) := by
  unfold energy
  fun_prop

theorem measurable_joint_density :
    Measurable (fun p : ℝ × (ℝ≥0 × Path) ↦ density p.1 p.2.1 p.2.2) :=
  (Real.continuous_exp.comp (continuous_joint_score.sub
    ((continuous_joint_energy.comp (continuous_fst.prodMk continuous_snd.fst)).div_const 2)))
    |>.measurable.ennreal_ofReal

theorem score_add (lambda : ℝ) (s t : ℝ≥0) (f : Path) :
    score lambda (s+t) f = score lambda s f+score (lambda-(s : ℝ)) t (futurePath s f) := by
  unfold score
  rw [pathArea_add,NNReal.coe_add,futurePath_eval]
  ring

theorem energy_add (lambda : ℝ) (s t : ℝ≥0) :
    energy lambda (s+t) = energy lambda s+energy (lambda-(s : ℝ)) t := by
  simp only [BrownianFactorialDensityDeletion.energy_eq_twice_criticalExponent,NNReal.coe_add]
  rw [BrownianFactorialDensityDeletion.criticalExponent_deletion]
  ring

theorem density_add (lambda : ℝ) (s t : ℝ≥0) (f : Path) :
    density lambda (s+t) f = density lambda s f*density (lambda-(s : ℝ)) t (futurePath s f) := by
  unfold density
  rw [score_add,energy_add,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem density_past (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    density lambda T (pastPath T f) = density lambda T f := by
  unfold density score
  rw [pathArea_past]
  change ENNReal.ofReal (Real.exp ((lambda-↑T)*f (min T T)+pathArea T f-energy lambda T/2)) = _
  rw [min_self]

theorem ae_density_zero_eq_one (lambda : ℝ) :
    ∀ᵐ f : Path ∂pathLaw, density lambda 0 f = 1 := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  simp only [density,score,energy,pathArea,intervalIntegral.integral_same,NNReal.coe_zero,
    sub_zero,hf,mul_zero,zero_pow (by norm_num : 2 ≠ 0),zero_pow (by norm_num : 3 ≠ 0),
    zero_div,add_zero,Real.exp_zero,ENNReal.ofReal_one]

theorem lintegral_actual_parabolic_density_allTimes (lambda : ℝ) (T : ℝ≥0) :
    (∫⁻ f : Path, density lambda T f ∂pathLaw) = 1 := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from bot_le) with hT | hT
  · subst T
    rw [lintegral_congr_ae (ae_density_zero_eq_one lambda),lintegral_one,measure_univ]
  · exact lintegral_actual_parabolic_density lambda T hT

theorem actual_stopped_parabolic_law_eq_weighted_allTimes (lambda : ℝ) (T : ℝ≥0) :
    pathLaw.map (stoppedParabolicPath lambda T) =
      (pathLaw.withDensity (density lambda T)).map (BrownianEndpointDriftTilt.stoppedPath T) := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from bot_le) with hT | hT
  · subst T
    have hd : pathLaw.withDensity (density lambda 0) = pathLaw := by
      rw [withDensity_congr_ae (ae_density_zero_eq_one lambda)]
      exact withDensity_one
    rw [hd]
    congr 1
    funext f
    apply ContinuousMap.ext
    intro t
    change f (min t 0)+lambda*(min t 0 : ℝ≥0)-(min t 0 : ℝ≥0)^2/2 = f (min t 0)
    simp
  · exact actual_stopped_parabolic_law_eq_weighted lambda T hT

end PerronWright.BrownianParabolicStoppedTiltGeometry
