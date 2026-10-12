import PerronWright.Probability.BrownianKilledTransitionKernel
import PerronWright.Probability.BrownianKilledGaussianAlgebra
import PerronWright.Probability.BrownianBridgeSurvivalPointwise
import PerronWright.Probability.BrownianFirstPassageNegativeDrift
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Actual bridge survival and killed Gaussian transition density

The genuine first-passage reflection identity identifies the actual
Gaussian-relative density of the killed endpoint law. Uniqueness of
densities gives the actual constrained pinned-bridge probability almost
everywhere. Monotonicity and the proved dense-good-endpoint argument
upgrade this to every endpoint. No reflection, positive-excursion,
first-passage density, or Palm identity is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeSurvivalLaw

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageBridgeLaw
open BrownianKilledTransitionKernel BrownianKilledGaussianAlgebra

theorem killedEndpointLaw_bridge_density (level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    killedEndpointLaw level T = (gaussianReal 0 T).withDensity
      (fun z ↦ pinnedLaw T (bridgeConstraint level T z)) := by
  ext B hB
  rw [killedEndpointLaw_apply level T hB,withDensity_apply _ hB]
  exact firstPassage_survival_endpoint_probability level T hT hB

/-- The actual constrained bridge probability is identified from true
reflection and Gaussian densities, without a conditional-law premise. -/
theorem bridgeConstraint_probability_ae (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) :
    (fun z ↦ pinnedLaw T (bridgeConstraint level T z)) =ᵐ[gaussianReal 0 T]
      survivalFactor level T := by
  let p : ℝ → ℝ≥0∞ := fun z ↦ pinnedLaw T (bridgeConstraint level T z)
  let r : ℝ → ℝ≥0∞ := (Ioi level).indicator (reflectedWeight level T)
  let I : ℝ → ℝ≥0∞ := (Ioi level).indicator 1
  have hp : Measurable p := measurable_bridgeConstraint_probability level T
  have hr : Measurable r := (measurable_reflectedWeight level T).indicator measurableSet_Ioi
  have hI : Measurable I := measurable_const.indicator measurableSet_Ioi
  have hs := killedEndpointLaw_add_reflected level hlevel T
  rw [killedEndpointLaw_bridge_density level T hT,
    gaussianReal_reflected_restrict_eq_withDensity level T hT,
    ← withDensity_indicator_one measurableSet_Ioi] at hs
  have hd : (gaussianReal 0 T).withDensity (p+r) = (gaussianReal 0 T).withDensity I := by
    rw [withDensity_add_left hp]
    exact hs
  have hae : p+r =ᵐ[gaussianReal 0 T] I :=
    (withDensity_eq_iff_of_sigmaFinite (hp.add hr).aemeasurable hI.aemeasurable).mp hd
  filter_upwards [hae] with z hz
  change p z = survivalFactor level T z
  change p z+r z = I z at hz
  by_cases hx : level < z
  · have hsum : p z+reflectedWeight level T z = 1 := by
      simpa only [r,I,Set.indicator,mem_Ioi,if_pos hx,Pi.one_apply] using hz
    have he : p z = 1-reflectedWeight level T z :=
      ENNReal.eq_sub_of_add_eq' (by simp) hsum
    rw [he]
    unfold reflectedWeight survivalFactor survivalFactorReal
    rw [if_pos hx,ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one]
  · rw [survivalFactor_of_le level T (le_of_not_gt hx)]
    simpa only [r,I,Set.indicator,mem_Ioi,if_neg hx,add_zero] using hz

theorem bridgeConstraint_probability (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) (z : ℝ) :
    pinnedLaw T (bridgeConstraint level T z) = survivalFactor level T z :=
  congrFun (BrownianBridgeSurvivalPointwise.bridgeConstraint_probability_eq_of_gaussian_ae
    level T hT 0 (continuous_survivalFactor level hlevel T hT)
      (bridgeConstraint_probability_ae level hlevel T hT)) z

theorem bridgeConstraint_probability_of_lt (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) {z : ℝ} (hz : level < z) :
    pinnedLaw T (bridgeConstraint level T z) =
      ENNReal.ofReal (1-Real.exp (2*level*(z-level)/(T : ℝ))) := by
  rw [bridgeConstraint_probability level hlevel T hT]
  simp only [survivalFactor,survivalFactorReal,if_pos hz]

theorem bridgeConstraint_probability_of_le (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) {z : ℝ} (hz : z ≤ level) :
    pinnedLaw T (bridgeConstraint level T z) = 0 := by
  rw [bridgeConstraint_probability level hlevel T hT,survivalFactor_of_le level T hz]

theorem continuous_bridgeConstraint_probability (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) :
    Continuous (fun z ↦ pinnedLaw T (bridgeConstraint level T z)) := by
  have he := funext (bridgeConstraint_probability level hlevel T hT)
  rw [he]
  exact continuous_survivalFactor level hlevel T hT

/-- Exact normalization of the actual zero-endpoint pinned bridge above
a negative barrier, before taking any positive-excursion limit. -/
theorem bridgeConstraint_probability_zero_endpoint (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) :
    pinnedLaw T (bridgeConstraint (-a) T 0) =
      ENNReal.ofReal (1-Real.exp (-2*a^2/(T : ℝ))) := by
  rw [bridgeConstraint_probability_of_lt (-a) (by linarith) T hT (z := 0) (by linarith)]
  rw [show 2*(-a)*(0-(-a))/(T : ℝ) = -2*a^2/(T : ℝ) by ring]

theorem bridgeConstraint_probability_zero_endpoint_pos (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) : 0 < pinnedLaw T (bridgeConstraint (-a) T 0) := by
  rw [bridgeConstraint_probability_zero_endpoint a ha T hT,ENNReal.ofReal_pos]
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos ha]) (show (0 : ℝ) < T from hT)

/-- Genuine killed Brownian endpoint law, with its proved Gaussian
relative survival density. -/
theorem killedEndpointLaw_eq_gaussian_withDensity (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) :
    killedEndpointLaw level T = (gaussianReal 0 T).withDensity (survivalFactor level T) := by
  rw [killedEndpointLaw_bridge_density level T hT]
  exact withDensity_congr_ae (bridgeConstraint_probability_ae level hlevel T hT)

def killedDensity (level : ℝ) (T : ℝ≥0) : ℝ → ℝ≥0∞ :=
  (Ioi level).indicator (fun z ↦ gaussianPDF 0 T z-gaussianPDF (2*level) T z)

theorem measurable_killedDensity (level : ℝ) (T : ℝ≥0) : Measurable (killedDensity level T) :=
  ((measurable_gaussianPDF 0 T).sub (measurable_gaussianPDF (2*level) T)).indicator measurableSet_Ioi

/-- The literal killed Gaussian density is the positive Gaussian density
minus its reflected density above the actual absorbing level, zero below. -/
theorem killedEndpointLaw_eq_withDensity (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) :
    killedEndpointLaw level T = volume.withDensity (killedDensity level T) := by
  rw [killedEndpointLaw_eq_gaussian_withDensity level hlevel T hT,
    gaussianReal_of_var_ne_zero _ (ne_of_gt hT),
    ← withDensity_mul volume (measurable_gaussianPDF 0 T)
      (continuous_survivalFactor level hlevel T hT).measurable]
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun z ↦ by
    by_cases hz : level < z
    · simp only [Pi.mul_apply,killedDensity,Set.indicator,mem_Ioi,if_pos hz]
      exact (gaussianPDF_reflected_difference level T hT hz).symm
    · simp only [Pi.mul_apply,survivalFactor_of_le level T (le_of_not_gt hz),mul_zero,
        killedDensity,Set.indicator,mem_Ioi,if_neg hz])

theorem firstPassage_survival_endpoint_probability_explicit (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
      ∫⁻ z in B, survivalFactor level T z ∂gaussianReal 0 T := by
  rw [firstPassage_survival_endpoint_probability level T hT hB]
  exact lintegral_congr (bridgeConstraint_probability level hlevel T hT)

theorem linearDrift_survival_endpoint_probability_explicit (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) (u : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level
      (BrownianFirstPassageNegativeDrift.linearPath u f) ∧
        BrownianFirstPassageNegativeDrift.linearPath u f T ∈ B} =
      ∫⁻ z in B, survivalFactor level T z ∂gaussianReal (u*(T : ℝ)) T := by
  rw [BrownianFirstPassageNegativeDrift.firstPassage_survival_endpoint_probability level T hT u hB]
  exact lintegral_congr (bridgeConstraint_probability level hlevel T hT)

end PerronWright.BrownianBridgeSurvivalLaw
