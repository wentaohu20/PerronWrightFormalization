import PerronWright.Probability.BrownianFirstPassageLaplace
import PerronWright.Probability.BrownianFirstPassageDensityLaw
import PerronWright.Probability.BrownianHeatPassageTail
import PerronWright.Probability.PositiveTimeConvolutionLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The actual Gaussian heat duration resolvent

Tonelli changes the level-tail integral of the genuine first-passage
transform into the heat transform. Its exponential evaluation follows
from the proved Brownian hitting transform, not a Green-kernel premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianHeatResolvent

open BrownianPathLaw BrownianFirstPassageLaplace BrownianFirstPassageDensityLaw
open BrownianHeatPassageTail PositiveTimeConvolutionLaplace

theorem measurable_joint_passageDensity :
    Measurable (fun p : ℝ × ℝ ↦ BrownianFirstPassageDensityGeometry.density p.1 p.2) := by
  unfold BrownianFirstPassageDensityGeometry.density BrownianFirstPassageDensityGeometry.densityReal
    BrownianFirstPassageDensityGeometry.argument
  change Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal
    (if 0 < p.2 then p.1/(p.2*Real.sqrt p.2)*gaussianPDFReal 0 1 (-p.1/Real.sqrt p.2) else 0))
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd) _ measurable_const
  fun_prop

theorem lintegral_passageDensity_laplace (a : ℝ) (ha : 0 < a)
    (p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ t : ℝ, laplaceWeight p t*BrownianFirstPassageDensityGeometry.density a t) =
      ENNReal.ofReal (Real.exp (-a*Real.sqrt (2*p))) := by
  have he := lintegral_firstPassage_density a ha (laplaceWeight p) (measurable_laplaceWeight p)
  have hh := lintegral_negative_passageLaplace a ha p hp
  change (∫⁻ f : Path, laplaceWeight p (BrownianFirstPassageDistribution.realTime (-a) f) ∂pathLaw) = _ at hh
  rw [he] at hh
  simpa only [mul_comm] using hh

def heatResolvent (p x : ℝ) : ℝ≥0∞ := ∫⁻ t : ℝ, laplaceWeight p t*heat t x

theorem heatResolvent_eq_level_tail (p a : ℝ) (ha : 0 ≤ a) :
    heatResolvent p a = ∫⁻ b in Ioi a, ∫⁻ t : ℝ,
      laplaceWeight p t*BrownianFirstPassageDensityGeometry.density b t := by
  have hM : Measurable (fun q : ℝ × ℝ ↦ laplaceWeight p q.1*
      BrownianFirstPassageDensityGeometry.density q.2 q.1) :=
    ((measurable_laplaceWeight p).comp measurable_fst).mul
      (measurable_joint_passageDensity.comp measurable_swap)
  calc
    _ = ∫⁻ t : ℝ, laplaceWeight p t*(∫⁻ b in Ioi a,
        BrownianFirstPassageDensityGeometry.density b t) := by
      simp only [lintegral_level_density _ _ ha,heatResolvent]
    _ = ∫⁻ t : ℝ, ∫⁻ b in Ioi a,
        laplaceWeight p t*BrownianFirstPassageDensityGeometry.density b t := by
      apply lintegral_congr
      intro t
      symm
      exact lintegral_const_mul _
        (measurable_joint_passageDensity.comp (measurable_id.prodMk measurable_const))
    _ = _ := lintegral_lintegral_swap hM.aemeasurable

theorem heatResolvent_eq (p : ℝ) (hp : 0 < p) (a : ℝ) (ha : 0 ≤ a) :
    heatResolvent p a = ENNReal.ofReal
      (Real.exp (-a*Real.sqrt (2*p))/Real.sqrt (2*p)) := by
  have hs : 0 < Real.sqrt (2*p) := Real.sqrt_pos.mpr (by positivity)
  rw [heatResolvent_eq_level_tail p a ha]
  calc
    _ = ∫⁻ b in Ioi a, ENNReal.ofReal (Real.exp (-b*Real.sqrt (2*p))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
      exact lintegral_passageDensity_laplace b (ha.trans_lt hb) p hp.le
    _ = ENNReal.ofReal (∫ b in Ioi a, Real.exp (-Real.sqrt (2*p)*b)) := by
      have he (b : ℝ) : Real.exp (-b*Real.sqrt (2*p)) =
          Real.exp (-Real.sqrt (2*p)*b) := by
        congr 1
        ring
      simp only [he]
      exact (ofReal_integral_eq_lintegral_ofReal
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) a)
        (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))).symm
    _ = _ := by
      rw [integral_exp_mul_Ioi (neg_neg_of_pos hs) a]
      simp only [neg_div_neg_eq]
      rw [show -Real.sqrt (2*p)*a = -a*Real.sqrt (2*p) by ring]

theorem heat_even (t a : ℝ) : heat t (-a) = heat t a := by
  unfold heat heatReal gaussianPDFReal
  simp only [sub_zero,neg_sq]

theorem heat_abs (t a : ℝ) : heat t |a| = heat t a := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha,heat_even]

theorem heatResolvent_eq_abs (p : ℝ) (hp : 0 < p) (a : ℝ) :
    heatResolvent p a = ENNReal.ofReal
      (Real.exp (-|a| * Real.sqrt (2*p))/Real.sqrt (2*p)) := by
  have he : heatResolvent p a = heatResolvent p |a| := by
    unfold heatResolvent
    simp only [heat_abs]
  rw [he]
  exact heatResolvent_eq p hp |a| (abs_nonneg a)

theorem heatResolvent_ne_top (p : ℝ) (hp : 0 < p) (a : ℝ) :
    heatResolvent p a ≠ ⊤ := by
  rw [heatResolvent_eq_abs p hp a]
  exact ENNReal.ofReal_ne_top

end PerronWright.BrownianHeatResolvent
