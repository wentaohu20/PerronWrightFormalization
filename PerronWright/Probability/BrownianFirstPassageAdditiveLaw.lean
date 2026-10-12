import PerronWright.Probability.BrownianFirstPassageAdditiveGeometry
import PerronWright.Probability.BrownianFirstPassageDensityLaw
import Mathlib.MeasureTheory.Group.Convolution

/-! # The actual additive-depth Brownian first-passage convolution

Literal successive passage times are independent under the constructed
Brownian law, because the entire post-passage future is independent of
the true stopped past. The pathwise level decomposition identifies their
sum with passage to the sum of the depths. Thus the Borel time laws really
form a convolution semigroup; no convolution or passage identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageAdditiveLaw

open BrownianPathLaw BrownianFirstPassageDistribution BrownianFirstPassageUncappedLaw
open BrownianFirstPassageStrongMarkovFull BrownianFirstPassageAdditiveGeometry
open BrownianFirstPassageDensityGeometry BrownianFirstPassageDensityLaw

theorem ae_realTime_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ f ∂pathLaw, realTime (-(a+b)) f =
      realTime (-a) f + realTime (-b) (passageFuture (-a) f) := by
  filter_upwards [ae_passageTime_add a b ha hb] with f hf
  change (passageTime (-(a+b)) f : ℝ) =
    (passageTime (-a) f : ℝ) + (passageTime (-b) (passageFuture (-a) f) : ℝ)
  exact_mod_cast hf

theorem successive_times_independent (a b : ℝ) (ha : 0 < a) :
    IndepFun (realTime (-a)) (fun f ↦ realTime (-b) (passageFuture (-a) f)) pathLaw := by
  have h := (passagePast_future_independent (-a) (neg_neg_of_pos ha)).comp
    (measurable_coe_nnreal_real.comp measurable_fst) (measurable_realTime (-b))
  exact h

theorem future_timeLaw (a b : ℝ) (ha : 0 < a) :
    pathLaw.map (fun f ↦ realTime (-b) (passageFuture (-a) f)) = timeLaw (-b) := by
  calc
    _ = (pathLaw.map (passageFuture (-a))).map (realTime (-b)) :=
      (Measure.map_map (measurable_realTime (-b)) (measurable_passageFuture (-a))).symm
    _ = _ := by rw [passageFuture_law (-a) (neg_neg_of_pos ha)]; rfl

theorem successive_time_jointLaw (a b : ℝ) (ha : 0 < a) :
    pathLaw.map (fun f ↦ (realTime (-a) f,realTime (-b) (passageFuture (-a) f))) =
      (timeLaw (-a)).prod (timeLaw (-b)) := by
  have h := (successive_times_independent a b ha).map_prod_eq_prod_map_map
    (measurable_realTime (-a)).aemeasurable
    ((measurable_realTime (-b)).comp (measurable_passageFuture (-a))).aemeasurable
  change pathLaw.map (fun f ↦ (realTime (-a) f,realTime (-b) (passageFuture (-a) f))) =
    (timeLaw (-a)).prod (pathLaw.map (fun f ↦ realTime (-b) (passageFuture (-a) f))) at h
  rw [future_timeLaw a b ha] at h
  exact h

theorem timeLaw_convolution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    timeLaw (-(a+b)) = (timeLaw (-a)).conv (timeLaw (-b)) := by
  change pathLaw.map (realTime (-(a+b))) = _
  calc
    _ = pathLaw.map (fun f ↦ realTime (-a) f + realTime (-b) (passageFuture (-a) f)) :=
      Measure.map_congr (ae_realTime_add a b ha hb)
    _ = (pathLaw.map (fun f ↦ (realTime (-a) f,realTime (-b) (passageFuture (-a) f)))).map
        (fun p : ℝ × ℝ ↦ p.1+p.2) :=
      (Measure.map_map (measurable_fst.add measurable_snd)
        ((measurable_realTime (-a)).prodMk
          ((measurable_realTime (-b)).comp (measurable_passageFuture (-a))))).symm
    _ = _ := by rw [successive_time_jointLaw a b ha]; rfl

theorem density_measure_convolution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume.withDensity (density (a+b)) =
      (volume.withDensity (density a)).conv (volume.withDensity (density b)) := by
  rw [← timeLaw_neg_eq_withDensity (a+b) (add_pos ha hb),
    ← timeLaw_neg_eq_withDensity a ha,← timeLaw_neg_eq_withDensity b hb]
  exact timeLaw_convolution a b ha hb

theorem lintegral_firstPassage_additive (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (realTime (-(a+b)) f) ∂pathLaw) =
      ∫⁻ s, ∫⁻ t, Ψ (s+t) ∂timeLaw (-b) ∂timeLaw (-a) := by
  rw [← lintegral_map hΨ (measurable_realTime (-(a+b))),← timeLaw,
    timeLaw_convolution a b ha hb,Measure.lintegral_conv hΨ]

theorem lintegral_firstPassage_additive_density (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (realTime (-(a+b)) f) ∂pathLaw) =
      ∫⁻ s, ∫⁻ t, density a s * density b t * Ψ (s+t) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ Ψ (p.1+p.2)) :=
    hΨ.comp (measurable_fst.add measurable_snd)
  have hAdd : Measurable (fun p : ℝ × ℝ ↦ p.1+p.2) :=
    measurable_fst.add measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ ↦ density a p.1 * density b p.2) :=
    ((measurable_density a).comp measurable_fst).mul
      ((measurable_density b).comp measurable_snd)
  rw [← lintegral_map hΨ (measurable_realTime (-(a+b))),← timeLaw,
    timeLaw_convolution a b ha hb]
  change (∫⁻ t, Ψ t ∂((timeLaw (-a)).prod (timeLaw (-b))).map
    (fun p : ℝ × ℝ ↦ p.1+p.2)) = _
  rw [lintegral_map hΨ hAdd,
    timeLaw_neg_eq_withDensity a ha,timeLaw_neg_eq_withDensity b hb,
    prod_withDensity (measurable_density a) (measurable_density b),
    lintegral_withDensity_eq_lintegral_mul (volume.prod volume) hd hm]
  exact lintegral_prod _ (hd.mul hm).aemeasurable

end PerronWright.BrownianFirstPassageAdditiveLaw
