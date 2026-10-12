import PerronWright.Probability.BrownianPositiveKilledEndpoint
import PerronWright.Probability.BrownianKilledSemigroup

/-! # Genuine absorbing-zero kernel and its Gaussian density at all states

The actual killed Brownian kernel is identified with the previously
proved positive-start endpoint law. Nonpositive initial states have
zero actual survival mass, and the truncated Gaussian difference is
zero there too. Thus the density and its genuine semigroup composition
hold for every real initial state, with no killed-kernel interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveKilledKernel

open BrownianPathLaw ContinuousPathFirstPassage BrownianPositiveKilledEndpoint BrownianKilledSemigroup

theorem transitionLaw_zero_eq_law (a : ℝ) (T : ℝ≥0) : transitionLaw 0 T a = law a T := by
  rw [law_eq_shift_killed,transitionLaw,zero_sub]
  congr 1
  funext y
  exact add_comm a y

theorem law_eq_zero_of_nonpos (a : ℝ) (ha : a ≤ 0) (T : ℝ≥0) : law a T = 0 := by
  have hz : pathLaw (survival (-a) T) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
    intro hs
    have he := (mem_survival_iff (-a) T f).mp hs 0 (show 0 ≤ T from zero_le)
    rw [hf] at he
    linarith
  rw [law,Measure.restrict_eq_zero.mpr hz,Measure.map_zero]

theorem density_eq_zero_of_nonpos (a : ℝ) (ha : a ≤ 0) (T : ℝ≥0) (hT : 0 < T) :
    density a T = 0 := by
  funext y
  by_cases hy : 0 < y
  · have hp : gaussianPDFReal a T y ≤ gaussianPDFReal (-a) T y := by
      rcases ha.eq_or_lt with h | h
      · rw [h,neg_zero]
      · simpa only [neg_neg] using gaussianPDFReal_negativeMean_le (-a) (by linarith) T hT y hy
    simp only [density,densityReal,Set.indicator,mem_Ioi,if_pos hy,Pi.zero_apply]
    exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hp)
  · simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hy,ENNReal.ofReal_zero,Pi.zero_apply]

theorem law_eq_withDensity_all (a : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    law a T = volume.withDensity (density a T) := by
  rcases lt_or_ge 0 a with ha | ha
  · exact law_eq_withDensity a ha T hT
  · rw [law_eq_zero_of_nonpos a ha T,density_eq_zero_of_nonpos a ha T hT,withDensity_zero]

theorem killedKernel_zero_eq_density (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    killedKernel 0 T a = volume.withDensity (density a T) := by
  rw [killedKernel_apply,transitionLaw_zero_eq_law,law_eq_withDensity_all a T hT]

theorem measurable_joint_densityReal (T : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ ↦ densityReal p.1 T p.2) := by
  have hp : Measurable (fun p : ℝ × ℝ ↦ gaussianPDFReal p.1 T p.2) :=
    measurable_uncurry_gaussianPDFReal.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hn : Measurable (fun p : ℝ × ℝ ↦ gaussianPDFReal (-p.1) T p.2) :=
    measurable_uncurry_gaussianPDFReal.comp (measurable_fst.neg.prodMk (measurable_const.prodMk measurable_snd))
  change Measurable (fun p : ℝ × ℝ ↦ if 0 < p.2 then
    gaussianPDFReal p.1 T p.2-gaussianPDFReal (-p.1) T p.2 else 0)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) (hp.sub hn) measurable_const

theorem measurable_joint_density (T : ℝ≥0) : Measurable (fun p : ℝ × ℝ ↦ density p.1 T p.2) :=
  (measurable_joint_densityReal T).ennreal_ofReal

theorem measurable_law_apply (T : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun a : ℝ ↦ law a T B) := by
  simpa only [transitionLaw_zero_eq_law] using measurable_transitionLaw_apply 0 T hB

theorem law_composition (a : ℝ) (s t : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    law a (s+t) B = ∫⁻ x, law x t B ∂law a s := by
  simpa only [transitionLaw_zero_eq_law] using transitionLaw_composition 0 s t a hB

theorem law_composition_density (a : ℝ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    {B : Set ℝ} (hB : MeasurableSet B) :
    law a (s+t) B = ∫⁻ x, density a s x*(∫⁻ y in B, density x t y) := by
  rw [law_composition a s t hB,law_eq_withDensity_all a s hs,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density a s) (measurable_law_apply t hB)]
  apply lintegral_congr
  intro x
  change density a s x*law x t B = density a s x*(∫⁻ y in B, density x t y)
  rw [law_eq_withDensity_all x t ht,withDensity_apply _ hB]

end PerronWright.BrownianPositiveKilledKernel
