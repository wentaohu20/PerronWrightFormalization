import PerronWright.Probability.BrownianMinimumEndpointJointLaw
import PerronWright.Probability.BrownianEntranceKernelLaplace
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # The genuine minimum endpoint law as an actual density measure

The bounded continuous joint-density equality determines the actual
mapped Brownian law. Consequently the numerical representation applies
to every nonnegative Borel test, including time-window restrictions.
Neither a regular conditional law nor a minimum-density identification
is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointMeasure

open BrownianPathLaw ContinuousPathLeastMinimum BrownianFirstPassageEndpointGeometry
open BrownianMinimumEndpointJointLaw BrownianKilledBoundaryEntrance

def minimumTriple (T : ℝ≥0) (f : Path) : ℝ≥0 × ℝ × ℝ :=
  (leastMinimizer T f,minimumValue T f,f T-minimumValue T f)

theorem measurable_minimumTriple (T : ℝ≥0) : Measurable (minimumTriple T) :=
  (measurable_leastMinimizer T).prodMk ((continuous_minimumValue T).measurable.prodMk
    ((continuous_eval T).measurable.sub (continuous_minimumValue T).measurable))

def actualLaw (T : ℝ≥0) : Measure (ℝ≥0 × ℝ × ℝ) := pathLaw.map (minimumTriple T)

instance actualLaw_isProbability (T : ℝ≥0) : IsProbabilityMeasure (actualLaw T) :=
  Measure.isProbabilityMeasure_map (measurable_minimumTriple T).aemeasurable

def referenceMeasure (T : ℝ≥0) : Measure (ℝ × ℝ × ℝ) :=
  (volume.restrict (Ioo 0 (T : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod volume)

def jointDensity (T : ℝ≥0) (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.2.1 p.1*entrance (remainingTime T p.1) p.2.2

theorem measurable_jointDensity (T : ℝ≥0) : Measurable (jointDensity T) :=
  (BrownianHeatResolvent.measurable_joint_passageDensity.comp
    (measurable_snd.fst.prodMk measurable_fst)).mul
    (BrownianEntranceKernelLaplace.measurable_joint_entrance.comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd.snd))

def encode (p : ℝ × ℝ × ℝ) : ℝ≥0 × ℝ × ℝ := (Real.toNNReal p.1,-p.2.1,p.2.2)

theorem measurable_encode : Measurable encode :=
  measurable_fst.real_toNNReal.prodMk (measurable_snd.fst.neg.prodMk measurable_snd.snd)

def candidateLaw (T : ℝ≥0) : Measure (ℝ≥0 × ℝ × ℝ) :=
  ((referenceMeasure T).withDensity (jointDensity T)).map encode

theorem lintegral_candidateLaw (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ p, Φ p ∂candidateLaw T) =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ y, entrance (remainingTime T s) y*Φ (Real.toNNReal s,-a,y) := by
  have hm := (measurable_jointDensity T).mul (hΦ.comp measurable_encode)
  rw [candidateLaw,lintegral_map hΦ measurable_encode]
  change (∫⁻ p, (Φ ∘ encode) p ∂(referenceMeasure T).withDensity (jointDensity T)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_jointDensity T) (hΦ.comp measurable_encode),
    referenceMeasure,lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro s
  trans ∫⁻ a in Ioi (0 : ℝ), ∫⁻ y : ℝ,
    (jointDensity T * Φ ∘ encode) (s,a,y)
  · exact lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  apply lintegral_congr
  intro a
  simp only [jointDensity,encode,Pi.mul_apply,Function.comp_apply,mul_assoc]
  exact lintegral_const_mul _ ((measurable_entrance _).mul
    (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))))

theorem actualLaw_eq_candidateLaw (T : ℝ≥0) (hT : 0 < T) :
    actualLaw T = candidateLaw T := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ :=
    ⟨⟨fun p ↦ (f p : ℝ),NNReal.continuous_coe.comp f.continuous⟩,f.map_bounded'⟩
  have he := actual_minimum_endpoint_joint_density T hT Φ (fun p ↦ (f p).coe_nonneg)
  rw [actualLaw,lintegral_map f.continuous.measurable.coe_nnreal_ennreal (measurable_minimumTriple T),
    lintegral_candidateLaw T _ f.continuous.measurable.coe_nnreal_ennreal]
  simpa only [Φ,BoundedContinuousFunction.coe_mk,ContinuousMap.coe_mk,minimumTriple,
    ENNReal.ofReal_coe_nnreal] using he

theorem candidateLaw_isProbability (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (candidateLaw T) := by
  rw [← actualLaw_eq_candidateLaw T hT]
  infer_instance

theorem actual_minimum_endpoint_borel_density (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (minimumTriple T f) ∂pathLaw) =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ y, entrance (remainingTime T s) y*Φ (Real.toNNReal s,-a,y) := by
  rw [← lintegral_map hΦ (measurable_minimumTriple T)]
  change (∫⁻ p, Φ p ∂actualLaw T) = _
  rw [actualLaw_eq_candidateLaw T hT,lintegral_candidateLaw T Φ hΦ]

end PerronWright.BrownianMinimumEndpointMeasure
