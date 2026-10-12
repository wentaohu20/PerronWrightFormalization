import PerronWright.Probability.BrownianParabolicStoppedTiltGeometry
import PerronWright.Probability.BrownianFirstPassageStrongMarkov
import PerronWright.Probability.BrownianParabolicFirstPassageDensity
import PerronWright.Probability.BrownianParabolicFirstPassagePastFibers

/-! # Actual random-time parabolic first-passage density

The raw Brownian stopped-past law is weighted by its literal random-time
endpoint/area score. The changed law is the actual stopped parabolic
driver law. Future integration uses the proved constant-level Brownian
whole-future product and the genuine all-duration density normalization.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageStoppedTilt

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassagePastFibers BrownianFirstPassageReflection BrownianFirstPassageStrongMarkov
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicFirstPassageDensity

def stoppedDensity (lambda : ℝ) (p : ℝ≥0 × Path) : ℝ≥0∞ := density lambda p.1 p.2

theorem measurable_stoppedDensity (lambda : ℝ) : Measurable (stoppedDensity lambda) :=
  measurable_joint_density.comp (measurable_const.prodMk measurable_id)

private theorem cappedTime_pastPath (level : ℝ) (T : ℝ≥0) (f : Path) :
    cappedTime level T (pastPath T f) = cappedTime level T f := by
  have he (s : ℝ≥0) (hs : s ≤ T) :
      cappedTime level T (pastPath T f) ≤ s ↔ cappedTime level T f ≤ s := by
    simp only [← ENNReal.coe_le_coe,cappedTime_coe,min_le_iff]
    exact or_congr (firstPassage_le_pastPath level T s hs f) Iff.rfl
  exact le_antisymm ((he _ (cappedTime_le level T f)).mpr le_rfl)
    ((he _ (cappedTime_le level T (pastPath T f))).mp le_rfl)

private theorem boundedPast_pastPath (level : ℝ) (T : ℝ≥0) (f : Path) :
    boundedPast level T (pastPath T f) = boundedPast level T f := by
  unfold boundedPast
  rw [cappedTime_pastPath]
  congr 1
  apply ContinuousMap.ext
  intro t
  change f (min (min t (cappedTime level T f)) T) = f (min t (cappedTime level T f))
  rw [min_eq_left ((min_le_right _ _).trans (cappedTime_le level T f))]

theorem density_weighted_boundedPast_lintegral (lambda level : ℝ) (T : ℝ≥0)
    {Φ : ℝ≥0 × Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f : Path, density lambda T f*Φ (boundedPast level T f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, stoppedDensity lambda p*Φ p ∂pathLaw.map (boundedPast level T) := by
  let Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun p ↦
    stoppedDensity lambda p.1*Φ p.1*density (lambda-(p.1.1 : ℝ)) (T-p.1.1) p.2
  have hΨ : Measurable Ψ :=
    (((measurable_stoppedDensity lambda).comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
      (measurable_joint_density.comp
        ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk
          ((measurable_const.sub measurable_fst.fst).prodMk measurable_snd)))
  have hj := (measurable_boundedPast level T).prodMk (measurable_boundedFuture level T)
  have he : (∫⁻ f : Path, density lambda T f*Φ (boundedPast level T f) ∂pathLaw) =
      ∫⁻ f : Path, Ψ (boundedPast level T f,boundedFuture level T f) ∂pathLaw := by
    apply lintegral_congr
    intro f
    have ht : cappedTime level T f+(T-cappedTime level T f) = T :=
      add_tsub_cancel_of_le (cappedTime_le level T f)
    have hd := density_add lambda (cappedTime level T f) (T-cappedTime level T f) f
    rw [ht,← density_past lambda (cappedTime level T f) f] at hd
    rw [hd]
    change _ = (density lambda (cappedTime level T f) (pastPath (cappedTime level T f) f)*
      Φ (boundedPast level T f))*density (lambda-(cappedTime level T f : ℝ))
        (T-cappedTime level T f) (futurePath (cappedTime level T f) f)
    ac_rfl
  rw [he,← lintegral_map hΨ hj,bounded_jointLaw,lintegral_prod _ hΨ.aemeasurable]
  apply lintegral_congr
  intro p
  change (∫⁻ g : Path, (stoppedDensity lambda p*Φ p)*
    density (lambda-(p.1 : ℝ)) (T-p.1) g ∂pathLaw) = _
  rw [lintegral_const_mul _ (measurable_density _ _),
    lintegral_actual_parabolic_density_allTimes,mul_one]

theorem density_weighted_boundedPast_law (lambda level : ℝ) (T : ℝ≥0) :
    (pathLaw.withDensity (density lambda T)).map (boundedPast level T) =
      (pathLaw.map (boundedPast level T)).withDensity (stoppedDensity lambda) := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ (measurable_boundedPast level T)]
  change (∫⁻ f : Path, (Φ ∘ boundedPast level T) f ∂pathLaw.withDensity (density lambda T)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_density lambda T)
      (hΦ.comp (measurable_boundedPast level T)),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity lambda) hΦ]
  exact density_weighted_boundedPast_lintegral lambda level T hΦ

def actualDriverBoundedPast (lambda level : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0 × Path :=
  boundedPast level T (BrownianPathReflectionLaw.driftPath lambda f)

theorem measurable_actualDriverBoundedPast (lambda level : ℝ) (T : ℝ≥0) :
    Measurable (actualDriverBoundedPast lambda level T) :=
  (measurable_boundedPast level T).comp
    (BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda)

theorem actual_parabolic_stoppedPassage_law (lambda level : ℝ) (T : ℝ≥0) :
    pathLaw.map (actualDriverBoundedPast lambda level T) =
      (pathLaw.map (boundedPast level T)).withDensity (stoppedDensity lambda) := by
  have h := congrArg (Measure.map (boundedPast level T))
    (actual_stopped_parabolic_law_eq_weighted_allTimes lambda T)
  rw [Measure.map_map (measurable_boundedPast level T) (measurable_stoppedParabolicPath lambda T),
    Measure.map_map (measurable_boundedPast level T) (BrownianEndpointDriftTilt.measurable_stoppedPath T)] at h
  have hl : (boundedPast level T) ∘ (stoppedParabolicPath lambda T) =
      actualDriverBoundedPast lambda level T := by
    funext f
    rw [Function.comp_apply,stoppedParabolicPath_eq_stopped_actual_drift]
    exact boundedPast_pastPath level T (BrownianPathReflectionLaw.driftPath lambda f)
  have hr : (boundedPast level T) ∘ (BrownianEndpointDriftTilt.stoppedPath T) =
      boundedPast level T := funext (boundedPast_pastPath level T)
  rw [hl,hr] at h
  exact h.trans (density_weighted_boundedPast_law lambda level T)

theorem actual_parabolic_stoppedPassage_lintegral (lambda level : ℝ) (T : ℝ≥0)
    {Φ : ℝ≥0 × Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f : Path, Φ (actualDriverBoundedPast lambda level T f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, stoppedDensity lambda p*Φ p ∂pathLaw.map (boundedPast level T) := by
  rw [← lintegral_map hΦ (measurable_actualDriverBoundedPast lambda level T),
    actual_parabolic_stoppedPassage_law]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity lambda) hΦ

end PerronWright.BrownianParabolicFirstPassageStoppedTilt
