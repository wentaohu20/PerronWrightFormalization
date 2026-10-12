import PerronWright.Probability.BrownianParabolicStoppedTiltGeometry
import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkov

/-! # Actual whole parabolic law from a finite-horizon density

The finite-horizon density depends only on the stopped past, so its true
whole future remains independent Brownian motion. The actual parabolic
future is then given its residual drift lambda - T. Splicing this future
with the density-weighted past proves the whole compact-open Borel law,
including the zero horizon. No infinite-horizon Radon--Nikodym density or
conditional path-law premise is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicWholePathTilt

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicFirstPassagePastFibers BrownianParabolicFirstPassageStrongMarkov

private theorem map_withDensity_pullback {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (fun x ↦ w (f x))).map f = (μ.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ hf]
  change (∫⁻ a, (Φ ∘ f) a ∂μ.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hw.comp hf) (hΦ.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hw hΦ,
    lintegral_map (hw.mul hΦ) hf]
  rfl

theorem actual_density_isProbability_allTimes (lambda : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure (pathLaw.withDensity (density lambda T)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    lintegral_actual_parabolic_density_allTimes]

theorem density_weighted_past_future_jointLaw (lambda : ℝ) (T : ℝ≥0) :
    (pathLaw.withDensity (density lambda T)).map
        (fun f ↦ (pastPath T f,futurePath T f)) =
      ((pathLaw.withDensity (density lambda T)).map (pastPath T)).prod pathLaw := by
  let J : Path → Path × Path := fun f ↦ (pastPath T f,futurePath T f)
  have hJ : Measurable J := (measurable_pastPath T).prodMk (measurable_futurePath T)
  have hW : Measurable (fun z : Path × Path ↦ density lambda T z.1) :=
    (measurable_density lambda T).comp measurable_fst
  have hd : (fun f : Path ↦ density lambda T (pastPath T f)) = density lambda T :=
    funext (density_past lambda T)
  have ha := map_withDensity_pullback pathLaw hJ hW
  change (pathLaw.withDensity (fun f ↦ density lambda T (pastPath T f))).map J =
    (pathLaw.map J).withDensity (fun z : Path × Path ↦ density lambda T z.1) at ha
  rw [hd,past_future_jointLaw] at ha
  have hb := map_withDensity_pullback pathLaw (measurable_pastPath T)
    (measurable_density lambda T)
  rw [hd] at hb
  rw [ha,← prod_withDensity_left (measurable_density lambda T)]
  rw [hb]
  rfl

def shiftedSplice (lambda : ℝ) (T : ℝ≥0) (p : Path × Path) : Path :=
  splicePath T (p.1,driftPath (lambda-(T : ℝ)) p.2)

theorem measurable_shiftedSplice (lambda : ℝ) (T : ℝ≥0) :
    Measurable (shiftedSplice lambda T) :=
  (measurable_splicePath T).comp
    (measurable_fst.prodMk ((measurable_actual_driftPath (lambda-(T : ℝ))).comp measurable_snd))

def wholeLift (lambda : ℝ) (T : ℝ≥0) (f : Path) : Path :=
  shiftedSplice lambda T (pastPath T f,futurePath T f)

theorem measurable_wholeLift (lambda : ℝ) (T : ℝ≥0) : Measurable (wholeLift lambda T) :=
  (measurable_shiftedSplice lambda T).comp
    ((measurable_pastPath T).prodMk (measurable_futurePath T))

private theorem stoppedParabolic_past (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    stoppedParabolicPath lambda T (pastPath T f) = stoppedParabolicPath lambda T f := by
  apply ContinuousMap.ext
  intro t
  change f (min (min t T) T)+lambda*(min t T : ℝ≥0)-(min t T : ℝ≥0)^2/2 = _
  rw [min_assoc,min_self]
  rfl

private theorem shiftedSplice_actual (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    shiftedSplice lambda T (stoppedParabolicPath lambda T f,futurePath T f) =
      driftPath lambda f := by
  have hp : stoppedParabolicPath lambda T f = pastPath T (driftPath lambda f) := rfl
  unfold shiftedSplice
  rw [hp,← actual_drift_futurePath_eq_shift,splice_past_future]

theorem actual_whole_parabolic_law_eq_lift (lambda : ℝ) (T : ℝ≥0) :
    pathLaw.map (driftPath lambda) =
      (pathLaw.withDensity (density lambda T)).map (wholeLift lambda T) := by
  have hν := density_weighted_past_future_jointLaw lambda T
  have hp := actual_stopped_parabolic_law_eq_weighted_allTimes lambda T
  change pathLaw.map (stoppedParabolicPath lambda T) =
    (pathLaw.withDensity (density lambda T)).map (pastPath T) at hp
  have hL := congrArg (Measure.map (shiftedSplice lambda T)) hν
  rw [Measure.map_map (measurable_shiftedSplice lambda T)
    ((measurable_pastPath T).prodMk (measurable_futurePath T)),← hp] at hL
  change (pathLaw.withDensity (density lambda T)).map (wholeLift lambda T) =
    ((pathLaw.map (stoppedParabolicPath lambda T)).prod pathLaw).map (shiftedSplice lambda T) at hL
  have hbase : (pastLaw T).map (stoppedParabolicPath lambda T) =
      pathLaw.map (stoppedParabolicPath lambda T) := by
    rw [pastLaw,Measure.map_map (measurable_stoppedParabolicPath lambda T) (measurable_pastPath T)]
    congr 1
    exact funext (stoppedParabolic_past lambda T)
  have hprod : ((pastLaw T).prod pathLaw).map
      (Prod.map (stoppedParabolicPath lambda T) (id : Path → Path)) =
        (pathLaw.map (stoppedParabolicPath lambda T)).prod pathLaw := by
    rw [← Measure.map_prod_map (pastLaw T) pathLaw
      (measurable_stoppedParabolicPath lambda T) measurable_id,Measure.map_id,hbase]
  have hm : Measurable (Prod.map (stoppedParabolicPath lambda T) (id : Path → Path)) :=
    (measurable_stoppedParabolicPath lambda T).prodMap measurable_id
  rw [← hprod,Measure.map_map (measurable_shiftedSplice lambda T) hm,
    ← past_future_jointLaw T,Measure.map_map ((measurable_shiftedSplice lambda T).comp hm)
      ((measurable_pastPath T).prodMk (measurable_futurePath T))] at hL
  have he : (shiftedSplice lambda T ∘ Prod.map (stoppedParabolicPath lambda T) id) ∘
      (fun f : Path ↦ (pastPath T f,futurePath T f)) = driftPath lambda := by
    funext f
    change shiftedSplice lambda T
      (stoppedParabolicPath lambda T (pastPath T f),futurePath T f) = _
    rw [stoppedParabolic_past]
    exact shiftedSplice_actual lambda T f
  rw [he] at hL
  exact hL.symm

theorem actual_whole_parabolic_lintegral (lambda : ℝ) (T : ℝ≥0)
    {Φ : Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f : Path, Φ (driftPath lambda f) ∂pathLaw) =
      ∫⁻ f : Path, density lambda T f*Φ (wholeLift lambda T f) ∂pathLaw := by
  rw [← lintegral_map hΦ (measurable_actual_driftPath lambda),
    actual_whole_parabolic_law_eq_lift lambda T,
    lintegral_map hΦ (measurable_wholeLift lambda T)]
  change (∫⁻ f, (Φ ∘ wholeLift lambda T) f ∂pathLaw.withDensity (density lambda T)) = _
  rw [lintegral_withDensity_eq_lintegral_mul pathLaw (measurable_density lambda T)
      (hΦ.comp (measurable_wholeLift lambda T))]
  rfl

end PerronWright.BrownianParabolicWholePathTilt
