import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull

/-! # True driver-stopped-past and whole future at parabolic passage

The genuine parabolic strong-Markov law initially retains the raw Brownian
stopped past. A literal stopped drift transform retains the driver stopped
past instead. The future raw noise is still an independent whole Brownian
path, and its actual driver has parameter lambda minus the passage time.
No finiteness, stopping-time, or driver-is-Brownian premise is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicPassageDriverFutureLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianFirstPassagePastFibers BrownianParabolicFirstPassagePastFibers
open BrownianParabolicFirstPassageStrongMarkov BrownianParabolicFirstPassageStrongMarkovFull
open BrownianParabolicFirstPassageStoppedTiltFull

private def driverStopped (lambda : ℝ) (p : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (p.1,pastPath p.1 (driftPath lambda p.2))

private theorem measurable_driverStopped (lambda : ℝ) : Measurable (driverStopped lambda) :=
  measurable_fst.prodMk (continuous_joint_pastPath.measurable.comp
    (measurable_fst.prodMk ((measurable_actual_driftPath lambda).comp measurable_snd)))

private theorem driverStopped_actual_past (lambda level : ℝ) (f : Path) :
    driverStopped lambda (parabolicPassagePast lambda level f) =
      actualDriverPassagePast lambda level f := by
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change f (min (min t (parabolicPassageTime lambda level f))
        (parabolicPassageTime lambda level f)) +
      lambda*(min t (parabolicPassageTime lambda level f) : ℝ)-
        (min t (parabolicPassageTime lambda level f) : ℝ)^2/2 = _
    rw [min_assoc,min_self]
    rfl

theorem actual_driver_passage_future_jointLaw (lambda level : ℝ) :
    pathLaw.map (fun f ↦ (actualDriverPassagePast lambda level f,
      parabolicPassageFuture lambda level f)) =
      (pathLaw.map (actualDriverPassagePast lambda level)).prod pathLaw := by
  let e : (ℝ≥0 × Path) × Path → (ℝ≥0 × Path) × Path :=
    Prod.map (driverStopped lambda) id
  have he : Measurable e := (measurable_driverStopped lambda).prodMap measurable_id
  have hj := (measurable_parabolicPassagePast lambda level).prodMk
    (measurable_parabolicPassageFuture lambda level)
  have hp : (pathLaw.map (parabolicPassagePast lambda level)).map (driverStopped lambda) =
      pathLaw.map (actualDriverPassagePast lambda level) := by
    rw [Measure.map_map (measurable_driverStopped lambda) (measurable_parabolicPassagePast lambda level)]
    congr 1
    funext f
    exact driverStopped_actual_past lambda level f
  let : IsProbabilityMeasure (pathLaw.map (parabolicPassagePast lambda level)) :=
    Measure.isProbabilityMeasure_map (measurable_parabolicPassagePast lambda level).aemeasurable
  calc
    _ = pathLaw.map (e ∘ (fun f ↦
        (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f))) := by
      congr 1
      funext f
      exact congrArg (fun p : ℝ≥0 × Path ↦ (p,parabolicPassageFuture lambda level f))
        (driverStopped_actual_past lambda level f).symm
    _ = (pathLaw.map (fun f ↦
        (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f))).map e :=
      (Measure.map_map he hj).symm
    _ = _ := by
      rw [parabolic_passage_jointLaw,← Measure.map_prod_map _ _
        (measurable_driverStopped lambda) measurable_id,Measure.map_id,hp]

theorem actual_driver_passage_future_lintegral (lambda level : ℝ)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (actualDriverPassagePast lambda level f,
      futurePath (parabolicPassageTime lambda level f) (driftPath lambda f)) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ h : Path,
        Ψ (p,driftPath (lambda-(p.1 : ℝ)) h) ∂pathLaw
          ∂pathLaw.map (actualDriverPassagePast lambda level) := by
  let Z : (ℝ≥0 × Path) × Path → (ℝ≥0 × Path) × Path :=
    fun q ↦ (q.1,driftPath (lambda-(q.1.1 : ℝ)) q.2)
  have hZ : Measurable Z := measurable_fst.prodMk
    (continuous_driftPath.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd))
  let : IsProbabilityMeasure (pathLaw.map (actualDriverPassagePast lambda level)) :=
    Measure.isProbabilityMeasure_map (measurable_actualDriverPassagePast lambda level).aemeasurable
  have hj := (measurable_actualDriverPassagePast lambda level).prodMk
    (measurable_parabolicPassageFuture lambda level)
  have he : (∫⁻ f, (Ψ ∘ Z) (actualDriverPassagePast lambda level f,
      parabolicPassageFuture lambda level f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ h : Path, (Ψ ∘ Z) (p,h) ∂pathLaw
        ∂pathLaw.map (actualDriverPassagePast lambda level) := by
    rw [← lintegral_map (hΨ.comp hZ) hj,actual_driver_passage_future_jointLaw]
    exact lintegral_prod _ (hΨ.comp hZ).aemeasurable
  simpa only [Function.comp_def,Z,actual_drift_futurePath_eq_shift,
    actualDriverPassagePast,parabolicPassageFuture,parabolicPassageTime,
    BrownianFirstPassageUncappedLaw.passagePast,BrownianFirstPassageUncappedLaw.passageTime] using he

private theorem measurable_variableSplice :
    Measurable (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

theorem actual_driver_passage_whole_lintegral (lambda level : ℝ)
    {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, F (driftPath lambda f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ h : Path,
        F (splicePath p.1 (p.2,driftPath (lambda-(p.1 : ℝ)) h)) ∂pathLaw
          ∂pathLaw.map (actualDriverPassagePast lambda level) := by
  have he := actual_driver_passage_future_lintegral lambda level (hF.comp measurable_variableSplice)
  calc
    _ = ∫⁻ f, F (splicePath (parabolicPassageTime lambda level f)
        (pastPath (parabolicPassageTime lambda level f) (driftPath lambda f),
          futurePath (parabolicPassageTime lambda level f) (driftPath lambda f))) ∂pathLaw := by
      apply lintegral_congr
      intro f
      rw [splice_past_future]
    _ = _ := he

end PerronWright.BrownianParabolicPassageDriverFutureLaw
