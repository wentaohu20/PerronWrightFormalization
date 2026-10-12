import PerronWright.Probability.BrownianParabolicFirstPassageGridStrongMarkov
import PerronWright.Probability.BrownianFirstPassageStrongMarkov

/-! # True whole-future Brownian factorization at bounded parabolic hitting

Actual causal grid laws converge to the capped hitting time of the
parabolic driver. Its post-hitting Brownian future is independent of
the time-tagged past. The actual driver future shifts lambda by that
random elapsed duration, by a proved deterministic path identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFirstPassagePastFibers
open BrownianFirstPassageGridReflection BrownianParabolicFirstPassagePastFibers
open BrownianParabolicFirstPassageGridStrongMarkov
open BrownianFirstPassageStrongMarkov (brownianProbability tendsto_map_pathLaw_of_pointwise)

def boundedParabolicPast (lambda level : ℝ) (T : ℝ≥0) (f : Path) : ℝ≥0 × Path :=
  (parabolicCappedTime lambda level T f,pastPath (parabolicCappedTime lambda level T f) f)

def boundedParabolicFuture (lambda level : ℝ) (T : ℝ≥0) (f : Path) : Path :=
  futurePath (parabolicCappedTime lambda level T f) f

theorem measurable_boundedParabolicPast (lambda level : ℝ) (T : ℝ≥0) :
    Measurable (boundedParabolicPast lambda level T) :=
  (measurable_parabolicCappedTime lambda level T).prodMk (continuous_joint_pastPath.measurable.comp
    ((measurable_parabolicCappedTime lambda level T).prodMk measurable_id))

theorem measurable_boundedParabolicFuture (lambda level : ℝ) (T : ℝ≥0) :
    Measurable (boundedParabolicFuture lambda level T) :=
  continuous_joint_futurePath.measurable.comp
    ((measurable_parabolicCappedTime lambda level T).prodMk measurable_id)

theorem dyadic_parabolicSelectedPast_tendsto (lambda level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ parabolicSelectedPast lambda level (dyadicGrid n)
      (DyadicFloorGeometry.index n T) f) atTop (𝓝 (boundedParabolicPast lambda level T f)) := by
  have ht := dyadic_parabolicSelectedTime_tendsto lambda level T f
  exact ht.prodMk_nhds (continuous_joint_pastPath.tendsto _ |>.comp
    (ht.prodMk_nhds tendsto_const_nhds))

theorem dyadic_parabolicSelectedFuture_tendsto (lambda level : ℝ) (T : ℝ≥0) (f : Path) :
    Tendsto (fun n ↦ parabolicSelectedFuture lambda level (dyadicGrid n)
      (DyadicFloorGeometry.index n T) f) atTop (𝓝 (boundedParabolicFuture lambda level T f)) :=
  continuous_joint_futurePath.tendsto _ |>.comp
    ((dyadic_parabolicSelectedTime_tendsto lambda level T f).prodMk_nhds tendsto_const_nhds)

theorem bounded_parabolic_jointLaw (lambda level : ℝ) (T : ℝ≥0) :
    pathLaw.map (fun f ↦ (boundedParabolicPast lambda level T f,
      boundedParabolicFuture lambda level T f)) =
      (pathLaw.map (boundedParabolicPast lambda level T)).prod pathLaw := by
  have hp := measurable_boundedParabolicPast lambda level T
  have hf := measurable_boundedParabolicFuture lambda level T
  have hj : Measurable (fun f ↦ (boundedParabolicPast lambda level T f,
      boundedParabolicFuture lambda level T f)) := hp.prodMk hf
  have hwp := tendsto_map_pathLaw_of_pointwise
    (fun n ↦ parabolicSelectedPast lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T))
    (boundedParabolicPast lambda level T) (fun n ↦ measurable_parabolicSelectedPast _ _ _ _) hp
    (dyadic_parabolicSelectedPast_tendsto lambda level T)
  have hwj := tendsto_map_pathLaw_of_pointwise
    (fun n f ↦ (parabolicSelectedPast lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T) f,
      parabolicSelectedFuture lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T) f))
    (fun f ↦ (boundedParabolicPast lambda level T f,boundedParabolicFuture lambda level T f))
    (fun n ↦ (measurable_parabolicSelectedPast _ _ _ _).prodMk
      (measurable_parabolicSelectedFuture _ _ _ _)) hj
    (fun f ↦ (dyadic_parabolicSelectedPast_tendsto lambda level T f).prodMk_nhds
      (dyadic_parabolicSelectedFuture_tendsto lambda level T f))
  have hwprod := ProbabilityMeasure.continuous_prod.tendsto
    (brownianProbability.map hp.aemeasurable,brownianProbability) |>.comp
      (hwp.prodMk_nhds tendsto_const_nhds)
  have he (n : ℕ) : brownianProbability.map
      ((measurable_parabolicSelectedPast lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T)).prodMk
        (measurable_parabolicSelectedFuture lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T))).aemeasurable =
      ProbabilityMeasure.prod
        (brownianProbability.map
          (measurable_parabolicSelectedPast lambda level (dyadicGrid n) (DyadicFloorGeometry.index n T)).aemeasurable)
        brownianProbability := by
    apply Subtype.ext
    exact parabolic_selected_jointLaw lambda level (dyadicGrid n) (monotone_dyadicGrid n) _
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hwj (hwprod.congr' (Eventually.of_forall (fun n ↦ (he n).symm))))

theorem boundedParabolicFuture_law (lambda level : ℝ) (T : ℝ≥0) :
    pathLaw.map (boundedParabolicFuture lambda level T) = pathLaw := by
  have hp := measurable_boundedParabolicPast lambda level T
  have hf := measurable_boundedParabolicFuture lambda level T
  let : IsProbabilityMeasure (pathLaw.map (boundedParabolicPast lambda level T)) :=
    Measure.isProbabilityMeasure_map hp.aemeasurable
  have he := congrArg (Measure.map Prod.snd) (bounded_parabolic_jointLaw lambda level T)
  rw [Measure.map_map measurable_snd (hp.prodMk hf),Measure.map_snd_prod,
    measure_univ,one_smul] at he
  exact he

theorem boundedParabolicPast_future_independent (lambda level : ℝ) (T : ℝ≥0) :
    IndepFun (boundedParabolicPast lambda level T) (boundedParabolicFuture lambda level T) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_boundedParabolicPast lambda level T).aemeasurable
    (measurable_boundedParabolicFuture lambda level T).aemeasurable).mpr
  rw [boundedParabolicFuture_law]
  exact bounded_parabolic_jointLaw lambda level T

theorem actual_drift_futurePath_eq_shift (lambda : ℝ) (s : ℝ≥0) (f : Path) :
    futurePath s (BrownianPathReflectionLaw.driftPath lambda f) =
      BrownianPathReflectionLaw.driftPath (lambda-(s : ℝ)) (futurePath s f) := by
  apply ContinuousMap.ext
  intro t
  change (f (s+t)+lambda*(↑s+↑t)-(↑s+↑t)^2/2)-
    (f s+lambda*↑s-(s : ℝ)^2/2) =
    (f (s+t)-f s)+(lambda-(s : ℝ))*(t : ℝ)-(t : ℝ)^2/2
  ring

theorem actual_parabolic_future_lintegral (lambda level : ℝ) (T : ℝ≥0)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ f : Path, Ψ (boundedParabolicPast lambda level T f,
      futurePath (parabolicCappedTime lambda level T f) (BrownianPathReflectionLaw.driftPath lambda f))
      ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ g : Path,
        Ψ (p,BrownianPathReflectionLaw.driftPath (lambda-(p.1 : ℝ)) g)
        ∂pathLaw ∂pathLaw.map (boundedParabolicPast lambda level T) := by
  let Z : (ℝ≥0 × Path) × Path → (ℝ≥0 × Path) × Path :=
    fun p ↦ (p.1,BrownianPathReflectionLaw.driftPath (lambda-(p.1.1 : ℝ)) p.2)
  have hm : Measurable Z := measurable_fst.prodMk
    (BrownianPathReflectionLaw.continuous_driftPath.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd))
  have hj := (measurable_boundedParabolicPast lambda level T).prodMk
    (measurable_boundedParabolicFuture lambda level T)
  have he : (∫⁻ f : Path, (Ψ ∘ Z) (boundedParabolicPast lambda level T f,
      boundedParabolicFuture lambda level T f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ g : Path, (Ψ ∘ Z) (p,g)
        ∂pathLaw ∂pathLaw.map (boundedParabolicPast lambda level T) := by
    rw [← lintegral_map (hΨ.comp hm) hj,bounded_parabolic_jointLaw lambda level T]
    exact lintegral_prod _ (hΨ.comp hm).aemeasurable
  simpa only [Function.comp_def,Z,actual_drift_futurePath_eq_shift,
    boundedParabolicPast,boundedParabolicFuture] using he

end PerronWright.BrownianParabolicFirstPassageStrongMarkov
