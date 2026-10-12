import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkov
import PerronWright.Probability.BrownianParabolicFirstPassageFinite
import PerronWright.Probability.BrownianParabolicPassageParameterMeasurability
import PerronWright.Probability.BrownianFirstPassageUncappedLaw

/-! # Actual uncapped parabolic hitting has a whole Brownian future

The finiteness theorem is proved from the genuine Brownian growth, so
every terminal product law here has no finiteness or Markov premise.
The actual driver future has parameter lambda minus its elapsed time.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageStrongMarkovFull

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianParabolicFirstPassagePastFibers BrownianParabolicFirstPassageStrongMarkov
open BrownianParabolicFirstPassageFinite BrownianParabolicPassageParameterMeasurability
open BrownianFirstPassagePastFibers
open BrownianFirstPassageStrongMarkov (brownianProbability)
open BrownianFirstPassageUncappedLaw (tendsto_map_pathLaw_of_ae)

def parabolicPassageTime (lambda level : ℝ) (f : Path) : ℝ≥0 :=
  (firstPassage level (BrownianPathReflectionLaw.driftPath lambda f)).toNNReal

def parabolicPassagePast (lambda level : ℝ) (f : Path) : ℝ≥0 × Path :=
  (parabolicPassageTime lambda level f,pastPath (parabolicPassageTime lambda level f) f)

def parabolicPassageFuture (lambda level : ℝ) (f : Path) : Path :=
  futurePath (parabolicPassageTime lambda level f) f

theorem measurable_parabolicPassageTime (lambda level : ℝ) :
    Measurable (parabolicPassageTime lambda level) :=
  measurable_joint_parabolicPassageTime.comp
    ((measurable_const : Measurable (fun _ : Path ↦ (lambda,level))).prodMk measurable_id)

theorem measurable_parabolicPassagePast (lambda level : ℝ) :
    Measurable (parabolicPassagePast lambda level) :=
  measurable_joint_parabolicPassagePast.comp
    ((measurable_const : Measurable (fun _ : Path ↦ (lambda,level))).prodMk measurable_id)

theorem measurable_parabolicPassageFuture (lambda level : ℝ) :
    Measurable (parabolicPassageFuture lambda level) :=
  measurable_joint_parabolicPassageFuture.comp
    ((measurable_const : Measurable (fun _ : Path ↦ (lambda,level))).prodMk measurable_id)

private theorem cappedTime_eventually_eq (lambda level : ℝ) (f : Path)
    (hfinite : firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, parabolicCappedTime lambda level (n : ℝ≥0) f =
      parabolicPassageTime lambda level f :=
  BrownianFirstPassageUncappedLaw.cappedTime_eventually_eq level
    (BrownianPathReflectionLaw.driftPath lambda f) hfinite

private theorem boundedPast_tendsto (lambda level : ℝ) (f : Path)
    (hfinite : firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ boundedParabolicPast lambda level (n : ℝ≥0) f) atTop
      (𝓝 (parabolicPassagePast lambda level f)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cappedTime_eventually_eq lambda level f hfinite] with n hn
  simp only [boundedParabolicPast,parabolicPassagePast,hn]

private theorem boundedFuture_tendsto (lambda level : ℝ) (f : Path)
    (hfinite : firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ boundedParabolicFuture lambda level (n : ℝ≥0) f) atTop
      (𝓝 (parabolicPassageFuture lambda level f)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cappedTime_eventually_eq lambda level f hfinite] with n hn
  simp only [boundedParabolicFuture,parabolicPassageFuture,hn]

theorem parabolic_passage_jointLaw (lambda level : ℝ) :
    pathLaw.map (fun f ↦ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) =
      (pathLaw.map (parabolicPassagePast lambda level)).prod pathLaw := by
  have hp := measurable_parabolicPassagePast lambda level
  have hf := measurable_parabolicPassageFuture lambda level
  have hfinite := ae_parabolicFirstPassage_ne_top lambda level
  have hwp := tendsto_map_pathLaw_of_ae
    (fun n ↦ boundedParabolicPast lambda level (n : ℝ≥0)) (parabolicPassagePast lambda level)
    (fun n ↦ measurable_boundedParabolicPast _ _ _) hp
    (hfinite.mono (fun f hf ↦ boundedPast_tendsto lambda level f hf))
  have hwj := tendsto_map_pathLaw_of_ae
    (fun n f ↦ (boundedParabolicPast lambda level (n : ℝ≥0) f,
      boundedParabolicFuture lambda level (n : ℝ≥0) f))
    (fun f ↦ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f))
    (fun n ↦ (measurable_boundedParabolicPast _ _ _).prodMk
      (measurable_boundedParabolicFuture _ _ _))
    (hp.prodMk hf) (hfinite.mono (fun f hf ↦
      (boundedPast_tendsto lambda level f hf).prodMk_nhds (boundedFuture_tendsto lambda level f hf)))
  have hwprod := ProbabilityMeasure.continuous_prod.tendsto
    (brownianProbability.map hp.aemeasurable,brownianProbability) |>.comp
      (hwp.prodMk_nhds tendsto_const_nhds)
  have he' (n : ℕ) : brownianProbability.map
      ((measurable_boundedParabolicPast lambda level (n : ℝ≥0)).prodMk
        (measurable_boundedParabolicFuture lambda level (n : ℝ≥0))).aemeasurable =
      ProbabilityMeasure.prod
        (brownianProbability.map (measurable_boundedParabolicPast lambda level (n : ℝ≥0)).aemeasurable)
        brownianProbability := by
    apply Subtype.ext
    exact bounded_parabolic_jointLaw lambda level (n : ℝ≥0)
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hwj (hwprod.congr' (Eventually.of_forall (fun n ↦ (he' n).symm))))

theorem parabolicPassageFuture_law (lambda level : ℝ) :
    pathLaw.map (parabolicPassageFuture lambda level) = pathLaw := by
  have hp := measurable_parabolicPassagePast lambda level
  have hf := measurable_parabolicPassageFuture lambda level
  let : IsProbabilityMeasure (pathLaw.map (parabolicPassagePast lambda level)) :=
    Measure.isProbabilityMeasure_map hp.aemeasurable
  have he := congrArg (Measure.map Prod.snd) (parabolic_passage_jointLaw lambda level)
  rw [Measure.map_map measurable_snd (hp.prodMk hf),Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he

theorem parabolicPassagePast_future_independent (lambda level : ℝ) :
    IndepFun (parabolicPassagePast lambda level) (parabolicPassageFuture lambda level) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_parabolicPassagePast lambda level).aemeasurable
    (measurable_parabolicPassageFuture lambda level).aemeasurable).mpr
  rw [parabolicPassageFuture_law]
  exact parabolic_passage_jointLaw lambda level

theorem ae_parabolicPassageTime_coe_eq (lambda level : ℝ) :
    ∀ᵐ f : Path ∂pathLaw, (parabolicPassageTime lambda level f : ℝ≥0∞) =
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) :=
  (ae_parabolicFirstPassage_ne_top lambda level).mono (fun _ hf ↦ ENNReal.coe_toNNReal hf)

theorem actual_parabolic_passageFuture_lintegral (lambda level : ℝ)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ f : Path, Ψ (parabolicPassagePast lambda level f,
      futurePath (parabolicPassageTime lambda level f) (BrownianPathReflectionLaw.driftPath lambda f))
      ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ g : Path,
        Ψ (p,BrownianPathReflectionLaw.driftPath (lambda-(p.1 : ℝ)) g)
        ∂pathLaw ∂pathLaw.map (parabolicPassagePast lambda level) := by
  let Z : (ℝ≥0 × Path) × Path → (ℝ≥0 × Path) × Path :=
    fun p ↦ (p.1,BrownianPathReflectionLaw.driftPath (lambda-(p.1.1 : ℝ)) p.2)
  have hm : Measurable Z := measurable_fst.prodMk
    (BrownianPathReflectionLaw.continuous_driftPath.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd))
  have hj := (measurable_parabolicPassagePast lambda level).prodMk
    (measurable_parabolicPassageFuture lambda level)
  have he : (∫⁻ f : Path, (Ψ ∘ Z) (parabolicPassagePast lambda level f,
      parabolicPassageFuture lambda level f) ∂pathLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ g : Path, (Ψ ∘ Z) (p,g)
        ∂pathLaw ∂pathLaw.map (parabolicPassagePast lambda level) := by
    rw [← lintegral_map (hΨ.comp hm) hj,parabolic_passage_jointLaw lambda level]
    exact lintegral_prod _ (hΨ.comp hm).aemeasurable
  simpa only [Function.comp_def,Z,actual_drift_futurePath_eq_shift,
    parabolicPassagePast,parabolicPassageFuture] using he

end PerronWright.BrownianParabolicFirstPassageStrongMarkovFull
