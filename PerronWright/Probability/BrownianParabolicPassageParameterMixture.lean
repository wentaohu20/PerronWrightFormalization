import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkovFull

/-! # True parabolic whole-future factorization with past-measurable parameters

The parameter is retained in the stopped-past factor. The input measure
is a genuine independent parameter/Brownian product; no drifted-process
Brownian law or conditional Markov assertion is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicPassageParameterMixture

open BrownianPathLaw BrownianPathIndependentIncrements
open BrownianParabolicFirstPassageStrongMarkovFull BrownianParabolicFirstPassageStrongMarkov
open BrownianParabolicPassageParameterMeasurability

variable {X : Type*} [MeasurableSpace X]

def parameterPassagePast (lambda level : X → ℝ) (p : X × Path) : X × (ℝ≥0 × Path) :=
  (p.1,parabolicPassagePast (lambda p.1) (level p.1) p.2)

def parameterPassageFuture (lambda level : X → ℝ) (p : X × Path) : Path :=
  parabolicPassageFuture (lambda p.1) (level p.1) p.2

theorem measurable_parameterPassagePast {lambda level : X → ℝ}
    (hLambda : Measurable lambda) (hL : Measurable level) :
    Measurable (parameterPassagePast lambda level) :=
  measurable_fst.prodMk (measurable_joint_parabolicPassagePast.comp
    (((hLambda.comp measurable_fst).prodMk (hL.comp measurable_fst)).prodMk measurable_snd))

theorem measurable_parameterPassageFuture {lambda level : X → ℝ}
    (hLambda : Measurable lambda) (hL : Measurable level) :
    Measurable (parameterPassageFuture lambda level) :=
  measurable_joint_parabolicPassageFuture.comp
    (((hLambda.comp measurable_fst).prodMk (hL.comp measurable_fst)).prodMk measurable_snd)

theorem parameter_passage_jointLaw (μ : Measure X) [SFinite μ]
    {lambda level : X → ℝ} (hLambda : Measurable lambda) (hL : Measurable level) :
    (μ.prod pathLaw).map (fun p ↦ (parameterPassagePast lambda level p,
      parameterPassageFuture lambda level p)) =
      ((μ.prod pathLaw).map (parameterPassagePast lambda level)).prod pathLaw := by
  have hp := measurable_parameterPassagePast hLambda hL
  have hf := measurable_parameterPassageFuture hLambda hL
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  have hi : Measurable (fun p : X × (ℝ≥0 × Path) ↦ ∫⁻ g : Path, Φ (p,g) ∂pathLaw) :=
    hΦ.lintegral_prod_right'
  rw [lintegral_map hΦ (hp.prodMk hf)]
  have hl := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun p : X × Path ↦ Φ (parameterPassagePast lambda level p,parameterPassageFuture lambda level p))
    (hΦ.comp (hp.prodMk hf)).aemeasurable
  rw [hl,lintegral_prod _ hΦ.aemeasurable,lintegral_map hi hp]
  have hr := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun p : X × Path ↦ ∫⁻ g : Path, Φ (parameterPassagePast lambda level p,g) ∂pathLaw)
    (hi.comp hp).aemeasurable
  rw [hr]
  apply lintegral_congr
  intro x
  have hm : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ Φ ((x,p.1),p.2)) :=
    hΦ.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hj := (measurable_parabolicPassagePast (lambda x) (level x)).prodMk
    (measurable_parabolicPassageFuture (lambda x) (level x))
  change (∫⁻ f : Path, Φ ((x,parabolicPassagePast (lambda x) (level x) f),
      parabolicPassageFuture (lambda x) (level x) f) ∂pathLaw) =
    ∫⁻ f : Path, ∫⁻ g : Path, Φ ((x,parabolicPassagePast (lambda x) (level x) f),g) ∂pathLaw ∂pathLaw
  rw [← lintegral_map hm hj,parabolic_passage_jointLaw,lintegral_prod _ hm.aemeasurable]
  exact lintegral_map (hi.comp (measurable_const.prodMk measurable_id))
    (measurable_parabolicPassagePast (lambda x) (level x))

theorem actual_parameter_parabolic_future_lintegral (μ : Measure X) [SFinite μ]
    {lambda level : X → ℝ} (hLambda : Measurable lambda) (hL : Measurable level)
    {Ψ : (X × (ℝ≥0 × Path)) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ p : X × Path, Ψ (parameterPassagePast lambda level p,
      futurePath (parabolicPassageTime (lambda p.1) (level p.1) p.2)
        (BrownianPathReflectionLaw.driftPath (lambda p.1) p.2)) ∂μ.prod pathLaw) =
      ∫⁻ p : X × (ℝ≥0 × Path), ∫⁻ g : Path,
        Ψ (p,BrownianPathReflectionLaw.driftPath (lambda p.1-(p.2.1 : ℝ)) g)
        ∂pathLaw ∂(μ.prod pathLaw).map (parameterPassagePast lambda level) := by
  let Z : (X × (ℝ≥0 × Path)) × Path → (X × (ℝ≥0 × Path)) × Path :=
    fun p ↦ (p.1,BrownianPathReflectionLaw.driftPath (lambda p.1.1-(p.1.2.1 : ℝ)) p.2)
  have hm : Measurable Z := measurable_fst.prodMk
    (BrownianPathReflectionLaw.continuous_driftPath.measurable.comp
      (((hLambda.comp measurable_fst.fst).sub
        (NNReal.continuous_coe.measurable.comp measurable_fst.snd.fst)).prodMk measurable_snd))
  have hj := (measurable_parameterPassagePast hLambda hL).prodMk
    (measurable_parameterPassageFuture hLambda hL)
  have he : (∫⁻ p : X × Path, (Ψ ∘ Z) (parameterPassagePast lambda level p,
      parameterPassageFuture lambda level p) ∂μ.prod pathLaw) =
      ∫⁻ p : X × (ℝ≥0 × Path), ∫⁻ g : Path, (Ψ ∘ Z) (p,g)
        ∂pathLaw ∂(μ.prod pathLaw).map (parameterPassagePast lambda level) := by
    rw [← lintegral_map (hΨ.comp hm) hj,parameter_passage_jointLaw μ hLambda hL]
    exact lintegral_prod _ (hΨ.comp hm).aemeasurable
  simpa only [Function.comp_def,Z,actual_drift_futurePath_eq_shift,
    parameterPassagePast,parameterPassageFuture,parabolicPassagePast,parabolicPassageFuture] using he

end PerronWright.BrownianParabolicPassageParameterMixture
