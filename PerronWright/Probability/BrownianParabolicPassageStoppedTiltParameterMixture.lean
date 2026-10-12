import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull

/-! # Actual stopped-driver density with past-dependent drift and level

The independent input parameter is retained. A genuine almost-everywhere
negative-level condition is the domain condition for the scalar hitting
law; the measure change is derived from that proved law and Tonelli.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicPassageStoppedTiltParameterMixture

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassagePastFibers BrownianFirstPassageUncappedLaw
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicFirstPassageStoppedTilt BrownianParabolicFirstPassageStoppedTiltFull

variable {X : Type*} [MeasurableSpace X]

def parameterBrownianPassagePast (level : X → ℝ) (p : X × Path) : X × (ℝ≥0 × Path) :=
  (p.1,passagePast (level p.1) p.2)

def parameterDriverPassagePast (lambda level : X → ℝ) (p : X × Path) : X × (ℝ≥0 × Path) :=
  (p.1,actualDriverPassagePast (lambda p.1) (level p.1) p.2)

def parameterStoppedDensity (lambda : X → ℝ) (p : X × (ℝ≥0 × Path)) : ℝ≥0∞ :=
  density (lambda p.1) p.2.1 p.2.2

theorem measurable_parameterBrownianPassagePast {level : X → ℝ} (hL : Measurable level) :
    Measurable (parameterBrownianPassagePast level) := by
  have ht : Measurable (fun p : X × Path ↦ (firstPassage (level p.1) p.2).toNNReal) :=
    (measurable_joint_firstPassage.comp ((hL.comp measurable_fst).prodMk measurable_snd)).ennreal_toNNReal
  exact measurable_fst.prodMk (ht.prodMk (continuous_joint_pastPath.measurable.comp
    (ht.prodMk measurable_snd)))

theorem measurable_parameterDriverPassagePast {lambda level : X → ℝ}
    (hLambda : Measurable lambda) (hL : Measurable level) :
    Measurable (parameterDriverPassagePast lambda level) := by
  have hd : Measurable (fun p : X × Path ↦ BrownianPathReflectionLaw.driftPath (lambda p.1) p.2) :=
    BrownianPathReflectionLaw.continuous_driftPath.measurable.comp
      ((hLambda.comp measurable_fst).prodMk measurable_snd)
  have ht : Measurable (fun p : X × Path ↦
      (firstPassage (level p.1) (BrownianPathReflectionLaw.driftPath (lambda p.1) p.2)).toNNReal) :=
    (measurable_joint_firstPassage.comp ((hL.comp measurable_fst).prodMk hd)).ennreal_toNNReal
  exact measurable_fst.prodMk (ht.prodMk (continuous_joint_pastPath.measurable.comp
    (ht.prodMk hd)))

theorem measurable_parameterStoppedDensity {lambda : X → ℝ} (hLambda : Measurable lambda) :
    Measurable (parameterStoppedDensity lambda) :=
  measurable_joint_density.comp ((hLambda.comp measurable_fst).prodMk measurable_snd)

theorem actual_parameter_stoppedPassage_lintegral (μ : Measure X) [SFinite μ]
    {lambda level : X → ℝ} (hLambda : Measurable lambda) (hL : Measurable level)
    (hnegative : ∀ᵐ x ∂μ, level x < 0)
    {Φ : X × (ℝ≥0 × Path) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ p : X × Path, Φ (parameterDriverPassagePast lambda level p) ∂μ.prod pathLaw) =
      ∫⁻ p : X × (ℝ≥0 × Path), parameterStoppedDensity lambda p*Φ p
        ∂(μ.prod pathLaw).map (parameterBrownianPassagePast level) := by
  have ha := measurable_parameterDriverPassagePast hLambda hL
  have hb := measurable_parameterBrownianPassagePast hL
  have hm : Measurable (fun p : X × (ℝ≥0 × Path) ↦ parameterStoppedDensity lambda p*Φ p) :=
    (measurable_parameterStoppedDensity hLambda).mul hΦ
  rw [lintegral_map hm hb]
  have hl := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun p : X × Path ↦ Φ (parameterDriverPassagePast lambda level p)) (hΦ.comp ha).aemeasurable
  have hr := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun p : X × Path ↦ parameterStoppedDensity lambda (parameterBrownianPassagePast level p)*
      Φ (parameterBrownianPassagePast level p)) (hm.comp hb).aemeasurable
  rw [hl,hr]
  apply lintegral_congr_ae
  filter_upwards [hnegative] with x hx
  have hFx : Measurable (fun p : ℝ≥0 × Path ↦ Φ (x,p)) :=
    hΦ.comp ((measurable_const : Measurable (fun _ : ℝ≥0 × Path ↦ x)).prodMk measurable_id)
  have he := actual_parabolic_passage_lintegral (lambda x) (level x) hx hFx
  have hWx : Measurable (fun p : ℝ≥0 × Path ↦ stoppedDensity (lambda x) p*Φ (x,p)) :=
    (measurable_stoppedDensity (lambda x)).mul hFx
  rw [lintegral_map hWx (measurable_passagePast (level x))] at he
  exact he

theorem actual_parameter_stoppedPassage_law (μ : Measure X) [SFinite μ]
    {lambda level : X → ℝ} (hLambda : Measurable lambda) (hL : Measurable level)
    (hnegative : ∀ᵐ x ∂μ, level x < 0) :
    (μ.prod pathLaw).map (parameterDriverPassagePast lambda level) =
      ((μ.prod pathLaw).map (parameterBrownianPassagePast level)).withDensity
        (parameterStoppedDensity lambda) := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  rw [lintegral_map hΦ (measurable_parameterDriverPassagePast hLambda hL),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_parameterStoppedDensity hLambda) hΦ]
  exact actual_parameter_stoppedPassage_lintegral μ hLambda hL hnegative hΦ

end PerronWright.BrownianParabolicPassageStoppedTiltParameterMixture
