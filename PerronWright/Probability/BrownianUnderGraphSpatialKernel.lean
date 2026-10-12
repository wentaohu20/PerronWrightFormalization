import PerronWright.Probability.BrownianUnderGraphPoissonLaw
import PerronWright.Probability.FinitePoissonPositionKernel

/-!
# Actual random-path spatial Poisson kernels under the reflected graph

The jointly measurable region is the literal under-graph region, and its
restricted Lebesgue measure and normalized iid-position law are proved
measurable, including zero area. The already constructed iid-atom Poisson
law consequently gives a genuine Markov kernel and actual path/spatial
joint probability laws. This is a bounded under-graph construction; no
global spatial process or Brownian excursion-density identity is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianUnderGraphSpatialKernel

open BrownianPathLaw BrownianUnderGraphIntensity BrownianReflectedAreaCounts
open BrownianUnderGraphPoissonLaw FinitePointMeasureCompact BrownianGaussianSkeleton

abbrev Parameters := (ℝ × Path) × (ℝ≥0 × ℝ≥0)

def parameterIntensity (p : Parameters) : FiniteMeasure (ℝ × ℝ) :=
  intensity p.1.1 p.2.1 p.2.2 p.1.2

def parameterRate (p : Parameters) : ℝ≥0 := area p.1.1 p.2.1 p.2.2 p.1.2

theorem parameterIntensity_mass (p : Parameters) :
    (parameterIntensity p).mass = parameterRate p :=
  intensity_mass _ _ _ _

theorem measurable_parameterRate : Measurable parameterRate :=
  measurable_area_all_parameters

/-- Membership in the genuine under-graph region is jointly measurable
in the drift, path, interval endpoints, and the actual spatial location. -/
theorem measurableSet_joint_region : MeasurableSet
    {p : Parameters × (ℝ × ℝ) | p.2 ∈ region p.1.1.1 p.1.2.1 p.1.2.2 p.1.1.2} := by
  have hs : Measurable (fun p : Parameters × (ℝ × ℝ) ↦
      surface p.1.1.1 p.1.1.2 p.2.1) :=
    continuous_joint_surface.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd.fst)
  have ha : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ (p.1.2.1 : ℝ)) := by fun_prop
  have hb : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ (p.1.2.2 : ℝ)) := by fun_prop
  have ht : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.2.1) := by fun_prop
  have hy : Measurable (fun p : Parameters × (ℝ × ℝ) ↦ p.2.2) := by fun_prop
  exact ((measurableSet_le ha ht).inter (measurableSet_le ht hb)).inter
      ((measurableSet_lt measurable_const hy).inter (measurableSet_lt hy hs))

/-- The literal restricted planar measure is a measurable family in its
evaluation sigma algebra. No weak-Borel/Giry identification is assumed. -/
theorem measurable_parameterIntensity_toMeasure : Measurable
    (fun p : Parameters ↦ (parameterIntensity p : Measure (ℝ × ℝ))) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  have hS : MeasurableSet {p : Parameters × (ℝ × ℝ) |
      p.2 ∈ A ∩ region p.1.1.1 p.1.2.1 p.1.2.2 p.1.1.2} :=
    (hA.preimage measurable_snd).inter measurableSet_joint_region
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure (ℝ × ℝ))) hS
  have he : (fun p : Parameters ↦ volume (Prod.mk p ⁻¹'
      {p : Parameters × (ℝ × ℝ) | p.2 ∈ A ∩ region p.1.1.1 p.1.2.1 p.1.2.2 p.1.1.2})) =
      (fun p : Parameters ↦ (parameterIntensity p : Measure (ℝ × ℝ)) A) := by
    funext p
    change volume (A ∩ region p.1.1 p.2.1 p.2.2 p.1.2) =
      volume.restrict (region p.1.1 p.2.1 p.2.2 p.1.2) A
    exact (Measure.restrict_apply hA).symm
  rw [he] at hm
  exact hm

def parameterLocations (p : Parameters) : Measure (ℝ × ℝ) :=
  ((parameterIntensity p).normalize : Measure (ℝ × ℝ))

instance (p : Parameters) : IsProbabilityMeasure (parameterLocations p) :=
  inferInstanceAs (IsProbabilityMeasure ((parameterIntensity p).normalize : Measure (ℝ × ℝ)))

theorem parameterLocations_eq (p : Parameters) :
    parameterLocations p = if parameterRate p = 0 then
      Measure.dirac ((inferInstance : Nonempty (ℝ × ℝ)).some)
    else (parameterRate p)⁻¹ • (parameterIntensity p : Measure (ℝ × ℝ)) := by
  by_cases hp : parameterRate p = 0
  · have hz : (parameterIntensity p).mass = 0 := (parameterIntensity_mass p).trans hp
    simp [parameterLocations,FiniteMeasure.normalize,hz,hp]
  · have hz : (parameterIntensity p).mass ≠ 0 := by rwa [parameterIntensity_mass]
    simpa only [parameterLocations,if_neg hp,parameterIntensity_mass] using
      (parameterIntensity p).toMeasure_normalize_eq_of_nonzero
        ((parameterIntensity p).mass_nonzero_iff.mp hz)

/-- Actual zero-intensity normalization and actual iid location sampling
are both measurable; no normalization witness is supplied as a premise. -/
theorem measurable_parameterLocations : Measurable parameterLocations := by
  have hs : Measurable (fun p : Parameters ↦
      (parameterRate p)⁻¹ • (parameterIntensity p : Measure (ℝ × ℝ))) := by
    apply Measure.measurable_measure.mpr
    intro A hA
    simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
    exact measurable_parameterRate.inv.coe_nnreal_ennreal.mul
      ((Measure.measurable_coe hA).comp measurable_parameterIntensity_toMeasure)
  have he : parameterLocations = fun p : Parameters ↦
      if parameterRate p = 0 then Measure.dirac ((inferInstance : Nonempty (ℝ × ℝ)).some)
      else (parameterRate p)⁻¹ • (parameterIntensity p : Measure (ℝ × ℝ)) :=
    funext parameterLocations_eq
  rw [he]
  exact Measurable.ite (measurable_parameterRate.eq measurable_const).setOf measurable_const hs

theorem measurable_spatialLaw_all_parameters : Measurable
    (fun p : Parameters ↦ BrownianUnderGraphPoissonLaw.law p.1.1 p.2.1 p.2.2 p.1.2) := by
  have hm := FinitePoissonPositionKernel.measurable_law parameterRate parameterLocations
    measurable_parameterRate measurable_parameterLocations
  simpa only [BrownianUnderGraphPoissonLaw.law,FinitePoissonIntensityLaw.law,
    intensity_mass,parameterRate,parameterLocations,parameterIntensity] using hm

theorem measurable_spatialLaw (lambda : ℝ) (a b : ℝ≥0) :
    Measurable (BrownianUnderGraphPoissonLaw.law lambda a b) :=
  measurable_spatialLaw_all_parameters.comp
    (f := fun f : Path ↦ ((lambda,f),(a,b)))
    ((measurable_const.prodMk measurable_id).prodMk measurable_const)

def spatialKernel (lambda : ℝ) (a b : ℝ≥0) : Kernel Path (PointMeasure (ℝ × ℝ)) :=
  ⟨BrownianUnderGraphPoissonLaw.law lambda a b,measurable_spatialLaw lambda a b⟩

instance (lambda : ℝ) (a b : ℝ≥0) : IsMarkovKernel (spatialKernel lambda a b) :=
  ⟨fun f ↦ inferInstanceAs (IsProbabilityMeasure (BrownianUnderGraphPoissonLaw.law lambda a b f))⟩

def pathJointLaw (lambda : ℝ) (a b : ℝ≥0) : Measure (Path × PointMeasure (ℝ × ℝ)) :=
  pathLaw ⊗ₘ spatialKernel lambda a b

instance (lambda : ℝ) (a b : ℝ≥0) : IsProbabilityMeasure (pathJointLaw lambda a b) := by
  unfold pathJointLaw
  infer_instance

theorem pathJointLaw_source (lambda : ℝ) (a b : ℝ≥0) :
    (pathJointLaw lambda a b).map Prod.fst = pathLaw :=
  Measure.fst_compProd _ _

theorem pathJointLaw_source_spatial_event (lambda : ℝ) (a b : ℝ≥0)
    {S : Set Path} (hS : MeasurableSet S) {A : Set (PointMeasure (ℝ × ℝ))} (hA : MeasurableSet A) :
    pathJointLaw lambda a b (S ×ˢ A) =
      ∫⁻ f in S, BrownianUnderGraphPoissonLaw.law lambda a b f A ∂pathLaw :=
  Measure.compProd_apply_prod hS hA

def actualSpatialKernel (lambda : ℝ) (a b : ℝ≥0) :
    Kernel (ℕ → ℝ) (PointMeasure (ℝ × ℝ)) :=
  ⟨fun x ↦ BrownianUnderGraphPoissonLaw.law lambda a b (measurablePath x),
    (measurable_spatialLaw lambda a b).comp measurable_measurablePath⟩

instance (lambda : ℝ) (a b : ℝ≥0) : IsMarkovKernel (actualSpatialKernel lambda a b) :=
  ⟨fun x ↦ inferInstanceAs (IsProbabilityMeasure
    (BrownianUnderGraphPoissonLaw.law lambda a b (measurablePath x)))⟩

def actualJointLaw (lambda : ℝ) (a b : ℝ≥0) :
    Measure ((ℕ → ℝ) × PointMeasure (ℝ × ℝ)) :=
  rationalLaw ⊗ₘ actualSpatialKernel lambda a b

instance (lambda : ℝ) (a b : ℝ≥0) : IsProbabilityMeasure (actualJointLaw lambda a b) := by
  unfold actualJointLaw
  infer_instance

theorem actualJointLaw_source (lambda : ℝ) (a b : ℝ≥0) :
    (actualJointLaw lambda a b).map Prod.fst = rationalLaw :=
  Measure.fst_compProd _ _

theorem actualJointLaw_source_spatial_event (lambda : ℝ) (a b : ℝ≥0)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    {A : Set (PointMeasure (ℝ × ℝ))} (hA : MeasurableSet A) :
    actualJointLaw lambda a b (S ×ˢ A) =
      ∫⁻ x in S, BrownianUnderGraphPoissonLaw.law lambda a b (measurablePath x) A ∂rationalLaw :=
  Measure.compProd_apply_prod hS hA

end PerronWright.BrownianUnderGraphSpatialKernel
