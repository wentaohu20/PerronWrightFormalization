import PerronWright.Probability.CountableProductProbabilityKernel
import PerronWright.Probability.BrownianUnderGraphSpatialKernel

/-!
# Actual full-horizon spatial atom sampling under the reflected graph

Independent finite spatial laws on the unit time strips construct a
genuine countable family of spatial atoms, a measurable summed random
measure, and actual Brownian-path/Gaussian-source joint probability laws.
Boundary-free strip support and the global Poisson characterization are
proved separately; neither is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialKernel

open BrownianPathLaw BrownianPathReflectionLaw BrownianGaussianSkeleton
open BrownianUnderGraphIntensity FinitePointMeasureCompact

abbrev SpatialAtoms := ℕ → PointMeasure (ℝ × ℝ)

def stripKernel (lambda : ℝ) (j : ℕ) : Kernel Path (PointMeasure (ℝ × ℝ)) :=
  BrownianUnderGraphSpatialKernel.spatialKernel lambda (j : ℝ≥0) (j + 1 : ℝ≥0)

instance (lambda : ℝ) (j : ℕ) : IsMarkovKernel (stripKernel lambda j) := by
  unfold stripKernel
  infer_instance

def spatialLaw (lambda : ℝ) (f : Path) : Measure SpatialAtoms :=
  CountableProductProbabilityKernel.law (stripKernel lambda) f

instance (lambda : ℝ) (f : Path) : IsProbabilityMeasure (spatialLaw lambda f) := by
  unfold spatialLaw
  infer_instance

theorem measurable_spatialLaw (lambda : ℝ) : Measurable (spatialLaw lambda) :=
  CountableProductProbabilityKernel.measurable_law _

def spatialKernel (lambda : ℝ) : Kernel Path SpatialAtoms :=
  CountableProductProbabilityKernel.productKernel (stripKernel lambda)

instance (lambda : ℝ) : IsMarkovKernel (spatialKernel lambda) := by
  unfold spatialKernel
  infer_instance

theorem spatialLaw_hasLaw_strip (lambda : ℝ) (f : Path) (j : ℕ) :
    HasLaw (fun a : SpatialAtoms ↦ a j)
      (BrownianUnderGraphPoissonLaw.law lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) (spatialLaw lambda f) :=
  CountableProductProbabilityKernel.law_hasLaw_eval (stripKernel lambda) f j

theorem spatialLaw_strips_independent (lambda : ℝ) (f : Path) :
    iIndepFun (fun j (a : SpatialAtoms) ↦ a j) (spatialLaw lambda f) :=
  CountableProductProbabilityKernel.law_independent _ _

theorem spatialLaw_map_restrict (lambda : ℝ) (f : Path) (I : Finset ℕ) :
    (spatialLaw lambda f).map I.restrict =
      Measure.pi (fun j : I ↦ BrownianUnderGraphPoissonLaw.law lambda
        (j.val : ℝ≥0) (j.val + 1 : ℝ≥0) f) :=
  CountableProductProbabilityKernel.law_map_restrict _ _ _

/-- The literal sum of all sampled unit-strip atomic measures. -/
def spatialMeasure (a : SpatialAtoms) : Measure (ℝ × ℝ) :=
  Measure.sum (fun j ↦ ((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)))

instance (a : SpatialAtoms) : SFinite (spatialMeasure a) := by
  unfold spatialMeasure
  infer_instance

theorem measurable_spatialMeasure : Measurable spatialMeasure := by
  apply Measure.measurable_measure.mpr
  intro A hA
  simp only [spatialMeasure,Measure.sum_apply _ hA]
  exact Measurable.tsum (fun j ↦
    (FinitePointMeasureMeasurable.measurable_eval hA).comp (measurable_pi_apply j))

theorem spatialLaw_lintegral_eval (lambda : ℝ) (f : Path)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ a, spatialMeasure a A ∂spatialLaw lambda f) =
      ∑' j : ℕ, volume (A ∩ region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) := by
  simp only [spatialMeasure,Measure.sum_apply _ hA]
  have hm : ∀ j : ℕ, AEMeasurable (fun a : SpatialAtoms ↦
      ((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A) (spatialLaw lambda f) :=
    fun j ↦ ((FinitePointMeasureMeasurable.measurable_eval hA).comp
      (measurable_pi_apply j)).aemeasurable
  rw [lintegral_tsum hm]
  apply tsum_congr
  intro j
  rw [(spatialLaw_hasLaw_strip lambda f j).lintegral_comp
    (FinitePointMeasureMeasurable.measurable_eval hA).aemeasurable]
  exact BrownianUnderGraphPoissonLaw.law_lintegral_eval lambda _ _ f hA

def pathJointLaw (lambda : ℝ) : Measure (Path × SpatialAtoms) := pathLaw ⊗ₘ spatialKernel lambda

instance (lambda : ℝ) : IsProbabilityMeasure (pathJointLaw lambda) := by
  unfold pathJointLaw
  infer_instance

theorem pathJointLaw_source (lambda : ℝ) : (pathJointLaw lambda).map Prod.fst = pathLaw :=
  Measure.fst_compProd _ _

theorem pathJointLaw_source_finite_event (lambda : ℝ)
    {A : Set Path} (hA : MeasurableSet A) (I : Finset ℕ)
    {B : Set (I → PointMeasure (ℝ × ℝ))} (hB : MeasurableSet B) :
    pathJointLaw lambda (A ×ˢ cylinder I B) = ∫⁻ f in A,
      Measure.pi (fun j : I ↦ BrownianUnderGraphPoissonLaw.law lambda
        (j.val : ℝ≥0) (j.val + 1 : ℝ≥0) f) B ∂pathLaw :=
  CountableProductProbabilityKernel.jointLaw_source_cylinder _ _ _ hA _ _ hB

def actualSpatialKernel (lambda : ℝ) : Kernel (ℕ → ℝ) SpatialAtoms :=
  ⟨fun x ↦ spatialLaw lambda (measurablePath x),
    (measurable_spatialLaw lambda).comp measurable_measurablePath⟩

instance (lambda : ℝ) : IsMarkovKernel (actualSpatialKernel lambda) :=
  ⟨fun x ↦ inferInstanceAs (IsProbabilityMeasure (spatialLaw lambda (measurablePath x)))⟩

def actualJointLaw (lambda : ℝ) : Measure ((ℕ → ℝ) × SpatialAtoms) :=
  rationalLaw ⊗ₘ actualSpatialKernel lambda

instance (lambda : ℝ) : IsProbabilityMeasure (actualJointLaw lambda) := by
  unfold actualJointLaw
  infer_instance

theorem actualJointLaw_source (lambda : ℝ) : (actualJointLaw lambda).map Prod.fst = rationalLaw :=
  Measure.fst_compProd _ _

theorem actualJointLaw_map_to_path (lambda : ℝ) :
    (actualJointLaw lambda).map (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (measurablePath p.1,p.2)) =
      pathJointLaw lambda := by
  have hm : Measurable (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  ext A hA
  rw [Measure.map_apply hm hA,actualJointLaw,Measure.compProd_apply (hA.preimage hm),
    pathJointLaw,Measure.compProd_apply hA,pathLaw,
    lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := spatialKernel lambda) hA)
      measurable_measurablePath]
  apply lintegral_congr
  intro x
  rfl

theorem hasLaw_actual_path_spatial_pair (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (measurablePath p.1,p.2))
      (pathJointLaw lambda) (actualJointLaw lambda) :=
  ⟨((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd).aemeasurable,
    actualJointLaw_map_to_path lambda⟩

theorem pathJointLaw_hasLaw_finite (lambda : ℝ) (I : Finset ℝ≥0) :
    HasLaw (fun p : Path × SpatialAtoms ↦ I.restrict (fun t ↦ p.1 t))
      (BrownianReal.projectiveFamily I) (pathJointLaw lambda) :=
  (pathLaw_hasLaw_finite I).fun_comp
    (show HasLaw (Prod.fst : Path × SpatialAtoms → Path) pathLaw (pathJointLaw lambda) from
      ⟨measurable_fst.aemeasurable,pathJointLaw_source lambda⟩)

theorem isBrownian_pathJointLaw (lambda : ℝ) :
    IsBrownianReal (fun t (p : Path × SpatialAtoms) ↦ p.1 t) (pathJointLaw lambda) :=
  ⟨⟨pathJointLaw_hasLaw_finite lambda⟩,Eventually.of_forall (fun p ↦ continuous_path p.1)⟩

theorem actualJointLaw_hasLaw_finite (lambda : ℝ) (I : Finset ℝ≥0) :
    HasLaw (fun p : (ℕ → ℝ) × SpatialAtoms ↦ I.restrict (fun t ↦ measurablePath p.1 t))
      (BrownianReal.projectiveFamily I) (actualJointLaw lambda) :=
  (pathJointLaw_hasLaw_finite lambda I).fun_comp (hasLaw_actual_path_spatial_pair lambda)

theorem isBrownian_actualJointLaw (lambda : ℝ) :
    IsBrownianReal (fun t (p : (ℕ → ℝ) × SpatialAtoms) ↦ measurablePath p.1 t)
      (actualJointLaw lambda) :=
  ⟨⟨actualJointLaw_hasLaw_finite lambda⟩,
    Eventually.of_forall (fun p ↦ continuous_path (measurablePath p.1))⟩

end PerronWright.BrownianFullHorizonSpatialKernel
