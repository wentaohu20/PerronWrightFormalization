import PerronWright.Probability.BrownianUnderGraphSpatialKernel

/-!
# Genuine Brownian-source spatial joint laws and their exact observables

The actual Gaussian source plus sampled planar atoms is pushed exactly to
the continuous Brownian path/spatial joint law. The original driver remains
a genuinely continuous Brownian process. Spatial intensity and Laplace
expectations are the proved literal under-graph formulae integrated over
the constructed Brownian source, with no source law, independence, or
normalization interface assumed.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianUnderGraphSpatialJointLaw

open BrownianPathLaw BrownianGaussianSkeleton BrownianUnderGraphSpatialKernel
open BrownianUnderGraphIntensity BrownianReflectedAreaCounts FinitePointMeasureCompact
open FinitePoissonPointLaplace
open BrownianPathReflectionLaw BrownianContinuousModification

/-- The source-space construction and the actual continuous-path
construction are exactly the same joint spatial law after pushforward. -/
theorem actualJointLaw_map_to_path (lambda : ℝ) (a b : ℝ≥0) :
    (actualJointLaw lambda a b).map
      (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ (measurablePath p.1,p.2)) =
      pathJointLaw lambda a b := by
  have hm : Measurable (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦
      (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  ext A hA
  rw [Measure.map_apply hm hA,actualJointLaw,Measure.compProd_apply (hA.preimage hm),
    pathJointLaw,Measure.compProd_apply hA,pathLaw,
    lintegral_map (Kernel.measurable_kernel_prodMk_left (κ := spatialKernel lambda a b) hA)
      measurable_measurablePath]
  apply lintegral_congr
  intro x
  rfl

theorem hasLaw_actual_path_spatial_pair (lambda : ℝ) (a b : ℝ≥0) :
    HasLaw (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ (measurablePath p.1,p.2))
      (pathJointLaw lambda a b) (actualJointLaw lambda a b) :=
  ⟨((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd).aemeasurable,
    actualJointLaw_map_to_path lambda a b⟩

theorem pathJointLaw_hasLaw_finite (lambda : ℝ) (a b : ℝ≥0) (I : Finset ℝ≥0) :
    HasLaw (fun p : Path × PointMeasure (ℝ × ℝ) ↦ I.restrict (fun t ↦ p.1 t))
      (BrownianReal.projectiveFamily I) (pathJointLaw lambda a b) :=
  (pathLaw_hasLaw_finite I).fun_comp
    (show HasLaw (Prod.fst : Path × PointMeasure (ℝ × ℝ) → Path)
      pathLaw (pathJointLaw lambda a b) from
        ⟨measurable_fst.aemeasurable,pathJointLaw_source lambda a b⟩)

theorem isBrownian_pathJointLaw (lambda : ℝ) (a b : ℝ≥0) :
    IsBrownianReal (fun t (p : Path × PointMeasure (ℝ × ℝ)) ↦ p.1 t)
      (pathJointLaw lambda a b) :=
  ⟨⟨pathJointLaw_hasLaw_finite lambda a b⟩,
    Eventually.of_forall (fun p ↦ continuous_path p.1)⟩

theorem actualJointLaw_hasLaw_finite (lambda : ℝ) (a b : ℝ≥0) (I : Finset ℝ≥0) :
    HasLaw (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦
      I.restrict (fun t ↦ measurablePath p.1 t))
      (BrownianReal.projectiveFamily I) (actualJointLaw lambda a b) :=
  (pathJointLaw_hasLaw_finite lambda a b I).fun_comp
    (hasLaw_actual_path_spatial_pair lambda a b)

theorem isBrownian_actualJointLaw (lambda : ℝ) (a b : ℝ≥0) :
    IsBrownianReal (fun t (p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ)) ↦ measurablePath p.1 t)
      (actualJointLaw lambda a b) :=
  ⟨⟨actualJointLaw_hasLaw_finite lambda a b⟩,
    Eventually.of_forall (fun p ↦ continuous_path (measurablePath p.1))⟩

/-- One actual joint full-measure set still identifies every reflection
evaluation, for all drift parameters and real nonnegative times. -/
theorem ae_all_actual_reflection_eq_under_joint (lambda : ℝ) (a b : ℝ≥0) :
    ∀ᵐ p ∂actualJointLaw lambda a b, ∀ c : ℝ, ∀ t : ℝ≥0,
      driftedReflectionPath c (measurablePath p.1) t =
        ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift c (fun s ↦ process s p.1)) t := by
  apply ae_of_ae_map (μ := actualJointLaw lambda a b)
    (f := (Prod.fst : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) → (ℕ → ℝ)))
    (p := fun x : ℕ → ℝ ↦ ∀ c : ℝ, ∀ t : ℝ≥0,
      driftedReflectionPath c (measurablePath x) t =
        ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift c (fun s ↦ process s x)) t)
    measurable_fst.aemeasurable
  rw [actualJointLaw_source]
  exact ae_all_actual_driftedReflection_eq

def rawRegion (lambda : ℝ) (a b : ℝ≥0) (x : ℕ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (a : ℝ) (b : ℝ) ∧ 0 < z.2 ∧ z.2 <
    ContinuousPathReflection.reflected
      (ContinuousPathReflection.parabolicDrift lambda (fun t ↦ process t x))
      (Real.toNNReal z.1)}

theorem ae_all_actual_region_eq_raw_under_joint (lambda : ℝ) (a b : ℝ≥0) :
    ∀ᵐ p ∂actualJointLaw lambda a b, ∀ c : ℝ, ∀ d e : ℝ≥0,
      region c d e (measurablePath p.1) = rawRegion c d e p.1 := by
  filter_upwards [ae_all_actual_reflection_eq_under_joint lambda a b] with p hp
  intro c d e
  ext z
  simp only [region,rawRegion,mem_ofPred_eq,surface,hp c (Real.toNNReal z.1)]

theorem ae_all_actual_area_eq_raw_under_joint (lambda : ℝ) (a b : ℝ≥0) :
    ∀ᵐ p ∂actualJointLaw lambda a b, ∀ c : ℝ, ∀ d e : ℝ≥0,
      (area c d e (measurablePath p.1) : ℝ) =
        ∫ s in Icc (d : ℝ) (e : ℝ), ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift c (fun t ↦ process t p.1))
          (Real.toNNReal s) := by
  apply ae_of_ae_map (μ := actualJointLaw lambda a b)
    (f := (Prod.fst : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) → (ℕ → ℝ)))
    (p := fun x : ℕ → ℝ ↦ ∀ c : ℝ, ∀ d e : ℝ≥0,
      (area c d e (measurablePath x) : ℝ) =
        ∫ s in Icc (d : ℝ) (e : ℝ), ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift c (fun t ↦ process t x))
          (Real.toNNReal s))
    measurable_fst.aemeasurable
  rw [actualJointLaw_source]
  exact ae_all_area_eq_raw

theorem pathJointLaw_lintegral_eval (lambda : ℝ) (a b : ℝ≥0)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ p, ((p.2 : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A
      ∂pathJointLaw lambda a b) =
      ∫⁻ f, volume (A ∩ region lambda a b f) ∂pathLaw := by
  have hm : Measurable (fun p : Path × PointMeasure (ℝ × ℝ) ↦
      ((p.2 : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A) :=
    (FinitePointMeasureMeasurable.measurable_eval hA).comp measurable_snd
  erw [pathJointLaw,Measure.lintegral_compProd hm]
  simp only [spatialKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro f
  exact BrownianUnderGraphPoissonLaw.law_lintegral_eval lambda a b f hA

theorem actualJointLaw_lintegral_eval (lambda : ℝ) (a b : ℝ≥0)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ p, ((p.2 : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A
      ∂actualJointLaw lambda a b) =
      ∫⁻ x, volume (A ∩ region lambda a b (measurablePath x)) ∂rationalLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦
      ((p.2 : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A) :=
    (FinitePointMeasureMeasurable.measurable_eval hA).comp measurable_snd
  erw [actualJointLaw,Measure.lintegral_compProd hm]
  simp only [actualSpatialKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro x
  exact BrownianUnderGraphPoissonLaw.law_lintegral_eval lambda a b (measurablePath x) hA

theorem pathJointLaw_laplace (lambda : ℝ) (a b : ℝ≥0)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ p, laplace F p.2 ∂pathJointLaw lambda a b) =
      ∫⁻ f, ENNReal.ofReal (Real.exp
        ((∫⁻ z in region lambda a b f, expNeg (F z)).toReal - (area lambda a b f : ℝ)))
        ∂pathLaw := by
  have hm : Measurable (fun p : Path × PointMeasure (ℝ × ℝ) ↦ laplace F p.2) :=
    (measurable_laplace hF).comp measurable_snd
  erw [pathJointLaw,Measure.lintegral_compProd hm]
  simp only [spatialKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro f
  exact BrownianUnderGraphPoissonLaw.law_laplace lambda a b f hF

/-- Terminal actual-source spatial Laplace identity, with the literal
reflected Brownian region and area and no abstract process law premise. -/
theorem actualJointLaw_laplace (lambda : ℝ) (a b : ℝ≥0)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ p, laplace F p.2 ∂actualJointLaw lambda a b) =
      ∫⁻ x, ENNReal.ofReal (Real.exp
        ((∫⁻ z in region lambda a b (measurablePath x), expNeg (F z)).toReal -
        (area lambda a b (measurablePath x) : ℝ))) ∂rationalLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ laplace F p.2) :=
    (measurable_laplace hF).comp measurable_snd
  erw [actualJointLaw,Measure.lintegral_compProd hm]
  simp only [actualSpatialKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro x
  exact BrownianUnderGraphPoissonLaw.law_laplace lambda a b (measurablePath x) hF

/-- The exact joint spatial Laplace formula is written entirely with the
literal raw constructed Brownian reflection and its planar under-graph
region. The measurable path version was identified on a proved full set. -/
theorem actualJointLaw_laplace_raw (lambda : ℝ) (a b : ℝ≥0)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ p, laplace F p.2 ∂actualJointLaw lambda a b) =
      ∫⁻ x, ENNReal.ofReal (Real.exp
        ((∫⁻ z in rawRegion lambda a b x, expNeg (F z)).toReal -
          ∫ s in Icc (a : ℝ) (b : ℝ), ContinuousPathReflection.reflected
            (ContinuousPathReflection.parabolicDrift lambda (fun t ↦ process t x))
            (Real.toNNReal s))) ∂rationalLaw := by
  rw [actualJointLaw_laplace lambda a b hF]
  apply lintegral_congr_ae
  filter_upwards [ae_all_actual_driftedReflection_eq,ae_all_area_eq_raw] with x hx ha
  have hr : region lambda a b (measurablePath x) = rawRegion lambda a b x := by
    ext z
    simp only [region,rawRegion,mem_ofPred_eq,surface,hx lambda (Real.toNNReal z.1)]
  rw [hr,ha lambda a b]

end PerronWright.BrownianUnderGraphSpatialJointLaw
