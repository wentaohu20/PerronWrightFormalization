import PerronWright.Probability.BrownianFullHorizonSpatialKernel
import PerronWright.Probability.BrownianFullHorizonSpatialIntensity

/-!
# Actual strip support, finite windows, and full spatial intensity

The constructed atom family is supported on disjoint half-open strips
almost surely. Its literal summed measure is finite on every bounded
time window, hence sigma-finite. Its true first intensity is exactly unit
planar Lebesgue measure restricted to the entire reflected under-graph.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialSupport

open BrownianPathLaw BrownianGaussianSkeleton FinitePointMeasureCompact
open BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialIntensity

def StripSupported (a : SpatialAtoms) : Prop :=
  ∀ j : ℕ, ((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) (timeStrip j)ᶜ = 0

theorem measurable_stripSupported : Measurable StripSupported := by
  apply Measurable.forall
  intro j
  exact (((FinitePointMeasureMeasurable.measurable_eval (measurableSet_timeStrip j).compl).comp
    (measurable_pi_apply j)).eq measurable_const)

theorem strip_intensity_outside_eq_zero (lambda : ℝ) (f : Path) (j : ℕ) :
    (BrownianUnderGraphPoissonLaw.intensity lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f :
      Measure (ℝ × ℝ)) (timeStrip j)ᶜ = 0 := by
  rw [← restrict_stripRegion,Measure.restrict_apply (measurableSet_timeStrip j).compl]
  have he : (timeStrip j)ᶜ ∩ stripRegion lambda f j = ∅ := by
    ext z
    simp only [stripRegion,mem_inter_iff,mem_compl_iff,mem_empty_iff_false]
    tauto
  rw [he,measure_empty]

theorem ae_strip_law_supported (lambda : ℝ) (f : Path) (j : ℕ) :
    ∀ᵐ η : PointMeasure (ℝ × ℝ) ∂BrownianUnderGraphPoissonLaw.law lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f,
      ((η : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) (timeStrip j)ᶜ = 0 := by
  apply (lintegral_eq_zero_iff
    (FinitePointMeasureMeasurable.measurable_eval (measurableSet_timeStrip j).compl)).mp
  rw [BrownianUnderGraphPoissonLaw.law_lintegral_eval lambda _ _ f
    (measurableSet_timeStrip j).compl]
  have hz := strip_intensity_outside_eq_zero lambda f j
  change volume.restrict (BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f)
    (timeStrip j)ᶜ = 0 at hz
  rwa [Measure.restrict_apply (measurableSet_timeStrip j).compl] at hz

theorem ae_spatialLaw_stripSupported (lambda : ℝ) (f : Path) :
    ∀ᵐ a ∂spatialLaw lambda f, StripSupported a :=
  CountableProductProbabilityKernel.ae_all_coordinates (stripKernel lambda) f
    (fun j η ↦ ((η : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) (timeStrip j)ᶜ = 0)
    (ae_strip_law_supported lambda f)

def timeCut (N : ℕ) : Set (ℝ × ℝ) := {z | z.1 < (N : ℝ)}

theorem measurableSet_timeCut (N : ℕ) : MeasurableSet (timeCut N) :=
  measurableSet_lt measurable_fst measurable_const

/-- On every upper bounded time set only finitely many real strips
contribute. This is an exact samplewise sum, not an integrability input. -/
theorem spatialMeasure_eq_finite_sum {a : SpatialAtoms} (ha : StripSupported a)
    (N : ℕ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    spatialMeasure a A = ∑ j ∈ Finset.range N,
      ((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A := by
  rw [spatialMeasure,Measure.sum_apply _ hA]
  apply tsum_eq_sum
  intro j hj
  have hNj : N ≤ j := Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h))
  apply measure_mono_null _ (ha j)
  intro z hz
  change ¬ z ∈ timeStrip j
  intro hs
  have ht : z.1 < (N : ℝ) := hAN hz
  have hjs : (j : ℝ) ≤ z.1 := hs.1
  have hcast : (N : ℝ) ≤ j := by exact_mod_cast hNj
  linarith

theorem spatialMeasure_ne_top_of_subset {a : SpatialAtoms} (ha : StripSupported a)
    (N : ℕ) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    spatialMeasure a A ≠ ∞ := by
  rw [spatialMeasure_eq_finite_sum ha N hA hAN]
  exact ENNReal.sum_ne_top.mpr (fun j _ ↦ measure_ne_top _ _)

theorem sigmaFinite_spatialMeasure {a : SpatialAtoms} (ha : StripSupported a) :
    SigmaFinite (spatialMeasure a) := by
  refine ⟨⟨⟨timeCut,fun _ ↦ mem_univ _,fun N ↦ ?_,?_⟩⟩⟩
  · exact lt_top_iff_ne_top.mpr
      (spatialMeasure_ne_top_of_subset ha N (measurableSet_timeCut N) subset_rfl)
  · ext z
    simp only [mem_iUnion,mem_univ,iff_true,timeCut,mem_ofPred_eq]
    exact exists_nat_gt z.1

theorem ae_spatialLaw_sigmaFinite (lambda : ℝ) (f : Path) :
    ∀ᵐ a ∂spatialLaw lambda f, SigmaFinite (spatialMeasure a) :=
  (ae_spatialLaw_stripSupported lambda f).mono (fun _ ha ↦ sigmaFinite_spatialMeasure ha)

/-- The actual full-horizon random measure has exactly the literal
under-graph intensity, not just a formal sum of strip intensities. -/
theorem spatialLaw_lintegral_eval_eq_intensity (lambda : ℝ) (f : Path)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ a, spatialMeasure a A ∂spatialLaw lambda f) = intensity lambda f A :=
  (spatialLaw_lintegral_eval lambda f hA).trans (intensity_apply_eq_tsum lambda f hA).symm

theorem ae_pathJointLaw_stripSupported (lambda : ℝ) :
    ∀ᵐ p ∂pathJointLaw lambda, StripSupported p.2 := by
  apply Measure.ae_compProd_of_ae_ae (measurable_stripSupported.comp measurable_snd).setOf
  exact Eventually.of_forall (fun f ↦ ae_spatialLaw_stripSupported lambda f)

theorem ae_actualJointLaw_stripSupported (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, StripSupported p.2 := by
  apply Measure.ae_compProd_of_ae_ae (measurable_stripSupported.comp measurable_snd).setOf
  exact Eventually.of_forall (fun x ↦ ae_spatialLaw_stripSupported lambda (measurablePath x))

theorem pathJointLaw_lintegral_eval (lambda : ℝ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ p, spatialMeasure p.2 A ∂pathJointLaw lambda) = ∫⁻ f, intensity lambda f A ∂pathLaw := by
  have hm : Measurable (fun p : Path × SpatialAtoms ↦ spatialMeasure p.2 A) :=
    ((Measure.measurable_coe hA).comp measurable_spatialMeasure).comp measurable_snd
  erw [pathJointLaw,Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro f
  exact spatialLaw_lintegral_eval_eq_intensity lambda f hA

theorem actualJointLaw_lintegral_eval (lambda : ℝ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ p, spatialMeasure p.2 A ∂actualJointLaw lambda) =
      ∫⁻ x, intensity lambda (measurablePath x) A ∂rationalLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ) × SpatialAtoms ↦ spatialMeasure p.2 A) :=
    ((Measure.measurable_coe hA).comp measurable_spatialMeasure).comp measurable_snd
  erw [actualJointLaw,Measure.lintegral_compProd hm]
  apply lintegral_congr
  intro x
  exact spatialLaw_lintegral_eval_eq_intensity lambda (measurablePath x) hA

end PerronWright.BrownianFullHorizonSpatialSupport
