import PerronWright.Probability.BrownianFullHorizonSpatialSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Literal full spatial Laplace functional on finite time windows

Only finitely many strips can contribute to a test vanishing outside a
finite time window. The actual sampled-measure integral is proved finite
and its exponential factors samplewise. Genuine strip independence then
computes its expectation from the already constructed finite spatial laws.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialLaplace

open BrownianPathLaw BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialIntensity
open BrownianFullHorizonSpatialSupport FinitePointMeasureCompact FinitePoissonPointLaplace

/-- The literal exponential of the integral against the full summed
spatial measure. Window support below proves finiteness almost surely. -/
def spatialLaplace (F : (ℝ × ℝ) → ℝ≥0) (a : SpatialAtoms) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∫⁻ z, (F z : ℝ≥0∞) ∂spatialMeasure a).toReal))

theorem measurable_spatialLaplace {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    Measurable (spatialLaplace F) := by
  have hm := (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp hF)).comp
    measurable_spatialMeasure
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hm.ennreal_toReal.neg)

theorem strip_lintegral_eq_zero_ennreal {G : (ℝ × ℝ) → ℝ≥0∞} (N j : ℕ) (hNj : N ≤ j)
    (hGN : ∀ z, z ∉ timeCut N → G z = 0) (μ : Measure (ℝ × ℝ))
    (hμ : μ (timeStrip j)ᶜ = 0) : (∫⁻ z, G z ∂μ) = 0 := by
  have hs : ∀ᵐ z ∂μ, z ∈ timeStrip j := ae_iff.mpr hμ
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hs] with z hz
  have hN : (N : ℝ) ≤ z.1 := (Nat.cast_le.mpr hNj).trans hz.1
  have hnot : z ∉ timeCut N := not_lt_of_ge hN
  exact hGN z hnot

theorem strip_lintegral_eq_zero {F : (ℝ × ℝ) → ℝ≥0} (N j : ℕ) (hNj : N ≤ j)
    (hFN : ∀ z, z ∉ timeCut N → F z = 0) (μ : Measure (ℝ × ℝ))
    (hμ : μ (timeStrip j)ᶜ = 0) : (∫⁻ z, (F z : ℝ≥0∞) ∂μ) = 0 :=
  strip_lintegral_eq_zero_ennreal N j hNj
    (fun z hz ↦ by simp only [hFN z hz,ENNReal.coe_zero]) μ hμ

theorem spatial_lintegral_eq_finite_sum {F : (ℝ × ℝ) → ℝ≥0}
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0)
    {a : SpatialAtoms} (ha : StripSupported a) :
    (∫⁻ z, (F z : ℝ≥0∞) ∂spatialMeasure a) =
      ∑ j ∈ Finset.range N, ∫⁻ z, (F z : ℝ≥0∞)
        ∂((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) := by
  rw [spatialMeasure,lintegral_sum_measure]
  apply tsum_eq_sum
  intro j hj
  exact strip_lintegral_eq_zero N j
    (Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h))) hFN _ (ha j)

theorem spatial_lintegral_ne_top {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0)
    {a : SpatialAtoms} (ha : StripSupported a) :
    (∫⁻ z, (F z : ℝ≥0∞) ∂spatialMeasure a) ≠ ∞ := by
  rw [spatial_lintegral_eq_finite_sum N hFN ha]
  exact ENNReal.sum_ne_top.mpr (fun j _ ↦ point_lintegral_ne_top hF (a j))

theorem spatialLaplace_eq_finite_prod {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0)
    {a : SpatialAtoms} (ha : StripSupported a) :
    spatialLaplace F a = ∏ j ∈ Finset.range N, laplace F (a j) := by
  unfold spatialLaplace laplace
  rw [spatial_lintegral_eq_finite_sum N hFN ha,
    ENNReal.toReal_sum (fun j _ ↦ point_lintegral_ne_top hF (a j)),
    ← Finset.sum_neg_distrib,Real.exp_sum]
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (Real.exp_pos _).le)

/-- An exact full spatial Laplace calculation from the genuine strip
product law; strip independence is derived, not a supplied hypothesis. -/
theorem spatialLaw_laplace_eq_strip_product (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ a, spatialLaplace F a ∂spatialLaw lambda f) =
      ∏ j ∈ Finset.range N,
        ∫⁻ η, laplace F η ∂BrownianUnderGraphPoissonLaw.law lambda
          (j : ℝ≥0) (j + 1 : ℝ≥0) f := by
  rw [lintegral_congr_ae ((ae_spatialLaw_stripSupported lambda f).mono
    (fun a ha ↦ spatialLaplace_eq_finite_prod hF N hFN ha))]
  have hi := (spatialLaw_strips_independent lambda f).comp
    (fun _ ↦ laplace F) (fun _ ↦ measurable_laplace hF)
  change iIndepFun (fun j (a : SpatialAtoms) ↦ laplace F (a j)) (spatialLaw lambda f) at hi
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (Finset.range N)
    (fun j (a : SpatialAtoms) ↦ laplace F (a j)) hi
    (fun j ↦ (measurable_laplace hF).comp (measurable_pi_apply j))]
  apply Finset.prod_congr rfl
  intro j _
  exact (spatialLaw_hasLaw_strip lambda f j).lintegral_comp (measurable_laplace hF).aemeasurable

/-- The standard nonnegative Poisson killing integrand, defined literally
from the exponential of the specified test. -/
def killing (x : ℝ≥0) : ℝ≥0∞ := 1 - expNeg x

theorem measurable_killing : Measurable killing :=
  measurable_const.sub measurable_expNeg

@[simp] theorem killing_zero : killing 0 = 0 := by
  simp [killing,expNeg]

theorem killing_le_one (x : ℝ≥0) : killing x ≤ 1 := tsub_le_self

theorem finite_killing_lintegral_ne_top (ν : FiniteMeasure (ℝ × ℝ))
    (F : (ℝ × ℝ) → ℝ≥0) : (∫⁻ z, killing (F z) ∂(ν : Measure (ℝ × ℝ))) ≠ ∞ := by
  have hle := lintegral_mono (μ := (ν : Measure (ℝ × ℝ))) (fun z ↦ killing_le_one (F z))
  simp only [lintegral_const,one_mul] at hle
  exact ne_top_of_le_ne_top (measure_ne_top _ _) hle

theorem finite_laplace_exponent (ν : FiniteMeasure (ℝ × ℝ))
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ z, expNeg (F z) ∂(ν : Measure (ℝ × ℝ))).toReal - (ν.mass : ℝ) =
      -(∫⁻ z, killing (F z) ∂(ν : Measure (ℝ × ℝ))).toReal := by
  have hle : (∫⁻ z, expNeg (F z) ∂(ν : Measure (ℝ × ℝ))) ≤
      (ν : Measure (ℝ × ℝ)) univ := by
    calc
      _ ≤ ∫⁻ _z, (1 : ℝ≥0∞) ∂(ν : Measure (ℝ × ℝ)) := lintegral_mono (fun z ↦ expNeg_le_one (F z))
      _ = _ := by simp
  have hn := ne_top_of_le_ne_top (measure_ne_top (ν : Measure (ℝ × ℝ)) univ) hle
  have he : (∫⁻ z, killing (F z) ∂(ν : Measure (ℝ × ℝ))) =
      (ν : Measure (ℝ × ℝ)) univ - ∫⁻ z, expNeg (F z) ∂(ν : Measure (ℝ × ℝ)) := by
    exact (lintegral_sub (measurable_expNeg.comp hF) hn
      (Eventually.of_forall (fun z ↦ expNeg_le_one (F z)))).trans (by simp)
  rw [he,ENNReal.toReal_sub_of_le hle (measure_ne_top _ _),
    ← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
  ring

theorem stripLaw_laplace_killing (lambda : ℝ) (f : Path) (j : ℕ)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ η, laplace F η ∂BrownianUnderGraphPoissonLaw.law lambda
      (j : ℝ≥0) (j + 1 : ℝ≥0) f) = ENNReal.ofReal (Real.exp
        (-(∫⁻ z, killing (F z) ∂(BrownianUnderGraphPoissonLaw.intensity lambda
          (j : ℝ≥0) (j + 1 : ℝ≥0) f : Measure (ℝ × ℝ))).toReal)) := by
  rw [BrownianUnderGraphPoissonLaw.law,FinitePoissonIntensityLaplace.law_laplace _ hF,
    finite_laplace_exponent _ hF]

theorem intensity_killing_lintegral_eq_finite_sum (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ z, killing (F z) ∂intensity lambda f) =
      ∑ j ∈ Finset.range N, ∫⁻ z, killing (F z)
        ∂(BrownianUnderGraphPoissonLaw.intensity lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f :
          Measure (ℝ × ℝ)) := by
  rw [intensity_eq_sum,lintegral_sum_measure]
  apply tsum_eq_sum
  intro j hj
  exact strip_lintegral_eq_zero_ennreal N j
    (Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h)))
    (fun z hz ↦ by rw [hFN z hz,killing_zero]) _
    (strip_intensity_outside_eq_zero lambda f j)

theorem intensity_killing_lintegral_ne_top (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ z, killing (F z) ∂intensity lambda f) ≠ ∞ := by
  rw [intensity_killing_lintegral_eq_finite_sum lambda f N hFN]
  exact ENNReal.sum_ne_top.mpr (fun j _ ↦ finite_killing_lintegral_ne_top _ F)

/-- The actual full random spatial measure has the exact Poisson Laplace
functional against the entire literal under-graph planar intensity. -/
theorem spatialLaw_laplace (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ a, spatialLaplace F a ∂spatialLaw lambda f) =
      ENNReal.ofReal (Real.exp (-(∫⁻ z, killing (F z) ∂intensity lambda f).toReal)) := by
  rw [spatialLaw_laplace_eq_strip_product lambda f hF N hFN]
  simp_rw [stripLaw_laplace_killing lambda f _ hF]
  rw [intensity_killing_lintegral_eq_finite_sum lambda f N hFN,
    ENNReal.toReal_sum (fun j _ ↦ finite_killing_lintegral_ne_top _ F),
    ← Finset.sum_neg_distrib,Real.exp_sum]
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (Real.exp_pos _).le)).symm

theorem intensity_restrict_timeCut (lambda : ℝ) (f : Path) (N : ℕ) :
    (intensity lambda f).restrict (timeCut N) =
      (BrownianUnderGraphPoissonLaw.intensity lambda 0 (N : ℝ≥0) f : Measure (ℝ × ℝ)).restrict
        (timeCut N) := by
  change (volume.restrict (fullRegion lambda f)).restrict (timeCut N) =
    (volume.restrict (BrownianUnderGraphIntensity.region lambda 0 (N : ℝ≥0) f)).restrict (timeCut N)
  rw [Measure.restrict_restrict (measurableSet_timeCut N),
    Measure.restrict_restrict (measurableSet_timeCut N)]
  congr 1
  ext z
  change (z.1 < (N : ℝ) ∧ 0 ≤ z.1 ∧ 0 < z.2 ∧
    z.2 < BrownianReflectedAreaCounts.surface lambda f z.1) ↔
    (z.1 < (N : ℝ) ∧ (0 ≤ z.1 ∧ z.1 ≤ (N : ℝ)) ∧ 0 < z.2 ∧
      z.2 < BrownianReflectedAreaCounts.surface lambda f z.1)
  constructor
  · rintro ⟨hN,h0,hp⟩
    exact ⟨hN,⟨h0,hN.le⟩,hp⟩
  · rintro ⟨hN,⟨h0,_⟩,hp⟩
    exact ⟨hN,h0,hp⟩

theorem killing_lintegral_eq_bounded (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ z, killing (F z) ∂intensity lambda f) =
      ∫⁻ z, killing (F z) ∂(BrownianUnderGraphPoissonLaw.intensity lambda 0 (N : ℝ≥0) f :
        Measure (ℝ × ℝ)) := by
  let G := fun z ↦ killing (F z)
  have he (z : ℝ × ℝ) : G z = (timeCut N).indicator G z := by
    by_cases hz : z ∈ timeCut N
    · exact (indicator_of_mem hz G).symm
    · rw [indicator_of_notMem hz]
      change killing (F z) = 0
      rw [hFN z hz,killing_zero]
  calc
    _ = ∫⁻ z, (timeCut N).indicator G z ∂intensity lambda f := lintegral_congr he
    _ = ∫⁻ z, G z ∂(intensity lambda f).restrict (timeCut N) :=
      lintegral_indicator (measurableSet_timeCut N) G
    _ = ∫⁻ z, G z ∂(BrownianUnderGraphPoissonLaw.intensity lambda 0 (N : ℝ≥0) f :
        Measure (ℝ × ℝ)).restrict (timeCut N) := by rw [intensity_restrict_timeCut]
    _ = ∫⁻ z, (timeCut N).indicator G z
        ∂(BrownianUnderGraphPoissonLaw.intensity lambda 0 (N : ℝ≥0) f : Measure (ℝ × ℝ)) :=
      (lintegral_indicator (measurableSet_timeCut N) G).symm
    _ = _ := lintegral_congr (fun z ↦ (he z).symm)

/-- The full spatial law and the earlier bounded spatial law have exactly
the same actual Laplace functional on tests supported before that horizon. -/
theorem spatialLaw_laplace_eq_bounded (lambda : ℝ) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ a, spatialLaplace F a ∂spatialLaw lambda f) =
      ∫⁻ η, laplace F η ∂BrownianUnderGraphPoissonLaw.law lambda 0 (N : ℝ≥0) f := by
  rw [spatialLaw_laplace lambda f hF N hFN,BrownianUnderGraphPoissonLaw.law,
    FinitePoissonIntensityLaplace.law_laplace _ hF,finite_laplace_exponent _ hF,
    killing_lintegral_eq_bounded lambda f N hFN]

theorem pathJointLaw_laplace (lambda : ℝ)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ p, spatialLaplace F p.2 ∂pathJointLaw lambda) =
      ∫⁻ f, ENNReal.ofReal (Real.exp (-(∫⁻ z, killing (F z) ∂intensity lambda f).toReal)) ∂pathLaw := by
  have hm : Measurable (fun p : Path × SpatialAtoms ↦ spatialLaplace F p.2) :=
    (measurable_spatialLaplace hF).comp measurable_snd
  erw [pathJointLaw,Measure.lintegral_compProd hm]
  exact lintegral_congr (fun f ↦ spatialLaw_laplace lambda f hF N hFN)

theorem actualJointLaw_laplace (lambda : ℝ)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F)
    (N : ℕ) (hFN : ∀ z, z ∉ timeCut N → F z = 0) :
    (∫⁻ p, spatialLaplace F p.2 ∂actualJointLaw lambda) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-(∫⁻ z, killing (F z)
        ∂intensity lambda (measurablePath x)).toReal)) ∂BrownianGaussianSkeleton.rationalLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ) × SpatialAtoms ↦ spatialLaplace F p.2) :=
    (measurable_spatialLaplace hF).comp measurable_snd
  erw [actualJointLaw,Measure.lintegral_compProd hm]
  exact lintegral_congr (fun x ↦ spatialLaw_laplace lambda (measurablePath x) hF N hFN)

end PerronWright.BrownianFullHorizonSpatialLaplace
