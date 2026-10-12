import PerronWright.Probability.BrownianPathReflectionLaw
import PerronWright.Probability.PoissonMixedCountLaw
import PerronWright.Probability.CountablePoissonKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual bounded-interval reflected areas and Poisson counts

The rates here are literal Lebesgue integrals of the constructed reflected
Brownian paths. Their measurability is proved, and the previously constructed
Poisson kernel supplies a genuine joint probability law. The independent
counts use the areas of fixed intervals as rates; their interpretation as
counts of one spatial process requires disjoint regions and a further
spatial construction. No spatial process or excursion identity is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.BrownianReflectedAreaCounts

open BrownianPathLaw BrownianPathReflectionLaw
open BrownianGaussianSkeleton BrownianContinuousModification

/-- The literal reflected surface, expressed in real Lebesgue time. -/
def surface (lambda : ℝ) (f : Path) (s : ℝ) : ℝ :=
  driftedReflectionPath lambda f (Real.toNNReal s)

theorem continuous_surface (lambda : ℝ) (f : Path) : Continuous (surface lambda f) := by
  unfold surface
  fun_prop

theorem continuous_joint_surface : Continuous
    (fun p : (ℝ × Path) × ℝ ↦ surface p.1.1 p.1.2 p.2) := by
  unfold surface
  exact continuous_joint_eval.comp
    ((continuous_driftedReflectionPath.comp continuous_fst).prodMk (by fun_prop))

theorem surface_nonneg (lambda : ℝ) (f : Path) (s : ℝ) :
    0 ≤ surface lambda f s := reflectionPath_nonneg _ _

/-- The actual finite area on a bounded interval; the empty interval has area zero. -/
def realArea (lambda : ℝ) (a b : ℝ≥0) (f : Path) : ℝ :=
  ∫ s in Set.Icc (a : ℝ) (b : ℝ), surface lambda f s

theorem integrableOn_surface (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    IntegrableOn (surface lambda f) (Set.Icc (a : ℝ) (b : ℝ)) :=
  (continuous_surface lambda f).integrableOn_Icc

theorem realArea_nonneg (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    0 ≤ realArea lambda a b f := integral_nonneg (surface_nonneg lambda f)

/-- Nonnegative rates carry the actual area, not a clipped substitute. -/
def area (lambda : ℝ) (a b : ℝ≥0) (f : Path) : ℝ≥0 :=
  ⟨realArea lambda a b f,realArea_nonneg lambda a b f⟩

@[simp] theorem coe_area (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    (area lambda a b f : ℝ) = realArea lambda a b f := rfl

/-- Integration is measurable jointly in the actual drift parameter and path. -/
theorem measurable_joint_realArea (a b : ℝ≥0) : Measurable
    (fun p : ℝ × Path ↦ realArea p.1 a b p.2) := by
  exact (continuous_joint_surface.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (a : ℝ) (b : ℝ)))).measurable

theorem measurable_realArea (lambda : ℝ) (a b : ℝ≥0) :
    Measurable (realArea lambda a b) :=
  (measurable_joint_realArea a b).comp (measurable_const.prodMk measurable_id)

theorem measurable_area (lambda : ℝ) (a b : ℝ≥0) : Measurable (area lambda a b) :=
  (measurable_realArea lambda a b).subtype_mk

/-- Actual variable endpoints may themselves be path-dependent. The
integral's joint measurability is proved by a moving-interval indicator. -/
theorem measurable_realArea_all_parameters : Measurable
    (fun p : (ℝ × Path) × (ℝ≥0 × ℝ≥0) ↦ realArea p.1.1 p.2.1 p.2.2 p.1.2) := by
  let D : Set (((ℝ × Path) × (ℝ≥0 × ℝ≥0)) × ℝ) :=
    {p | (p.1.2.1 : ℝ) ≤ p.2 ∧ p.2 ≤ (p.1.2.2 : ℝ)}
  have hD : MeasurableSet D :=
    (measurableSet_le (by fun_prop) measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  let H : ((ℝ × Path) × (ℝ≥0 × ℝ≥0)) × ℝ → ℝ :=
    D.indicator (fun p ↦ surface p.1.1.1 p.1.1.2 p.2)
  have hH : Measurable H :=
    (continuous_joint_surface.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)).indicator hD
  have h := hH.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have he : (fun p : (ℝ × Path) × (ℝ≥0 × ℝ≥0) ↦ ∫ s, H (p,s)) =
      (fun p : (ℝ × Path) × (ℝ≥0 × ℝ≥0) ↦ realArea p.1.1 p.2.1 p.2.2 p.1.2) := by
    funext p
    have hi : (fun s : ℝ ↦ H (p,s)) =
        (Set.Icc (p.2.1 : ℝ) (p.2.2 : ℝ)).indicator (surface p.1.1 p.1.2) := by
      funext s
      rfl
    rw [hi,integral_indicator measurableSet_Icc]
    rfl
  rw [he] at h
  exact h.measurable

theorem measurable_area_all_parameters : Measurable
    (fun p : (ℝ × Path) × (ℝ≥0 × ℝ≥0) ↦ area p.1.1 p.2.1 p.2.2 p.1.2) :=
  measurable_realArea_all_parameters.subtype_mk

/-- One actual full-measure set identifies every interval area with the raw
sampled Brownian reflection, for all drift parameters simultaneously. -/
theorem ae_all_area_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ a b : ℝ≥0,
    (area lambda a b (measurablePath x) : ℝ) =
      ∫ s in Set.Icc (a : ℝ) (b : ℝ),
        ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift lambda (fun t ↦ process t x))
          (Real.toNNReal s) := by
  filter_upwards [ae_all_actual_driftedReflection_eq] with x hx
  intro lambda a b
  apply integral_congr_ae
  filter_upwards with s
  exact hx lambda (Real.toNNReal s)

variable {ι : Type*} [Fintype ι]

def rates (lambda : ℝ) (a b : ι → ℝ≥0) (f : Path) (i : ι) : ℝ≥0 :=
  area lambda (a i) (b i) f

omit [Fintype ι] in
theorem measurable_rates (lambda : ℝ) (a b : ι → ℝ≥0) :
    Measurable (rates lambda a b) :=
  measurable_pi_lambda _ (fun i ↦ measurable_area lambda (a i) (b i))

/-- Conditional on the actual Brownian path, finitely many literal area
rates give actual independent Poisson counts. -/
def jointLaw (lambda : ℝ) (a b : ι → ℝ≥0) : Measure (Path × (ι → ℕ)) :=
  PoissonMixedCountLaw.law pathLaw (rates lambda a b) (measurable_rates lambda a b)

instance (lambda : ℝ) (a b : ι → ℝ≥0) : IsProbabilityMeasure (jointLaw lambda a b) := by
  unfold jointLaw
  infer_instance

theorem jointLaw_source (lambda : ℝ) (a b : ι → ℝ≥0) :
    (jointLaw lambda a b).map Prod.fst = pathLaw :=
  PoissonMixedCountLaw.law_source_marginal _ _ _

theorem jointLaw_source_count_event (lambda : ℝ) (a b : ι → ℝ≥0)
    (s : Set Path) (hs : MeasurableSet s) (n : ι → ℕ) :
    jointLaw lambda a b (s ×ˢ {n}) = ∫⁻ f in s, ∏ i, ENNReal.ofReal
      (Real.exp (-(area lambda (a i) (b i) f : ℝ)) *
        (area lambda (a i) (b i) f : ℝ) ^ n i / ((n i).factorial : ℝ)) ∂pathLaw :=
  PoissonMixedCountLaw.law_source_count_event _ _ _ s hs n

theorem conditional_counts_independent (lambda : ℝ) (a b : ι → ℝ≥0) (f : Path) :
    iIndepFun (fun i (n : ι → ℕ) ↦ n i)
      (PoissonCountKernel.finiteCountLaw (rates lambda a b f)) :=
  PoissonCountKernel.finiteCountLaw_independent _

/-- All actual interval-area rates may be marked simultaneously on one
genuine probability space. No finite-prefix consistency is assumed. -/
def countableJointLaw (lambda : ℝ) (a b : ℕ → ℝ≥0) : Measure (Path × (ℕ → ℕ)) :=
  CountablePoissonKernel.jointLaw pathLaw (rates lambda a b) (measurable_rates lambda a b)

instance (lambda : ℝ) (a b : ℕ → ℝ≥0) : IsProbabilityMeasure (countableJointLaw lambda a b) := by
  unfold countableJointLaw
  infer_instance

theorem countableJointLaw_source (lambda : ℝ) (a b : ℕ → ℝ≥0) :
    (countableJointLaw lambda a b).map Prod.fst = pathLaw :=
  CountablePoissonKernel.jointLaw_source _ _ _

theorem countableJointLaw_finite_count_event (lambda : ℝ) (a b : ℕ → ℝ≥0)
    (s : Set Path) (hs : MeasurableSet s) (I : Finset ℕ) (n : I → ℕ) :
    countableJointLaw lambda a b (s ×ˢ cylinder (α := fun _ : ℕ ↦ ℕ) I {n}) =
      ∫⁻ f in s, ∏ i : I, ENNReal.ofReal
        (Real.exp (-(area lambda (a i) (b i) f : ℝ)) *
          (area lambda (a i) (b i) f : ℝ) ^ n i / ((n i).factorial : ℝ)) ∂pathLaw :=
  CountablePoissonKernel.jointLaw_source_finite_count_event _ _ _ s hs I n

end PerronWright.BrownianReflectedAreaCounts
