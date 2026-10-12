import PerronWright.Probability.CountableRealProjectiveLaw
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Literal finite Gaussian grids with Brownian covariance

The laws are actual linear images of Mathlib's constructed finite
Brownian Gaussian measures, including repeated or unordered times.
Normalization, Gaussianity, exact prefix consistency and one-coordinate
and increment distributions are proved. These finite laws are the source
of the ensuing constructed countable Gaussian skeleton, not a postulated
Brownian realization.
-/

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianGaussianGrid

open CountableRealProjectiveLaw ProbabilityTheory.BrownianReal

def gridTimes (t : ℕ → ℝ≥0) (n : ℕ) : Finset ℝ≥0 := (Finset.Iic n).image t

def gridIndex (t : ℕ → ℝ≥0) (n : ℕ) (i : Finset.Iic n) : gridTimes t n :=
  ⟨t i,Finset.mem_image.mpr ⟨i,i.property,rfl⟩⟩

def relabel (t : ℕ → ℝ≥0) (n : ℕ) : ((gridTimes t n) → ℝ) →L[ℝ] Prefix n :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (gridIndex t n i))

@[simp] theorem relabel_apply (t : ℕ → ℝ≥0) (n : ℕ)
    (x : gridTimes t n → ℝ) (i : Finset.Iic n) : relabel t n x i = x (gridIndex t n i) := rfl

/-- A constructed genuine finite-dimensional Gaussian law, not a covariance interface. -/
def gridLaw (t : ℕ → ℝ≥0) (n : ℕ) : Measure (Prefix n) :=
  (projectiveFamily (gridTimes t n)).map (relabel t n)

instance (t : ℕ → ℝ≥0) (n : ℕ) : IsGaussian (gridLaw t n) := by
  unfold gridLaw
  infer_instance

instance (t : ℕ → ℝ≥0) (n : ℕ) : IsProbabilityMeasure (gridLaw t n) := inferInstance

/-- The finite grid laws have their proved exact restriction consistency,
even when the time sequence is neither monotone nor injective. -/
theorem gridLaw_prefix (t : ℕ → ℝ≥0) (a b : ℕ) (hab : a ≤ b) :
    (gridLaw t b).map (frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) hab) = gridLaw t a := by
  have ht : gridTimes t a ⊆ gridTimes t b :=
    Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hab)
  rw [gridLaw,Measure.map_map (measurable_frestrictLe₂ (X := fun _ : ℕ ↦ ℝ) hab)
    (relabel t b).measurable,gridLaw]
  rw [← (measurePreserving_restrict_projectiveFamily ht).map_eq,
    Measure.map_map (relabel t a).measurable (Finset.measurable_restrict₂ ht)]
  congr 1

theorem gridLaw_hasLaw_eval (t : ℕ → ℝ≥0) (n : ℕ) (i : Finset.Iic n) :
    HasLaw (fun x : Prefix n ↦ x i) (gaussianReal 0 (t i)) (gridLaw t n) := by
  refine ⟨(measurable_pi_apply i).aemeasurable,?_⟩
  rw [gridLaw,Measure.map_map (measurable_pi_apply i) (relabel t n).measurable]
  exact (measurePreserving_eval_projectiveFamily (gridIndex t n i)).map_eq

theorem gridLaw_hasLaw_sub (t : ℕ → ℝ≥0) (n : ℕ) (i j : Finset.Iic n) :
    HasLaw (fun x : Prefix n ↦ x i - x j)
      (gaussianReal 0 (nndist (t i).val (t j).val)) (gridLaw t n) := by
  have hs : Measurable (fun x : Prefix n ↦ x i - x j) :=
    (measurable_pi_apply i).sub (measurable_pi_apply j)
  refine ⟨hs.aemeasurable,?_⟩
  rw [gridLaw,Measure.map_map hs (relabel t n).measurable]
  exact (measurePreserving_eval_sub_eval_projectiveFamily (gridTimes t n)
    (gridIndex t n i) (gridIndex t n j)).map_eq

theorem gridLaw_integral_eval (t : ℕ → ℝ≥0) (n : ℕ) (i : Finset.Iic n) :
    (∫ x : Prefix n, x i ∂gridLaw t n) = 0 := by
  rw [(gridLaw_hasLaw_eval t n i).integral_eq,integral_id_gaussianReal]

theorem gridLaw_covariance_eval (t : ℕ → ℝ≥0) (n : ℕ) (i j : Finset.Iic n) :
    cov[fun x : Prefix n ↦ x i,fun x : Prefix n ↦ x j;gridLaw t n] =
      min (t i).val (t j).val := by
  rw [gridLaw,covariance_map (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (relabel t n).measurable.aemeasurable]
  exact covariance_eval_projectiveFamily (gridTimes t n) (gridIndex t n i) (gridIndex t n j)

end PerronWright.BrownianGaussianGrid
