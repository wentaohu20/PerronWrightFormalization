import PerronWright.Probability.BrownianGaussianGrid
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Data.Rat.Encodable

/-!
# A constructed genuine Gaussian skeleton at all rational nonnegative times

The sample space is an actual space of real sequences, and its normalized
law is constructed by regular conditional distributions and Ionescu-Tulcea.
Every finite prefix is exactly the literal Brownian Gaussian grid law.
Thus all nonnegative rational times live on one real probability space
with the required Gaussian increments, centered means and min covariance.

This is a countable Gaussian skeleton, not a continuous Brownian motion
realization. Continuous extension, excursion structure and Poisson
marking are deliberately not asserted.
-/

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianGaussianSkeleton

open CountableRealProjectiveLaw BrownianGaussianGrid

/-- Genuine normalized infinite-sequence law, from actual Gaussian
finite laws and their proved exact consistency. -/
def law (t : ℕ → ℝ≥0) : Measure (ℕ → ℝ) := CountableRealProjectiveLaw.law (gridLaw t)

instance (t : ℕ → ℝ≥0) : IsProbabilityMeasure (law t) := by
  unfold law
  infer_instance

theorem law_prefix (t : ℕ → ℝ≥0) (n : ℕ) :
    (law t).map (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) = gridLaw t n :=
  CountableRealProjectiveLaw.law_prefix (gridLaw t) (gridLaw_prefix t) n

theorem hasLaw_prefix (t : ℕ → ℝ≥0) (n : ℕ) :
    HasLaw (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) (gridLaw t n) (law t) :=
  ⟨(measurable_frestrictLe (X := fun _ : ℕ ↦ ℝ) n).aemeasurable,law_prefix t n⟩

theorem hasLaw_eval (t : ℕ → ℝ≥0) (i : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ x i) (gaussianReal 0 (t i)) (law t) := by
  simpa only [Function.comp_def,frestrictLe_apply] using
    (gridLaw_hasLaw_eval t i ⟨i,Finset.mem_Iic.mpr le_rfl⟩).comp (hasLaw_prefix t i)

theorem hasLaw_sub (t : ℕ → ℝ≥0) (i j : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ x i - x j)
      (gaussianReal 0 (nndist (t i).val (t j).val)) (law t) := by
  simpa only [Function.comp_def,frestrictLe_apply] using
    (gridLaw_hasLaw_sub t (max i j)
      ⟨i,Finset.mem_Iic.mpr (le_max_left i j)⟩
      ⟨j,Finset.mem_Iic.mpr (le_max_right i j)⟩).comp (hasLaw_prefix t (max i j))

theorem integral_eval (t : ℕ → ℝ≥0) (i : ℕ) : (∫ x, x i ∂law t) = 0 := by
  rw [(hasLaw_eval t i).integral_eq,integral_id_gaussianReal]

theorem covariance_eval (t : ℕ → ℝ≥0) (i j : ℕ) :
    cov[fun x : ℕ → ℝ ↦ x i,fun x : ℕ → ℝ ↦ x j;law t] = min (t i).val (t j).val := by
  let i' : Finset.Iic (max i j) := ⟨i,Finset.mem_Iic.mpr (le_max_left i j)⟩
  let j' : Finset.Iic (max i j) := ⟨j,Finset.mem_Iic.mpr (le_max_right i j)⟩
  calc
    _ = cov[fun x : Prefix (max i j) ↦ x i',fun x : Prefix (max i j) ↦ x j';gridLaw t (max i j)] := by
      simpa only [Function.comp_apply,frestrictLe_apply] using
        (hasLaw_prefix t (max i j)).covariance_fun_comp
          (f := fun x : Prefix (max i j) ↦ x i') (g := fun x : Prefix (max i j) ↦ x j')
          (measurable_pi_apply i').aemeasurable (measurable_pi_apply j').aemeasurable
    _ = _ := gridLaw_covariance_eval t (max i j) i' j'

def restrictFinite (I : Finset ℕ) : Prefix (I.sup id) →L[ℝ] (I → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj
    ⟨i,I.subset_Iic_sup_id i.property⟩)

/-- This is Gaussianity of an actually constructed process on an actual
probability law, not a predicate supplied as a realization hypothesis. -/
theorem isGaussianProcess (t : ℕ → ℝ≥0) : IsGaussianProcess (fun i (x : ℕ → ℝ) ↦ x i) (law t) := by
  constructor
  intro I
  constructor
  have he : (fun x : ℕ → ℝ ↦ I.restrict (fun i ↦ x i)) =
      restrictFinite I ∘ frestrictLe (π := fun _ : ℕ ↦ ℝ) (I.sup id) := rfl
  rw [he,← Measure.map_map (restrictFinite I).measurable
    (measurable_frestrictLe (X := fun _ : ℕ ↦ ℝ) (I.sup id)),law_prefix]
  infer_instance

abbrev RationalTime := {q : ℚ // 0 ≤ q}

def rationalTimeReal (q : RationalTime) : ℝ≥0 := ⟨(q.val : ℝ),Rat.cast_nonneg.mpr q.property⟩

def rationalTimes (n : ℕ) : ℝ≥0 :=
  rationalTimeReal ((Encodable.decode n : Option RationalTime).getD ⟨0,by norm_num⟩)

@[simp] theorem rationalTimes_encode (q : RationalTime) :
    rationalTimes (Encodable.encode q) = rationalTimeReal q := by
  simp [rationalTimes,Encodable.encodek]

def rationalLaw : Measure (ℕ → ℝ) := law rationalTimes

instance : IsProbabilityMeasure rationalLaw := by unfold rationalLaw; infer_instance

def rationalProcess (q : RationalTime) (x : ℕ → ℝ) : ℝ := x (Encodable.encode q)

theorem rational_isGaussianProcess : IsGaussianProcess rationalProcess rationalLaw :=
  (isGaussianProcess rationalTimes).comp_right Encodable.encode

theorem rational_hasLaw_eval (q : RationalTime) :
    HasLaw (rationalProcess q) (gaussianReal 0 (rationalTimeReal q)) rationalLaw := by
  change HasLaw (fun x : ℕ → ℝ ↦ x (Encodable.encode q))
    (gaussianReal 0 (rationalTimeReal q)) (law rationalTimes)
  simpa only [rationalTimes_encode] using
    hasLaw_eval rationalTimes (Encodable.encode q)

theorem rational_hasLaw_sub (q r : RationalTime) :
    HasLaw (fun x ↦ rationalProcess q x - rationalProcess r x)
      (gaussianReal 0 (nndist (q.val : ℝ) (r.val : ℝ))) rationalLaw := by
  simpa only [rationalProcess,rationalLaw,rationalTimes_encode,rationalTimeReal] using
    hasLaw_sub rationalTimes (Encodable.encode q) (Encodable.encode r)

theorem rational_integral_eval (q : RationalTime) : (∫ x, rationalProcess q x ∂rationalLaw) = 0 := by
  rw [(rational_hasLaw_eval q).integral_eq,integral_id_gaussianReal]

theorem rational_covariance_eval (q r : RationalTime) :
    cov[rationalProcess q,rationalProcess r;rationalLaw] = min (q.val : ℝ) (r.val : ℝ) := by
  change cov[fun x : ℕ → ℝ ↦ x (Encodable.encode q),fun x : ℕ → ℝ ↦ x (Encodable.encode r);law rationalTimes] = _
  simpa only [rationalTimes_encode,rationalTimeReal] using
    covariance_eval rationalTimes (Encodable.encode q) (Encodable.encode r)

end PerronWright.BrownianGaussianSkeleton
