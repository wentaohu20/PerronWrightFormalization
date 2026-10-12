import PerronWright.Model.CountablePerronLawApproximation
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Literal countable probability marks with their atomic-variation metric

A probability measure on natural types is embedded by its actual atom
masses into real ell-one. Pulling back the proved norm metric gives the
full atomic absolute variation metric. Thus previously proved atomic
Perron-law convergence is genuine convergence in an actual mark space,
not an assumed equivalence of mark topologies.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.CountableVariationMarks

/-- Actual probability masses as an ell-one vector. -/
def massVector (μ : ProbabilityMeasure ℕ) : lp (fun _ : ℕ ↦ ℝ) 1 := by
  refine ⟨fun a ↦ (μ : Measure ℕ).real {a}, ?_⟩
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
  have he (a : ℕ) : ‖(μ : Measure ℕ).real {a}‖ = (μ : Measure ℕ).real {a} :=
    Real.norm_of_nonneg measureReal_nonneg
  simpa only [ENNReal.toReal_one, Real.rpow_one, he]
    using (CountableKernel.probability_atomMass_hasSum (μ : Measure ℕ)).summable

@[simp] theorem massVector_apply (μ : ProbabilityMeasure ℕ) (a : ℕ) :
    massVector μ a = (μ : Measure ℕ).real {a} := rfl

theorem massVector_injective : Function.Injective massVector := by
  intro μ ν h
  have : IsProbabilityMeasure (μ : Measure ℕ) := μ.2
  have : IsProbabilityMeasure (ν : Measure ℕ) := ν.2
  have hmeasure : (μ : Measure ℕ) = (ν : Measure ℕ) := by
    apply (ext_iff_measureReal_singleton (μ1 := (μ : Measure ℕ))
      (μ2 := (ν : Measure ℕ))).mpr
    intro a
    exact congrArg (fun f : lp (fun _ : ℕ ↦ ℝ) 1 ↦ f a) h
  exact Subtype.ext hmeasure

theorem norm_massVector_sub (μ ν : ProbabilityMeasure ℕ) :
    ‖massVector μ - massVector ν‖ =
      ∑' a, |(μ : Measure ℕ).real {a} - (ν : Measure ℕ).real {a}| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, one_div_one, Real.rpow_one,
    lp.coeFn_sub, Pi.sub_apply, massVector_apply, Real.norm_eq_abs]

/-- The values are literal probability measures; only the metric is chosen. -/
structure VariationMark where
  val : ProbabilityMeasure ℕ

def ofProbability (μ : ProbabilityMeasure ℕ) : VariationMark := ⟨μ⟩

def encoding (p : VariationMark) : lp (fun _ : ℕ ↦ ℝ) 1 := massVector p.val

theorem encoding_injective : Function.Injective encoding := by
  intro p q h
  cases p
  cases q
  exact congrArg VariationMark.mk (massVector_injective h)

instance : MetricSpace VariationMark := MetricSpace.induced encoding encoding_injective inferInstance

instance : MeasurableSpace VariationMark := borel VariationMark

instance : BorelSpace VariationMark := ⟨rfl⟩

/-- Exact metric: full atomic absolute variation (twice the usual TV convention). -/
theorem dist_eq_atomic_variation (p q : VariationMark) :
    dist p q = ∑' a, |(p.val : Measure ℕ).real {a} - (q.val : Measure ℕ).real {a}| := by
  change dist (massVector p.val) (massVector q.val) = _
  rw [dist_eq_norm, norm_massVector_sub]

/-- Convergence is exactly convergence of the actual full atomic variation. -/
theorem tendsto_iff_atomic_variation (p : ℕ → VariationMark) (q : VariationMark) :
    Tendsto p atTop (𝓝 q) ↔
      Tendsto (fun n ↦ ∑' a,
        |((p n).val : Measure ℕ).real {a} - (q.val : Measure ℕ).real {a}|) atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_atomic_variation]

/-- Every event probability is controlled by the genuine variation-mark distance. -/
theorem event_error_le_dist (p q : VariationMark) (s : Set ℕ) :
    |(p.val : Measure ℕ).real s - (q.val : Measure ℕ).real s| ≤ dist p q := by
  rw [dist_eq_atomic_variation]
  exact CountableKernel.probability_set_error_le_atomic_variation _ _ s

end PerronWright.CountableVariationMarks
