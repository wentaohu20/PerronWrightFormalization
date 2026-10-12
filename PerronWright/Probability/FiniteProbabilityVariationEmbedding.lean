import PerronWright.Probability.CountableVariationMarks
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite empirical probability marks in the actual countable TV space

A finite type probability measure is pushed forward along its genuine
natural-type map. The map into countable atomic variation marks is
continuous for the finite weak topology, proved by its actual ell-one
mass vector. Thus continuous countable-mark tests can be applied to the
proved finite coupled-mark asymptotic without a topology interface.
-/

open MeasureTheory Topology
open scoped BigOperators Classical ENNReal
noncomputable section

namespace PerronWright.FiniteProbabilityVariationEmbedding

open CountableVariationMarks

variable {S : Type*} [Fintype S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem continuous_atom_mass (a : S) :
    Continuous (fun μ : ProbabilityMeasure S ↦ (μ : Measure S).real {a}) := by
  let test : C(S, ℝ) := ⟨Set.indicator {a} (fun _ ↦ 1), continuous_of_discreteTopology⟩
  have h := ProbabilityMeasure.continuous_integral_continuousMap test
  change Continuous (fun μ : ProbabilityMeasure S ↦
    ∫ x, Set.indicator ({a} : Set S) (1 : S → ℝ) x ∂(μ : Measure S)) at h
  simpa only [integral_indicator_one (measurableSet_singleton a)] using h

def embed (f : S → ℕ) (μ : ProbabilityMeasure S) : VariationMark :=
  ofProbability (μ.map (measurable_of_countable f).aemeasurable)

theorem embed_val (f : S → ℕ) (μ : ProbabilityMeasure S) :
    (embed f μ).val = μ.map (measurable_of_countable f).aemeasurable := rfl

theorem encoding_embed (f : S → ℕ) (μ : ProbabilityMeasure S) :
    encoding (embed f μ) =
      ∑ s : S, lp.single (1 : ℝ≥0∞) (f s) ((μ : Measure S).real {s}) := by
  apply lp.ext
  funext a
  simp only [encoding, embed, ofProbability, massVector_apply, ProbabilityMeasure.toMeasure_map,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  rw [map_measureReal_apply (measurable_of_countable f) (measurableSet_singleton a)]
  have he : f ⁻¹' {a} = (↑(Finset.univ.filter (fun s : S ↦ f s = a)) : Set S) := by
    ext s
    simp
  rw [he, ← sum_measureReal_singleton]
  simp only [Finset.sum_filter, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : f s = a
  · simp [hs]
  · simp [hs, Ne.symm hs]

theorem continuous_encoding_embed (f : S → ℕ) :
    Continuous (fun μ : ProbabilityMeasure S ↦ encoding (embed f μ)) := by
  simp_rw [encoding_embed]
  apply continuous_finsetSum
  intro s _
  exact (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℝ) (1 : ℝ≥0∞) (f s)).continuous.comp
    (continuous_atom_mass s)

theorem continuous_embed (f : S → ℕ) : Continuous (embed f) := by
  have he : Isometry encoding := fun _ _ ↦ rfl
  exact he.isEmbedding.isInducing.continuous_iff.mpr (continuous_encoding_embed f)

theorem continuous_coupled_test {q : ℕ} (f : S → ℕ)
    (Ψ : (Fin q → VariationMark) → ℝ) (hΨ : Continuous Ψ) :
    Continuous (fun ν : Fin q → ProbabilityMeasure S ↦ Ψ (fun i ↦ embed f (ν i))) :=
  hΨ.comp (continuous_pi (fun i ↦ (continuous_embed f).comp (continuous_apply i)))

end PerronWright.FiniteProbabilityVariationEmbedding
