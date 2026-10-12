import PerronWright.Probability.EmpiricalTypeMarks
import Mathlib.Order.Filter.Pi

/-!
# Finite-test control of actual weak probability-measure neighborhoods

This module proves, rather than assumes, the finite-test criterion for
concentration in the weak topology of `ProbabilityMeasure`.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped Topology BigOperators

noncomputable section

namespace PerronWright.EmpiricalWeakNeighborhood

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]

/-- Every genuine weak neighborhood of a probability measure contains
a neighborhood specified by finitely many continuous integral tests. -/
theorem exists_finite_tests_of_mem_nhds (ν : ProbabilityMeasure S)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 ν) :
    ∃ F : Finset (S →ᵇ ℝ), ∃ ε : (S →ᵇ ℝ) → ℝ,
      (∀ f ∈ F, 0 < ε f) ∧ ∀ μ : ProbabilityMeasure S,
        (∀ f ∈ F, |(∫ x, f x ∂(μ : Measure S)) - ∫ x, f x ∂(ν : Measure S)| < ε f) → μ ∈ U := by
  classical
  let T : ProbabilityMeasure S → ((S →ᵇ ℝ) → ℝ) :=
    fun μ f ↦ ∫ x, f x ∂(μ : Measure S)
  have ht : Tendsto (id : ProbabilityMeasure S → ProbabilityMeasure S)
      (comap T (𝓝 (T ν))) (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact (show Continuous (fun z : ((S →ᵇ ℝ) → ℝ) ↦ z f) from continuous_apply f).continuousAt.tendsto.comp
      (show Tendsto T (comap T (𝓝 (T ν))) (𝓝 (T ν)) from tendsto_comap)
  have hu : U ∈ comap T (𝓝 (T ν)) := ht hU
  obtain ⟨V, hV, hVU⟩ := mem_comap.mp hu
  have hVp : V ∈ Filter.pi (fun f ↦ 𝓝 (T ν f)) := by rwa [← nhds_pi]
  obtain ⟨⟨F, ε⟩, ⟨hF, hε⟩, hFV⟩ :=
    (Filter.hasBasis_pi (fun f ↦ Metric.nhds_basis_ball (x := T ν f))).mem_iff.mp hVp
  refine ⟨hF.toFinset, ε, ?_, ?_⟩
  · intro f hf
    exact hε f (hF.mem_toFinset.mp hf)
  · intro μ hμ
    apply hVU
    apply hFV
    intro f hf
    rw [Metric.mem_ball, Real.dist_eq]
    exact hμ f (hF.mem_toFinset.mpr hf)

/-- Scalar concentration for every bounded continuous test implies
concentration in every genuine weak neighborhood. The sampling
spaces may depend on the index; no weak metric or convergence
interface is postulated. -/
theorem probability_outside_nhds_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (htest : ∀ f : S →ᵇ ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (μ n).real
        {ω | ε ≤ |(∫ x, f x ∂(X n ω : Measure S)) - ∫ x, f x ∂(ν : Measure S)|})
        atTop (𝓝 0))
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 ν) :
    Tendsto (fun n ↦ (μ n).real {ω | X n ω ∉ U}) atTop (𝓝 0) := by
  classical
  obtain ⟨F, ε, hε, hFU⟩ := exists_finite_tests_of_mem_nhds ν U hU
  let A : ∀ n, (S →ᵇ ℝ) → Set (Ω n) := fun n f ↦
    {ω | ε f ≤ |(∫ x, f x ∂(X n ω : Measure S)) - ∫ x, f x ∂(ν : Measure S)|}
  have hs : Tendsto (fun n ↦ ∑ f ∈ F, (μ n).real (A n f)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum F (fun f hf ↦ htest f (ε f) (hε f hf))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hs
  exact Eventually.of_forall (fun n ↦ by
    have : IsFiniteMeasure (μ n) := (‹∀ n, IsFiniteMeasure (μ n)› n)
    have hsubset : {ω | X n ω ∉ U} ⊆ ⋃ f ∈ F, A n f := by
      intro ω hω
      by_contra hbad
      apply hω
      apply hFU
      intro f hf
      have hn : ω ∉ A n f := by
        intro hm
        apply hbad
        exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hm⟩⟩
      exact lt_of_not_ge hn
    exact (measureReal_mono hsubset (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le F _))

end PerronWright.EmpiricalWeakNeighborhood
