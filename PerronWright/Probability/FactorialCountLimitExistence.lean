import PerronWright.Probability.FactorialCountConvergenceCriterion

/-! # Existence, uniqueness and convergence from actual factorial moments

No target law is supplied. Tightness gives an actual subsequential law;
the proved next-order tail argument passes all moments to it. The summable
series of the numerical limiting moments then identifies this law and
gives convergence of the whole sequence.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section

namespace PerronWright.FactorialCountLimitExistence

open FactorialCountDeterminacy FactorialCountConvergence
  FactorialCountConvergenceCriterion

variable {ι : Type*} [Fintype ι]

theorem isCompact_closure_of_factorialMoments_tendsto
    (μ : ℕ → ProbabilityMeasure (ι → ℕ))
    (hint : ∀ n q, Integrable (factorialPolynomial q) (μ n : Measure (ι → ℕ)))
    (L : (ι → ℕ) → ℝ)
    (hmom : ∀ q, Tendsto (fun n ↦ factorialMoment (μ n) q) atTop (𝓝 (L q))) :
    IsCompact (closure (Set.range μ)) := by
  apply isCompact_closure_of_isTightMeasureSet
  have hrange : {x : Measure (ι → ℕ) | ∃ p ∈ Set.range μ, (p : Measure (ι → ℕ)) = x} =
      Set.range (fun n ↦ (μ n : Measure (ι → ℕ))) := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_range,exists_exists_eq_and]
  rw [hrange]
  exact isTightMeasureSet_of_factorialMoments_tendsto μ hint L hmom

/-- Construction of a genuine limit law from the actual source laws,
not an assumed moment realization. -/
theorem exists_unique_limit_of_factorialMoments
    (μ : ℕ → ProbabilityMeasure (ι → ℕ))
    (hint : ∀ n q, Integrable (factorialPolynomial q) (μ n : Measure (ι → ℕ)))
    (L : (ι → ℕ) → ℝ)
    (hmom : ∀ q, Tendsto (fun n ↦ factorialMoment (μ n) q) atTop (𝓝 (L q)))
    (hseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ)^(∑ i, q i) * L q / ∏ i, ((q i).factorial : ℝ))) :
    ∃! ν : ProbabilityMeasure (ι → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (ι → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (ι → ℕ)) q = L q) ∧
      Tendsto μ atTop (𝓝 ν) := by
  have hcompact := isCompact_closure_of_factorialMoments_tendsto μ hint L hmom
  obtain ⟨ν,_hν,φ,hφ,hweak⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  have hsubmom (q) : Tendsto (fun n ↦ factorialMoment (μ (φ n)) q) atTop (𝓝 (L q)) :=
    (hmom q).comp hφ.tendsto_atTop
  obtain ⟨hνint,hνmom⟩ := moments_pass_to_weak_limit (μ ∘ φ) ν
    (fun n q ↦ hint (φ n) q) L hsubmom hweak
  have hsν : Summable (fun q : ι → ℕ ↦
      (2 : ℝ)^(∑ i, q i) * factorialMoment (ν : Measure (ι → ℕ)) q /
        ∏ i, ((q i).factorial : ℝ)) := by
    simpa only [hνmom] using hseries
  have hlim : Tendsto μ atTop (𝓝 ν) :=
    weak_tendsto_of_factorialMoments_of_target_series μ ν hint hνint
      (fun q ↦ by simpa only [hνmom] using hmom q) hsν
  refine ⟨ν,⟨hνint,hνmom,hlim⟩,?_⟩
  intro ρ hρ
  exact tendsto_nhds_unique hρ.2.2 hlim

end PerronWright.FactorialCountLimitExistence
