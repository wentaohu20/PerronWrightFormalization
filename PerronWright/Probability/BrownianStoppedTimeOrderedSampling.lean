import PerronWright.Probability.BrownianStoppedTimePathSampling
import Mathlib.Data.Finset.Sort

/-! # Strictly ordered observations determine a tagged whole-path law

Finite sets remove duplicate observations, and their literal order
isomorphism sorts them. Adding zero and one permits reuse of completed
excursion finite densities without imposing any restriction on tests.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianStoppedTimeOrderedSampling

open BrownianPathLaw BrownianStoppedTimePathSampling

theorem exists_ordered_extension {n : ℕ} (σ : Fin n → ℝ≥0) :
    ∃ (m : ℕ) (τ : Fin m → ℝ≥0), StrictMono τ ∧
      (∃ i, τ i = 0) ∧ (∃ i, τ i = 1) ∧
        ∃ j : Fin n → Fin m, ∀ i, τ (j i) = σ i := by
  let s : Finset ℝ≥0 := insert 0 (insert 1 (Finset.univ.image σ))
  let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
  let τ : Fin s.card → ℝ≥0 := fun i ↦ (e i).1
  have ht : StrictMono τ := (s.orderEmbOfFin rfl).strictMono
  have hm (i : Fin n) : σ i ∈ s := by simp [s]
  have h0 : (0 : ℝ≥0) ∈ s := by simp [s]
  have h1 : (1 : ℝ≥0) ∈ s := by simp [s]
  refine ⟨s.card,τ,ht,?_,?_,fun i ↦ e.symm ⟨σ i,hm i⟩,?_⟩
  · exact ⟨e.symm ⟨0,h0⟩,congrArg Subtype.val (e.apply_symm_apply ⟨0,h0⟩)⟩
  · exact ⟨e.symm ⟨1,h1⟩,congrArg Subtype.val (e.apply_symm_apply ⟨1,h1⟩)⟩
  · intro i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨σ i,hm i⟩)

theorem ext_of_ordered_sample_tests (μ ν : Measure (ℝ≥0 × Path))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (σ : Fin n → ℝ≥0), StrictMono σ →
      (∃ i, σ i = 0) → (∃ i, σ i = 1) →
      ∀ (Ψ : (ℝ≥0 × (Fin n → ℝ)) →ᵇ ℝ≥0),
        (∫⁻ q, Ψ (sample σ q) ∂μ) = ∫⁻ q, Ψ (sample σ q) ∂ν) : μ = ν := by
  apply ext_of_finite_sample_tests
  intro n σ Ψ
  obtain ⟨m,τ,ht,h0,h1,j,hj⟩ := exists_ordered_extension σ
  let C : C(ℝ≥0 × (Fin m → ℝ),ℝ≥0 × (Fin n → ℝ)) :=
    ⟨fun x ↦ (x.1,fun i ↦ x.2 (j i)),continuous_fst.prodMk
      (continuous_pi (fun i ↦ (continuous_apply (j i)).comp continuous_snd))⟩
  have he (q : ℝ≥0 × Path) : C (sample τ q) = sample σ q := by
    change (q.1,fun i ↦ q.2 (τ (j i))) = (q.1,fun i ↦ q.2 (σ i))
    congr 1
    funext i
    exact congrArg q.2 (hj i)
  simpa only [BoundedContinuousFunction.compContinuous_apply,he] using
    h m τ ht h0 h1 (Ψ.compContinuous C)

end PerronWright.BrownianStoppedTimeOrderedSampling
