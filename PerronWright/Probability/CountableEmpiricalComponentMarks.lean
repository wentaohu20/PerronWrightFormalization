import PerronWright.Probability.CountableEmpiricalGraphLaw
import PerronWright.Probability.CountableVariationMarks

/-! # Literal countable empirical component marks

Embedding the retained finite types into natural types commutes with
the genuine component empirical probability measure. Thus finite-model
marks and the paper's countable marks agree as measures, not merely in
their test averages. Their variation-mark distance to a Perron law is
the actual full atomic absolute variation. No graph-limit claim is made.
-/

open MeasureTheory
open scoped BigOperators Classical
noncomputable section

namespace PerronWright.EmpiricalTypeMarks

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem empiricalMeasure_map {n : ℕ} (x : Fin n → S) (B : Finset (Fin n))
    (f : S → T) (hf : Measurable f) :
    (empiricalMeasure x B).map f = empiricalMeasure (fun v ↦ f (x v)) B := by
  unfold empiricalMeasure
  rw [Measure.map_smul]
  simp only [Measure.map_finset_sum hf.aemeasurable, Measure.map_dirac' hf]

theorem empiricalProbability_map {n : ℕ} (x : Fin n → S) (B : Finset (Fin n))
    (hB : B.Nonempty) (f : S → T) (hf : Measurable f) :
    (empiricalProbability x B hB).map hf.aemeasurable =
      empiricalProbability (fun v ↦ f (x v)) B hB := by
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalMeasure_map x B f hf

theorem componentMark_map {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) (f : S → T) (hf : Measurable f) :
    (componentMark x C).map hf.aemeasurable = componentMark (fun v ↦ f (x v)) C :=
  empiricalProbability_map x _ _ f hf

end PerronWright.EmpiricalTypeMarks

namespace PerronWright.CountableKernel

theorem empiricalVertexTypes_coe (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ) :
    (fun v ↦ (M.empiricalVertexTypes level n v : ℕ)) =
      CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1) := rfl

theorem empiricalVertexTypes_componentMark_map (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) {G : SimpleGraph (Fin (n + 1))} (C : G.ConnectedComponent) :
    (EmpiricalTypeMarks.componentMark (M.empiricalVertexTypes level n) C).map
        (measurable_subtype_coe : Measurable (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ))).aemeasurable =
      EmpiricalTypeMarks.componentMark
        (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) C :=
  EmpiricalTypeMarks.componentMark_map _ C _ measurable_subtype_coe

theorem empiricalVertexTypes_empiricalMeasure_map (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) :
    (EmpiricalTypeMarks.empiricalMeasure (M.empiricalVertexTypes level n) Finset.univ).map
        (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ)) =
      CountableTypeRealization.empiricalMeasure M (level (n + 1)) (n + 1) :=
  EmpiricalTypeMarks.empiricalMeasure_map _ _ _ measurable_subtype_coe

def empiricalVariationComponentMark (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) {G : SimpleGraph (Fin (n + 1))} (C : G.ConnectedComponent) :
    CountableVariationMarks.VariationMark :=
  CountableVariationMarks.ofProbability (EmpiricalTypeMarks.componentMark
    (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) C)

theorem empiricalVariationComponentMark_val (M : CountableKernel) (level : ℕ → ℕ)
    (n : ℕ) {G : SimpleGraph (Fin (n + 1))} (C : G.ConnectedComponent) :
    (M.empiricalVariationComponentMark level n C).val =
      (EmpiricalTypeMarks.componentMark (M.empiricalVertexTypes level n) C).map
        (measurable_subtype_coe : Measurable (fun a : Finset.range (level (n + 1) + 1) ↦ (a : ℕ))).aemeasurable :=
  (M.empiricalVertexTypes_componentMark_map level n C).symm

theorem empiricalVariationComponentMark_dist (M : CountableKernel) (hM : M.IsRegularCritical)
    (level : ℕ → ℕ) (n : ℕ) {G : SimpleGraph (Fin (n + 1))} (C : G.ConnectedComponent) :
    dist (M.empiricalVariationComponentMark level n C)
      (CountableVariationMarks.ofProbability ⟨M.perronLaw hM, inferInstance⟩) =
      ∑' a : ℕ, |(EmpiricalTypeMarks.componentMark
        (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) C : Measure ℕ).real {a} -
        (M.perronLaw hM).real {a}| :=
  CountableVariationMarks.dist_eq_atomic_variation _ _

end PerronWright.CountableKernel
