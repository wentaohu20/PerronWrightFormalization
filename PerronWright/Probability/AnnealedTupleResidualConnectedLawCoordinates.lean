import PerronWright.Probability.AnnealedTupleResidualConnectedLawWeights
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Literal product-law coordinates for selected component types and graphs
-/

open MeasureTheory Measure
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualConnectedLawCoordinates

open AnnealedGraph ComponentCounts ExactFactorialExpectation
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawGraphTuple AnnealedTupleResidualConnectedLawWeights
open AnnealedTupleResidualConnectedLawProduct

/-- Distribute a dependent product of type/graph pairs into its two
dependent coordinate vectors. -/
def dependentPiProd {I : Type*} (X Y : I → Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] :
    ((i : I) → X i × Y i) ≃ᵐ (((i : I) → X i) × ((i : I) → Y i)) where
  toFun p := (fun i ↦ (p i).1,fun i ↦ (p i).2)
  invFun p := fun i ↦ (p.1 i,p.2 i)
  left_inv p := by funext i; exact Prod.eta _
  right_inv p := by cases p; rfl
  measurable_toFun := by
    change Measurable (fun p : (i : I) → X i × Y i ↦ (fun i ↦ (p i).1,fun i ↦ (p i).2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ((i : I) → X i) × ((i : I) → Y i) ↦ fun i ↦ (p.1 i,p.2 i))
    fun_prop

/-- Measure preservation is proved on rectangles, including dependent
component sizes; it is not an independence premise. -/
theorem measurePreserving_dependentPiProd {I : Type*} [Fintype I]
    {X Y : I → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : I) → Measure (X i)) (ν : (i : I) → Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiProd X Y) (Measure.pi (fun i ↦ (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentPiProd X Y).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s,⟨s,_,rfl⟩,⟨_,⟨t,_,rfl⟩,rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show dependentPiProd X Y ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
        ext p
        simp [dependentPiProd,Set.mem_pi,forall_and]]
      simp_rw [Measure.pi_pi,Measure.prod_prod,Measure.pi_pi,Finset.prod_mul_distrib]

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Reconstruct the actual selected-union type vector from per-block types. -/
def selectedTypes {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (x : (i : Fin q) → Fin (k i) → S) :
    ↥(selectedUnion (blocksOfPlacement hk f)) → S :=
  fun v ↦ x ((selectedVerticesEquiv hk f).symm v).1 ((selectedVerticesEquiv hk f).symm v).2

omit [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem blockTypes_selectedTypes {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (x : (i : Fin q) → Fin (k i) → S) :
    blockTypes hk f (selectedTypes hk f x) = x := by
  funext i a
  unfold blockTypes selectedTypes
  rw [(selectedVerticesEquiv hk f).symm_apply_apply ⟨i,a⟩]

/-- The literal selected type law becomes the literal product of component
type laws, using the proved placement bijection and finite dependent curry. -/
theorem integral_selectedTypes {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (F : (↥(selectedUnion (blocksOfPlacement hk f)) → S) → ℝ) :
    (∫ x : (i : Fin q) → Fin (k i) → S, F (selectedTypes hk f x)
      ∂Measure.pi (fun i ↦ typeLaw M (k i))) =
      ∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S, F u ∂Measure.pi (fun _ ↦ M.mu) := by
  let e : ((SelectedVertices k → S) ≃ᵐ ((i : Fin q) → Fin (k i) → S)) :=
    MeasurableEquiv.piCurry (fun _ _ ↦ S)
  have hmap : (Measure.pi (fun _ : SelectedVertices k ↦ M.mu)).map e =
      Measure.pi (fun i ↦ typeLaw M (k i)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry (μ := fun (i : Fin q) (_a : Fin (k i)) ↦ M.mu))
  have hc : MeasurePreserving e (Measure.pi (fun _ : SelectedVertices k ↦ M.mu))
      (Measure.pi (fun i ↦ typeLaw M (k i))) := ⟨e.measurable,hmap⟩
  have hr := measurePreserving_piCongrLeft (fun _ : ↥(selectedUnion (blocksOfPlacement hk f)) ↦ M.mu)
    (selectedVerticesEquiv hk f)
  calc
    _ = ∫ z : SelectedVertices k → S, F (selectedTypes hk f (e z))
        ∂Measure.pi (fun _ ↦ M.mu) := (hc.integral_comp' _).symm
    _ = _ := by
      convert hr.integral_comp' F using 1
      congr 1
      funext z
      congr 1
      funext v
      have hv := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ↥(selectedUnion (blocksOfPlacement hk f)) ↦ S) (selectedVerticesEquiv hk f) z
        ((selectedVerticesEquiv hk f).symm v)
      rw [(selectedVerticesEquiv hk f).apply_symm_apply v] at hv
      exact hv.symm

theorem pi_graph_count {q : ℕ} (k : Fin q → ℕ) :
    Measure.pi (fun i ↦ (Measure.count : Measure (SimpleGraph (Fin (k i))))) =
      (Measure.count : Measure (GraphTuple k)) := by
  apply Measure.ext_of_singleton
  intro H
  simp only [Measure.pi_singleton,Measure.count_singleton,Finset.prod_const_one]

/-- The literal unweighted component-state product splits into its type
vector and finite labelled graph tuple; this follows from the proved
dependent-product rectangle calculation and singleton counting. -/
theorem baseLaw_coordinates {q : ℕ} (M : CompactBJRModel S) (k : Fin q → ℕ) :
    MeasurePreserving
      (dependentPiProd (fun i : Fin q ↦ Fin (k i) → S)
        (fun i : Fin q ↦ SimpleGraph (Fin (k i))))
      (baseLaw M k)
      ((Measure.pi (fun i ↦ typeLaw M (k i))).prod Measure.count) := by
  have h := measurePreserving_dependentPiProd
    (fun i : Fin q ↦ typeLaw M (k i))
    (fun i : Fin q ↦ (Measure.count : Measure (SimpleGraph (Fin (k i)))))
  rw [pi_graph_count] at h
  exact h

def tupleState {q : ℕ} {k : Fin q → ℕ}
    (x : (i : Fin q) → Fin (k i) → S) (H : GraphTuple k) : TupleState S k :=
  fun i ↦ (x i,H i)

def residualObservable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (s₀ : S) (p : TupleState S k) : ℝ :=
  selectedResidual M t hk f (fun i ↦ (p i).2)
    (selectedTypes hk f (fun i ↦ (p i).1)) s₀

/-- General finite-graph Fubini on the genuine component-state product.
The only regularity assumptions here are ordinary measurability and
integrability of the concrete observable slices. -/
theorem integral_baseLaw_eq_sum_graph_integrals {q : ℕ}
    (M : CompactBJRModel S) (k : Fin q → ℕ) (W : TupleState S k → ℝ)
    (hm : ∀ H : GraphTuple k, Measurable (fun x ↦ W (tupleState x H)))
    (hi : ∀ H : GraphTuple k, Integrable (fun x ↦ W (tupleState x H))
      (Measure.pi (fun i ↦ typeLaw M (k i)))) :
    (∫ p, W p ∂baseLaw M k) =
      ∑ H : GraphTuple k, ∫ x : (i : Fin q) → Fin (k i) → S,
        W (tupleState x H) ∂Measure.pi (fun i ↦ typeLaw M (k i)) := by
  let e := dependentPiProd (fun i : Fin q ↦ Fin (k i) → S)
    (fun i : Fin q ↦ SimpleGraph (Fin (k i)))
  have hwm : Measurable (fun p : ((i : Fin q) → Fin (k i) → S) × GraphTuple k ↦ W (e.symm p)) :=
    measurable_from_prod_countable_left hm
  have hwi : Integrable (fun p : ((i : Fin q) → Fin (k i) → S) × GraphTuple k ↦ W (e.symm p))
      ((Measure.pi (fun i ↦ typeLaw M (k i))).prod Measure.count) := by
    apply (integrable_prod_iff' hwm.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall hi,Integrable.of_finite⟩
  calc
    _ = ∫ p, W (e.symm p)
        ∂((Measure.pi (fun i ↦ typeLaw M (k i))).prod Measure.count) := by
      have h := (baseLaw_coordinates M k).integral_comp' (fun p ↦ W (e.symm p))
      change (∫ p, W (e.symm (e p)) ∂baseLaw M k) = _ at h
      simpa only [MeasurableEquiv.symm_apply_apply] using h
    _ = _ := by rw [integral_prod_symm _ hwi,integral_count]; rfl

end PerronWright.AnnealedTupleResidualConnectedLawCoordinates
