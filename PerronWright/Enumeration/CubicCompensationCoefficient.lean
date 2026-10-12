import PerronWright.Enumeration.CubicCompensationOrientation
import PerronWright.Enumeration.CubicCompensationHalfEdgeCount

/-!
# Actual half-edge tables and the cubic coefficient

This finite equivalence retains all vertex and edge labels.  The total cubic
coefficient is computed from labelled half-edge assignments, while the
connected subset is identified with the literal connected compensation sum.
-/

noncomputable section

open scoped BigOperators Classical
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000

namespace PerronWright.GraphCore

/-- Pair the two labelled half-edge sides into their actual unordered edge. -/
def halfEdgeMultiGraph {v e : ℕ} (x : Fin e × Bool → Fin v) :
    PerronWright.FiniteMultiGraph v e :=
  ⟨fun i ↦ s(x (i,false), x (i,true))⟩

theorem halfEdgeMultiGraph_degree {v e : ℕ} (x : Fin e × Bool → Fin v)
    (a : Fin v) :
    (halfEdgeMultiGraph x).degree a = Nat.card {i : Fin e × Bool // x i = a} := by
  unfold PerronWright.FiniteMultiGraph.degree halfEdgeMultiGraph
  simp only [PerronWright.FiniteMultiGraph.incidence_mk]
  have hc : Nat.card {i : Fin e × Bool // x i = a} =
      ∑ i : Fin e × Bool, if x i = a then 1 else 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.univ_bool, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  exact add_comm _ _

/-- Read the two actual endpoint sides of an ordered presentation. -/
def orderedPresentationHalfEdges {v e : ℕ}
    {H : PerronWright.FiniteMultiGraph v e}
    (p : OrderedMultiGraphPresentation H) : Fin e × Bool → Fin v :=
  fun i ↦ if i.2 then (p i.1).val.2 else (p i.1).val.1

theorem halfEdgeMultiGraph_orderedPresentation {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e)
    (p : OrderedMultiGraphPresentation H) :
    halfEdgeMultiGraph (orderedPresentationHalfEdges p) = H := by
  cases H with
  | mk endpoints =>
    unfold halfEdgeMultiGraph
    congr 1
    funext i
    exact (p i).property

/-- All cubic kernels before imposing connectedness. -/
abbrev LabelledCubicKernel (ell : ℕ) :=
  {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell) // ∀ v, H.degree v = 3}

abbrev CubicOrderedPresentation (ell : ℕ) :=
  Σ K : LabelledCubicKernel ell, OrderedMultiGraphPresentation K.val

def cubicOrderedPresentationToHalfEdges (ell : ℕ)
    (p : CubicOrderedPresentation ell) :
    UniformHalfEdgeAssignment (CubicHalfEdgeSlot ell) (Fin (2 * ell)) 3 := by
  refine ⟨orderedPresentationHalfEdges p.2, ?_⟩
  intro v
  rw [← halfEdgeMultiGraph_degree,
    halfEdgeMultiGraph_orderedPresentation p.1.val p.2]
  exact p.1.property v

theorem cubicOrderedPresentationToHalfEdges_bijective (ell : ℕ) :
    Function.Bijective (cubicOrderedPresentationToHalfEdges ell) := by
  constructor
  · rintro ⟨K,p⟩ ⟨K',p'⟩ he
    have hx := congrArg Subtype.val he
    have hK : K = K' := by
      apply Subtype.ext
      rw [← halfEdgeMultiGraph_orderedPresentation K.val p,
        ← halfEdgeMultiGraph_orderedPresentation K'.val p']
      exact congrArg halfEdgeMultiGraph hx
    cases hK
    have hp : p = p' := by
      funext i
      apply Subtype.ext
      apply Prod.ext
      · exact congrFun hx (i,false)
      · exact congrFun hx (i,true)
    cases hp
    rfl
  · intro x
    let K : LabelledCubicKernel ell := ⟨halfEdgeMultiGraph x.val, fun v ↦ by
      rw [halfEdgeMultiGraph_degree]
      exact x.property v⟩
    let p : OrderedMultiGraphPresentation K.val := fun i ↦
      ⟨(x.val (i,false), x.val (i,true)), rfl⟩
    refine ⟨⟨K,p⟩, ?_⟩
    apply Subtype.ext
    funext i
    rcases i with ⟨i,b⟩
    cases b <;> rfl

/-- Exact degree-constrained configuration equivalence; no quotient or
unproved compensation convention enters it. -/
def cubicOrderedPresentationEquivHalfEdges (ell : ℕ) :
    CubicOrderedPresentation ell ≃
      UniformHalfEdgeAssignment (CubicHalfEdgeSlot ell) (Fin (2 * ell)) 3 :=
  Equiv.ofBijective _ (cubicOrderedPresentationToHalfEdges_bijective ell)

theorem card_cubicOrderedPresentation_mul_sixPower (ell : ℕ) :
    Fintype.card (CubicOrderedPresentation ell) * 6 ^ (2 * ell) =
      (6 * ell).factorial := by
  rw [Fintype.card_congr (cubicOrderedPresentationEquivHalfEdges ell)]
  exact card_cubicHalfEdgeAssignment_mul_sixPower ell

/-- The exact rational compensation coefficient, including disconnected
cubic kernels and the empty configuration. -/
def allCubicCompensation (ell : ℕ) : ℝ :=
  ∑ K : LabelledCubicKernel ell,
    (((2 * ell).factorial * (3 * ell).factorial *
      2 ^ Fintype.card (MultiGraphLoopEdge K.val) : ℕ) : ℝ)⁻¹

theorem allCubicCompensation_eq_orderedCard (ell : ℕ) :
    allCubicCompensation ell =
      (Fintype.card (CubicOrderedPresentation ell) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  have ht (K : LabelledCubicKernel ell) :
      ((((2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (MultiGraphLoopEdge K.val) : ℕ) : ℝ)⁻¹) =
      (Fintype.card (OrderedMultiGraphPresentation K.val) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
    have hc := card_orderedMultiGraphPresentation_mul_loopPower K.val
    have hcr : (Fintype.card (OrderedMultiGraphPresentation K.val) : ℝ) *
        (2 : ℝ) ^ Fintype.card (MultiGraphLoopEdge K.val) = 2 ^ (3 * ell) := by
      exact_mod_cast hc
    push_cast
    field_simp
    nlinarith [hcr]
  unfold allCubicCompensation
  simp_rw [ht]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.card_sigma, Nat.cast_sum]

/-- Closed coefficient of the genuine finite cubic compensation sum. -/
theorem allCubicCompensation_eq_factorials (ell : ℕ) :
    allCubicCompensation ell =
      (6 * ell).factorial /
        ((2 * ell).factorial * (3 * ell).factorial *
          (2 : ℝ) ^ (3 * ell) * 6 ^ (2 * ell)) := by
  rw [allCubicCompensation_eq_orderedCard]
  have hc := card_cubicOrderedPresentation_mul_sixPower ell
  have hcr : (Fintype.card (CubicOrderedPresentation ell) : ℝ) *
      (6 : ℝ) ^ (2 * ell) = (6 * ell).factorial := by exact_mod_cast hc
  have hf2 : ((2 * ell).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : ((3 * ell).factorial : ℝ) ≠ 0 := by positivity
  have hp2 : (2 : ℝ) ^ (3 * ell) ≠ 0 := by positivity
  have hp6 : (6 : ℝ) ^ (2 * ell) ≠ 0 := by positivity
  field_simp
  nlinarith [hcr]

end PerronWright.GraphCore
