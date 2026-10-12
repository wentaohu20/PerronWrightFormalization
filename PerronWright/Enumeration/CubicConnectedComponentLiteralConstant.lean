import PerronWright.Enumeration.CubicConnectedComponentFactorization
import PerronWright.Enumeration.PerronWrightFormulaMainTerm

/-!
# Literal connected compensation and connected half-edge tables

This finite bijection identifies the connected table counts in the root
decomposition with the unchanged labelled-kernel compensation constants.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

def connectedCubicOrderedToHalfEdges (ell : ℕ)
    (p : ConnectedCubicOrderedPresentation ell) :
    ConnectedCubicHalfEdgeTable (Fin (2 * ell)) (Fin (3 * ell)) := by
  refine ⟨⟨orderedPresentationHalfEdges p.2,?_⟩,?_⟩
  · intro v
    rw [← halfEdgeMultiGraph_degree,halfEdgeMultiGraph_orderedPresentation p.1.graph p.2]
    exact p.1.cubic v
  · rw [orderedPresentationHalfEdges_support p.1.graph p.2]
    exact p.1.connected

theorem connectedCubicOrderedToHalfEdges_bijective (ell : ℕ) :
    Function.Bijective (connectedCubicOrderedToHalfEdges ell) := by
  constructor
  · rintro ⟨K,p⟩ ⟨K',p'⟩ he
    have hx := congrArg (fun x ↦ x.val.val) he
    have hK : K = K' := by
      have hg : K.graph = K'.graph := by
        rw [← halfEdgeMultiGraph_orderedPresentation K.graph p,
          ← halfEdgeMultiGraph_orderedPresentation K'.graph p']
        exact congrArg halfEdgeMultiGraph hx
      cases K
      cases K'
      cases hg
      rfl
    cases hK
    have hp : p = p' := by
      funext e
      apply Subtype.ext
      apply Prod.ext
      · exact congrFun hx (e,false)
      · exact congrFun hx (e,true)
    cases hp
    rfl
  · intro x
    let K : LabelledConnectedCubicKernel ell :=
      ⟨halfEdgeMultiGraph x.val.val,fun v ↦ by
        rw [halfEdgeMultiGraph_degree]
        exact x.val.property v,x.property⟩
    let p : OrderedMultiGraphPresentation K.graph :=
      fun e ↦ ⟨(x.val.val (e,false),x.val.val (e,true)),rfl⟩
    refine ⟨⟨K,p⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rcases i with ⟨e,b⟩
    cases b <;> rfl

def connectedCubicOrderedEquivHalfEdges (ell : ℕ) :
    ConnectedCubicOrderedPresentation ell ≃
      ConnectedCubicHalfEdgeTable (Fin (2 * ell)) (Fin (3 * ell)) :=
  Equiv.ofBijective _ (connectedCubicOrderedToHalfEdges_bijective ell)

theorem sum_labelledCubicKernelInverseMultiplicityReal_eq_connectedHalfEdgeCard
    (ell : ℕ) :
    letI := labelledConnectedCubicKernelFintype ell
    (∑ K : LabelledConnectedCubicKernel ell,
      labelledCubicKernelInverseMultiplicityReal K) =
      (Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * ell)) (Fin (3 * ell))) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  letI := connectedCubicOrderedPresentationFintype ell
  rw [sum_labelledCubicKernelInverseMultiplicityReal_eq_orderedCard,
    ← Nat.card_eq_fintype_card,Nat.card_congr (connectedCubicOrderedEquivHalfEdges ell)]

theorem positiveSurplusWrightConstantReal_eq_connectedHalfEdgeCard (ell : ℕ) :
    positiveSurplusWrightConstantReal ell =
      (Real.sqrt (2 * Real.pi) / Real.Gamma (3 * (ell : ℝ) / 2)) *
      (Real.sqrt 2 ^ (3 * ell))⁻¹ *
      ((Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * ell)) (Fin (3 * ell))) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell))) := by
  unfold positiveSurplusWrightConstantReal positiveSurplusCubicEGFConstantReal
  rw [sum_labelledCubicKernelInverseMultiplicityReal_eq_connectedHalfEdgeCard]
  ring

end PerronWright.GraphCore
