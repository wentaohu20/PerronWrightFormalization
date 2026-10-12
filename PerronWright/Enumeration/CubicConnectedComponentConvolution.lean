import PerronWright.Enumeration.CubicConnectedComponentShape
import PerronWright.Enumeration.CubicCompensationInitialCoefficient

/-!
# The genuine scalar pointing convolution for cubic compensation

The connected coefficient here is only a name for the existing finite
inverse-global-multiplicity sum.  The convolution is derived from the
actual root-component bijection and the counts of its label subsets.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

def connectedCubicCompensation (ell : ℕ) : ℝ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell, labelledCubicKernelInverseMultiplicityReal K

theorem connectedCubicCompensation_eq_halfEdgeCard (ell : ℕ) :
    connectedCubicCompensation ell =
      (Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * ell)) (Fin (3 * ell))) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) :=
  sum_labelledCubicKernelInverseMultiplicityReal_eq_connectedHalfEdgeCard ell

theorem allCubicCompensation_eq_halfEdgeCard (ell : ℕ) :
    allCubicCompensation ell =
      (Nat.card (UniformHalfEdgeAssignment (Fin (3 * ell) × Bool) (Fin (2 * ell)) 3) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  rw [allCubicCompensation_eq_orderedCard,← Nat.card_eq_fintype_card,
    Nat.card_congr (cubicOrderedPresentationEquivHalfEdges ell)]

theorem connectedCubicCompensation_zero : connectedCubicCompensation 0 = 0 := by
  rw [connectedCubicCompensation_eq_halfEdgeCard]
  haveI : IsEmpty (ConnectedCubicHalfEdgeTable (Fin (2 * 0)) (Fin (3 * 0))) :=
    ⟨fun x ↦ by obtain ⟨v⟩ := x.property.nonempty; exact Fin.elim0 v⟩
  simp [Nat.card_eq_fintype_card]

theorem connectedCubicCompensation_one : connectedCubicCompensation 1 = 5 / 24 :=
  sum_labelledCubicKernelInverseMultiplicityReal_one

private def compensationDenominator (ell : ℕ) : ℝ :=
  (2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)

private theorem compensationDenominator_ne_zero (ell : ℕ) :
    compensationDenominator ell ≠ 0 := by unfold compensationDenominator; positivity

theorem cubic_pointed_label_factor (ell j : ℕ) (hj : 0 < j) (hjl : j ≤ ell) :
    (2 * ell : ℝ) * ((2 * ell - 1).choose (2 * j - 1) : ℝ) *
        ((3 * ell).choose (3 * j) : ℝ) *
        ((2 * j).factorial * (3 * j).factorial * (2 : ℝ) ^ (3 * j)) *
        ((2 * (ell - j)).factorial * (3 * (ell - j)).factorial *
          (2 : ℝ) ^ (3 * (ell - j))) =
      (2 * j : ℝ) * ((2 * ell).factorial * (3 * ell).factorial *
        (2 : ℝ) ^ (3 * ell)) := by
  have hv : (2 * ell).choose (2 * j) * (2 * j).factorial *
      (2 * (ell - j)).factorial = (2 * ell).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * ell) (k := 2 * j) (by omega)
    rwa [show 2 * ell - 2 * j = 2 * (ell - j) by omega] at h
  have he : (3 * ell).choose (3 * j) * (3 * j).factorial *
      (3 * (ell - j)).factorial = (3 * ell).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 3 * ell) (k := 3 * j) (by omega)
    rwa [show 3 * ell - 3 * j = 3 * (ell - j) by omega] at h
  have hp : (2 * ell) * (2 * ell - 1).choose (2 * j - 1) =
      (2 * ell).choose (2 * j) * (2 * j) := by
    have h := Nat.add_one_mul_choose_eq (2 * ell - 1) (2 * j - 1)
    rwa [show 2 * ell - 1 + 1 = 2 * ell by omega,
      show 2 * j - 1 + 1 = 2 * j by omega] at h
  have hvr : ((2 * ell).choose (2 * j) : ℝ) * (2 * j).factorial *
      (2 * (ell - j)).factorial = (2 * ell).factorial := by exact_mod_cast hv
  have her : ((3 * ell).choose (3 * j) : ℝ) * (3 * j).factorial *
      (3 * (ell - j)).factorial = (3 * ell).factorial := by exact_mod_cast he
  have hpr : (2 * ell : ℝ) * ((2 * ell - 1).choose (2 * j - 1) : ℝ) =
      ((2 * ell).choose (2 * j) : ℝ) * (2 * j : ℝ) := by exact_mod_cast hp
  have hpow : (2 : ℝ) ^ (3 * j) * 2 ^ (3 * (ell - j)) = 2 ^ (3 * ell) := by
    rw [← pow_add,show 3 * j + 3 * (ell - j) = 3 * ell by omega]
  calc
    _ = ((2 * ell : ℝ) * ((2 * ell - 1).choose (2 * j - 1) : ℝ)) *
        (2 * j).factorial * (2 * (ell - j)).factorial *
        (((3 * ell).choose (3 * j) : ℝ) * (3 * j).factorial *
          (3 * (ell - j)).factorial) *
        ((2 : ℝ) ^ (3 * j) * 2 ^ (3 * (ell - j))) := by ring
    _ = ((2 * ell).choose (2 * j) : ℝ) * (2 * j : ℝ) *
        (2 * j).factorial * (2 * (ell - j)).factorial *
        (3 * ell).factorial * (2 : ℝ) ^ (3 * ell) := by rw [hpr,her,hpow]
    _ = (2 * j : ℝ) *
        (((2 * ell).choose (2 * j) : ℝ) * (2 * j).factorial *
          (2 * (ell - j)).factorial) *
        (3 * ell).factorial * (2 : ℝ) ^ (3 * ell) := by ring
    _ = _ := by rw [hvr]; ring

/-- The root-component pointing convolution for the actual connected
inverse-global-multiplicity sum, including the empty remainder. -/
theorem cubicCompensation_root_convolution (ell : ℕ) :
    (2 * ell : ℝ) * allCubicCompensation ell =
      ∑ j : CubicRootSize ell,
        (2 * j.val : ℝ) * connectedCubicCompensation j.val *
          allCubicCompensation (ell - j.val) := by
  by_cases hell : ell = 0
  · subst ell
    haveI : IsEmpty (CubicRootSize 0) := ⟨fun j ↦ by omega⟩
    simp
  let root : Fin (2 * ell) := ⟨0,by omega⟩
  rw [allCubicCompensation_eq_orderedCard,← Nat.card_eq_fintype_card,
    card_cubicOrderedPresentation_eq_scalarRootSum ell root,Nat.cast_sum,
    Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [connectedCubicCompensation_eq_halfEdgeCard,allCubicCompensation_eq_halfEdgeCard]
  push_cast
  change (2 * ell : ℝ) *
      ((((2 * ell - 1).choose (2 * j.val - 1) : ℝ) *
        ((3 * ell).choose (3 * j.val) : ℝ) * _ * _) / compensationDenominator ell) =
    (2 * j.val : ℝ) * (_ / compensationDenominator j.val) *
      (_ / compensationDenominator (ell - j.val))
  have hf := cubic_pointed_label_factor ell j.val j.property.1 j.property.2
  change (2 * ell : ℝ) * ((2 * ell - 1).choose (2 * j.val - 1) : ℝ) *
      ((3 * ell).choose (3 * j.val) : ℝ) * compensationDenominator j.val *
      compensationDenominator (ell - j.val) =
    (2 * j.val : ℝ) * compensationDenominator ell at hf
  have hm := congrArg (fun z : ℝ ↦ z *
      (Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * j.val)) (Fin (3 * j.val))) : ℝ) *
      (Nat.card (UniformHalfEdgeAssignment
        (Fin (3 * (ell - j.val)) × Bool) (Fin (2 * (ell - j.val))) 3) : ℝ)) hf
  field_simp [compensationDenominator_ne_zero]
  nlinarith only [hm]

theorem positiveSurplusWrightConstantReal_eq_connectedCompensation (ell : ℕ) :
    positiveSurplusWrightConstantReal ell =
      (Real.sqrt (2 * Real.pi) / Real.Gamma (3 * (ell : ℝ) / 2)) *
        (Real.sqrt 2 ^ (3 * ell))⁻¹ * connectedCubicCompensation ell := by
  unfold positiveSurplusWrightConstantReal positiveSurplusCubicEGFConstantReal
    connectedCubicCompensation
  ring

end PerronWright.GraphCore
