import PerronWright.Enumeration.CubicCompensationCoefficient
import PerronWright.Enumeration.PerronWrightFormulaMainTerm
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# First literal connected cubic compensation coefficient

Odd degree excludes a component consisting of one loop-only vertex.  Hence
every two-vertex cubic endpoint table is genuinely connected, and its exact
compensation coefficient follows from the previously proved half-edge count.
-/

noncomputable section

open scoped BigOperators Classical
set_option linter.style.haveILetI false
set_option maxHeartbeats 1500000

namespace PerronWright.GraphCore

theorem two_vertex_cubic_has_cross_edge
    (H : PerronWright.FiniteMultiGraph 2 3) (h : ∀ v, H.degree v = 3) :
    ∃ i, H.endpoints i = s((0 : Fin 2), (1 : Fin 2)) := by
  by_contra! hn
  have hi (q : Sym2 (Fin 2)) (hq : q ≠ s((0 : Fin 2), (1 : Fin 2))) :
      PerronWright.FiniteMultiGraph.incidence q 0 % 2 = 0 := by
    induction q using Sym2.inductionOn with
    | _ a b =>
      fin_cases a <;> fin_cases b <;>
        simp_all [PerronWright.FiniteMultiGraph.incidence_mk]
  have hh : H.degree 0 % 2 = 0 := by
    unfold PerronWright.FiniteMultiGraph.degree
    rw [Finset.sum_nat_mod]
    simp_rw [hi _ (hn _)]
    simp
  rw [h 0] at hh
  norm_num at hh

theorem two_vertex_cubic_connected
    (H : PerronWright.FiniteMultiGraph 2 3) (h : ∀ v, H.degree v = 3) :
    (finiteMultiGraphSupportGraph H).Connected := by
  obtain ⟨i,hi⟩ := two_vertex_cubic_has_cross_edge H h
  have hadj : (finiteMultiGraphSupportGraph H).Adj (0 : Fin 2) 1 := by
    rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨i,hi⟩, by decide⟩
  constructor
  intro v w
  fin_cases v <;> fin_cases w
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- Forgetting connectedness loses no two-vertex cubic table. -/
def connectedCubicKernelOneEquivAll :
    LabelledConnectedCubicKernel 1 ≃ LabelledCubicKernel 1 where
  toFun K := ⟨K.graph,K.cubic⟩
  invFun K := ⟨K.val,K.property,two_vertex_cubic_connected K.val K.property⟩
  left_inv K := by cases K; rfl
  right_inv K := by cases K; rfl

theorem connectedCubicOrderedPresentation_one_card :
    letI := connectedCubicOrderedPresentationFintype 1
    Fintype.card (ConnectedCubicOrderedPresentation 1) = 20 := by
  letI := labelledConnectedCubicKernelFintype 1
  letI := connectedCubicOrderedPresentationFintype 1
  have he : ConnectedCubicOrderedPresentation 1 ≃ CubicOrderedPresentation 1 :=
    Equiv.sigmaCongr connectedCubicKernelOneEquivAll (fun _ ↦ Equiv.refl _)
  rw [Fintype.card_congr he]
  have h := card_cubicOrderedPresentation_mul_sixPower 1
  rw [← Nat.card_eq_fintype_card] at h ⊢
  norm_num only [Nat.mul_one, Nat.factorial, Nat.reduceMul, Nat.reducePow] at h
  omega

/-- The first connected compensation coefficient is the actual finite
inverse-global-multiplicity sum, not an independently prescribed constant. -/
theorem sum_labelledCubicKernelInverseMultiplicityReal_one :
    letI := labelledConnectedCubicKernelFintype 1
    (∑ K : LabelledConnectedCubicKernel 1,
      labelledCubicKernelInverseMultiplicityReal K) = 5 / 24 := by
  rw [sum_labelledCubicKernelInverseMultiplicityReal_eq_orderedCard,
    connectedCubicOrderedPresentation_one_card]
  norm_num

theorem positiveSurplusCubicEGFConstantReal_one_exact :
    positiveSurplusCubicEGFConstantReal 1 = (Real.sqrt 2 ^ 3)⁻¹ * (5 / 24) := by
  unfold positiveSurplusCubicEGFConstantReal
  rw [sum_labelledCubicKernelInverseMultiplicityReal_one]

theorem positiveSurplusWrightConstantReal_one_exact :
    positiveSurplusWrightConstantReal 1 =
      (Real.sqrt (2 * Real.pi) / Real.Gamma (3 / 2)) *
      (Real.sqrt 2 ^ 3)⁻¹ * (5 / 24) := by
  unfold positiveSurplusWrightConstantReal
  rw [positiveSurplusCubicEGFConstantReal_one_exact]
  norm_num
  ring

theorem allCubicCompensation_zero : allCubicCompensation 0 = 1 := by
  rw [allCubicCompensation_eq_factorials]
  norm_num

theorem allCubicCompensation_one : allCubicCompensation 1 = 5 / 24 := by
  rw [allCubicCompensation_eq_factorials]
  norm_num

/-- Linear coefficient recurrence for all cubic configurations, proved from
their actual finite presentation count.  Turning this into the nonlinear
connected recurrence still requires the component decomposition. -/
theorem allCubicCompensation_recurrence (ell : ℕ) :
    24 * ((ell : ℝ) + 1) * allCubicCompensation (ell + 1) =
      (6 * (ell : ℝ) + 1) * (6 * (ell : ℝ) + 5) * allCubicCompensation ell := by
  have h6 : ((6 * (ell + 1)).factorial : ℝ) =
      (6 * (ell : ℝ) + 6) * (6 * (ell : ℝ) + 5) *
      (6 * (ell : ℝ) + 4) * (6 * (ell : ℝ) + 3) *
      (6 * (ell : ℝ) + 2) * (6 * (ell : ℝ) + 1) *
      ((6 * ell).factorial : ℝ) := by
    norm_num [Nat.mul_add, Nat.factorial_succ, Nat.add_assoc]
    ring
  have h2 : ((2 * (ell + 1)).factorial : ℝ) =
      (2 * (ell : ℝ) + 2) * (2 * (ell : ℝ) + 1) *
      ((2 * ell).factorial : ℝ) := by
    norm_num [Nat.mul_add, Nat.factorial_succ, Nat.add_assoc]
    ring
  have h3 : ((3 * (ell + 1)).factorial : ℝ) =
      (3 * (ell : ℝ) + 3) * (3 * (ell : ℝ) + 2) *
      (3 * (ell : ℝ) + 1) * ((3 * ell).factorial : ℝ) := by
    norm_num [Nat.mul_add, Nat.factorial_succ, Nat.add_assoc]
    ring
  have hp2 : (2 : ℝ) ^ (3 * (ell + 1)) = 2 ^ (3 * ell) * 8 := by
    rw [Nat.mul_add, pow_add]
    norm_num
  have hp6 : (6 : ℝ) ^ (2 * (ell + 1)) = 6 ^ (2 * ell) * 36 := by
    rw [Nat.mul_add, pow_add]
    norm_num
  rw [allCubicCompensation_eq_factorials, allCubicCompensation_eq_factorials,
    h6,h2,h3,hp2,hp6]
  have hf2 : ((2 * ell).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : ((3 * ell).factorial : ℝ) ≠ 0 := by positivity
  have ht2 : (2 : ℝ) ^ (3 * ell) ≠ 0 := by positivity
  have ht6 : (6 : ℝ) ^ (2 * ell) ≠ 0 := by positivity
  have hl : (0 : ℝ) ≤ ell := Nat.cast_nonneg ell
  have h21 : 2 * (ell : ℝ) + 1 ≠ 0 := by positivity
  have h22 : 2 * (ell : ℝ) + 2 ≠ 0 := by positivity
  have h31 : 3 * (ell : ℝ) + 1 ≠ 0 := by positivity
  have h32 : 3 * (ell : ℝ) + 2 ≠ 0 := by positivity
  have h33 : 3 * (ell : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hf2,hf3,ht2,ht6,h21,h22,h31,h32,h33]
  ring

theorem positiveSurplusWrightConstantReal_one :
    positiveSurplusWrightConstantReal 1 = 5 / 24 := by
  rw [positiveSurplusWrightConstantReal_one_exact]
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    calc
      Real.Gamma (3 / 2) = Real.Gamma ((1 / 2 : ℝ) + 1) := by norm_num
      _ = (1 / 2 : ℝ) * Real.Gamma (1 / 2) := Real.Gamma_add_one (by norm_num)
      _ = _ := by rw [Real.Gamma_one_half_eq]; ring
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have htwo : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  rw [hg, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num)]
  rw [hp]
  field_simp [hpi,htwo]

/-- The unchanged paper main-term constant at surplus two. -/
theorem wrightConstant_two : PerronWrightFormulaMainTerm.wrightConstant 2 = 5 / 24 := by
  exact positiveSurplusWrightConstantReal_one

end PerronWright.GraphCore
