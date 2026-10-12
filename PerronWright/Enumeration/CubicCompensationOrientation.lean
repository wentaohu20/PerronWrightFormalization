import PerronWright.Enumeration.PositiveSurplusCubicConstantPositivity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Integer oriented presentations behind cubic compensation

An unordered non-loop edge has two ordered endpoint presentations; a loop
has one.  The exact fibre calculation below removes the loop denominators
from the project's literal connected cubic compensation sum.  In particular,
the result concerns the existing constants, not a replacement sequence.
-/

noncomputable section

open scoped BigOperators Classical
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

/-- The genuine ordered-pair fibre of an unordered endpoint pair. -/
abbrev OrderedEndpointFiber {V : Type*} (q : Sym2 V) :=
  {p : V × V // s(p.1, p.2) = q}

theorem card_orderedEndpointFiber {V : Type*} [Fintype V]
    (q : Sym2 V) [hq : Fintype (OrderedEndpointFiber q)] :
    Fintype.card (OrderedEndpointFiber q) = if q.IsDiag then 1 else 2 := by
  revert hq
  induction q using Sym2.inductionOn with
  | _ a b =>
    intro hq
    letI := hq
    have hc : Fintype.card (OrderedEndpointFiber s(a,b)) =
        ({(a,b), (b,a)} : Finset (V × V)).card := by
      apply Fintype.card_of_subtype
      intro p
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simpa only [Prod.swap_prod_mk] using
        (show p = (a,b) ∨ p = (a,b).swap ↔ s(p.1,p.2) = s(a,b) from
          Sym2.mk_eq_mk_iff.symm)
    rw [hc]
    by_cases h : a = b
    · subst b
      simp
    · have hp : (a,b) ≠ (b,a) := by
        intro he
        exact h (congrArg Prod.fst he)
      simp [h, hp]

/-- Independently orient every labelled edge, retaining its actual endpoints. -/
abbrev OrderedMultiGraphPresentation {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e) :=
  ∀ i : Fin e, OrderedEndpointFiber (H.endpoints i)

/-- The actual loop-edge subtype, without a cubic restriction. -/
abbrev MultiGraphLoopEdge {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e) :=
  {i : Fin e // (H.endpoints i).IsDiag}

theorem card_orderedMultiGraphPresentation_mul_loopPower {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e) :
    Fintype.card (OrderedMultiGraphPresentation H) *
        2 ^ Fintype.card (MultiGraphLoopEdge H) = 2 ^ e := by
  have hl : (∏ i : Fin e, if (H.endpoints i).IsDiag then (2 : ℕ) else 1) =
      2 ^ Fintype.card (MultiGraphLoopEdge H) := by
    rw [Finset.prod_ite]
    simp [Fintype.card_subtype]
  rw [show Fintype.card (OrderedMultiGraphPresentation H) =
    ∏ i : Fin e, Fintype.card (OrderedEndpointFiber (H.endpoints i)) from
      Fintype.card_pi]
  simp_rw [card_orderedEndpointFiber]
  rw [← hl, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ _i : Fin e, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> rfl
    _ = _ := by simp

/-- All oriented presentations of actual labelled connected cubic kernels. -/
abbrev ConnectedCubicOrderedPresentation (ell : ℕ) :=
  Σ K : LabelledConnectedCubicKernel ell, OrderedMultiGraphPresentation K.graph

@[instance_reducible] noncomputable def connectedCubicOrderedPresentationFintype
    (ell : ℕ) : Fintype (ConnectedCubicOrderedPresentation ell) := by
  letI := labelledConnectedCubicKernelFintype ell
  infer_instance

theorem labelledCubicKernelInverseMultiplicityReal_eq_orderedCard
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    labelledCubicKernelInverseMultiplicityReal K =
      (Fintype.card (OrderedMultiGraphPresentation K.graph) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  have hc := card_orderedMultiGraphPresentation_mul_loopPower K.graph
  have hcr : (Fintype.card (OrderedMultiGraphPresentation K.graph) : ℝ) *
      (2 : ℝ) ^ Fintype.card (CubicKernelLoopEdge K.graph) = 2 ^ (3 * ell) := by
    exact_mod_cast hc
  have hf2 : ((2 * ell).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : ((3 * ell).factorial : ℝ) ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ Fintype.card (CubicKernelLoopEdge K.graph) ≠ 0 := by positivity
  have he : (2 : ℝ) ^ (3 * ell) ≠ 0 := by positivity
  unfold labelledCubicKernelInverseMultiplicityReal labelledCubicKernelGlobalMultiplicity
  push_cast
  field_simp
  nlinarith [hcr]

/-- Exact integer presentation formula for the already defined compensation
sum.  Loops and parallel edge labels are included without exceptions. -/
theorem sum_labelledCubicKernelInverseMultiplicityReal_eq_orderedCard (ell : ℕ) :
    letI := labelledConnectedCubicKernelFintype ell
    letI := connectedCubicOrderedPresentationFintype ell
    (∑ K : LabelledConnectedCubicKernel ell,
      labelledCubicKernelInverseMultiplicityReal K) =
      (Fintype.card (ConnectedCubicOrderedPresentation ell) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  letI := labelledConnectedCubicKernelFintype ell
  letI := connectedCubicOrderedPresentationFintype ell
  simp_rw [labelledCubicKernelInverseMultiplicityReal_eq_orderedCard]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.card_sigma, Nat.cast_sum]

theorem positiveSurplusCubicEGFConstantReal_eq_orderedCard (ell : ℕ) :
    letI := connectedCubicOrderedPresentationFintype ell
    positiveSurplusCubicEGFConstantReal ell =
      (Real.sqrt 2 ^ (3 * ell))⁻¹ *
      ((Fintype.card (ConnectedCubicOrderedPresentation ell) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell))) := by
  unfold positiveSurplusCubicEGFConstantReal
  rw [sum_labelledCubicKernelInverseMultiplicityReal_eq_orderedCard]

theorem positiveSurplusWrightConstantReal_eq_orderedCard (ell : ℕ) :
    letI := connectedCubicOrderedPresentationFintype ell
    positiveSurplusWrightConstantReal ell =
      (Real.sqrt (2 * Real.pi) / Real.Gamma (3 * (ell : ℝ) / 2)) *
      (Real.sqrt 2 ^ (3 * ell))⁻¹ *
      ((Fintype.card (ConnectedCubicOrderedPresentation ell) : ℝ) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell))) := by
  unfold positiveSurplusWrightConstantReal
  rw [positiveSurplusCubicEGFConstantReal_eq_orderedCard]
  ring

end PerronWright.GraphCore
