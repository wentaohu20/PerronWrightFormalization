import PerronWright.Enumeration.MarkedPathFactor
import PerronWright.Analysis.TreeRealComplexBridge

/-!
# Literal constant-mark paths as operator powers

This module isolates the exact interface between the finite-dimensional
marked path integral and the path operator.  It deliberately stops before any
spectral splitting or resolvent analysis.

For a real mark `mark`, one internal vertex carries the complete profile

`mark(y) * exp (-t * d(y))`.

Consequently a path with `n` internal vertices is the `(a,b)` matrix
coefficient of the `n`-th power of `t K M_profile`, applied to the terminal
column `t K(.,b)`.
-/

open MeasureTheory
open scoped Classical

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The complete real weight at one internal path vertex: the supplied
terminal mark times the genuine compact-BJR isolation factor. -/
def markedPathProfile (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) : C(S, ℝ) :=
  ⟨fun y ↦ mark y * Real.exp (-t * M.degreeFunction y), by fun_prop⟩

@[simp] theorem markedPathProfile_apply (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) (y : S) :
    markedPathProfile M t mark y =
      mark y * Real.exp (-t * M.degreeFunction y) :=
  rfl

/-- Pointwise multiplication by a complex profile. -/
def pathProfileMultiplier (profile : C(S, ℂ)) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  ((ContinuousLinearMap.mulLeftRight ℂ (C(S, ℂ))) profile) 1

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem pathProfileMultiplier_apply (profile f : C(S, ℂ)) :
    pathProfileMultiplier profile f = profile * f := by
  simp [pathProfileMultiplier, ContinuousLinearMap.mulLeftRight_apply]

/-- The oriented path action `t K M_profile`.  Its orientation agrees with
the literal recurrence that peels the internal vertex adjacent to the left
endpoint. -/
def markedPathOperator (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) : C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (t : ℂ) •
    (M.kernel.complexActionCLM M.mu).comp
      (pathProfileMultiplier
        (TreeRealComplexBridge.complexify (markedPathProfile M t mark)))

theorem markedPathOperator_apply (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) (f : C(S, ℂ)) (x : S) :
    markedPathOperator M t mark f x =
      ∫ y : S, ((t * M.kernel x y : ℝ) : ℂ) *
        ((markedPathProfile M t mark y : ℝ) : ℂ) * f y ∂M.mu := by
  rw [markedPathOperator, smul_apply,
    ContinuousLinearMap.comp_apply, pathProfileMultiplier_apply,
    ContinuousKernel.complexActionCLM_apply]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  rw [ContinuousKernel.complexAction_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousMap.mul_apply,
    TreeRealComplexBridge.complexify_apply]
  push_cast
  ring

/-- The terminal direct-edge column `t K(.,b)`. -/
def markedPathTerminalColumn (M : CompactBJRModel S) (t : ℝ) (b : S) :
    C(S, ℂ) :=
  (t : ℂ) • M.kernel.complexColumns b

@[simp] theorem markedPathTerminalColumn_apply
    (M : CompactBJRModel S) (t : ℝ) (b x : S) :
    markedPathTerminalColumn M t b x = ((t * M.kernel x b : ℝ) : ℂ) := by
  change (t : ℂ) * (M.kernel x b : ℂ) = ((t * M.kernel x b : ℝ) : ℂ)
  rw [Complex.ofReal_mul]

/-- The one-internal-vertex literal path integral, with all scalar factors
displayed. -/
theorem markedPathFactor_const_one (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) (a b : S) :
    markedPathFactor M t 1 (fun _ ↦ mark) a b =
      ∫ y : S, (t * M.kernel a y) *
        Real.exp (-t * M.degreeFunction y) * mark y *
        (t * M.kernel y b) ∂M.mu := by
  let F : C((Fin 1 → S), ℝ) :=
    ⟨fun x ↦ (∏ i : Fin 1, mark (x i)) *
      interiorPathObservable M t 0 a b x, by fun_prop⟩
  change (∫ x : Fin 1 → S, F x
      ∂Measure.pi (fun _ : Fin 1 ↦ M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous M 0 F]
  apply integral_congr_ae
  filter_upwards [] with y
  have hx (z : Fin 0 → S) :
      (Fin.insertNth (0 : Fin 1) y z : Fin 1 → S) = ![y] := by
    funext i
    fin_cases i
    simp
  simp_rw [hx]
  change (∫ z : Fin 0 → S,
      (∏ i : Fin 1, mark (![y] i)) *
        interiorPathObservable M t 0 a b ![y]
      ∂Measure.pi (fun _ : Fin 0 ↦ M.mu)) = _
  simp only [Fin.prod_univ_one]
  change (∫ z : Fin 0 → S,
      mark y * ((t * M.kernel a y) *
        M.graphWeightIntegrand t (SimpleGraph.pathGraph 1) ![y] *
        (t * M.kernel y b))
      ∂Measure.pi (fun _ : Fin 0 ↦ M.mu)) = _
  rw [graphWeightIntegrand_pathGraph_one]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Peeling the leftmost internal vertex from a literal constant-mark path.
The statement starts at two internal vertices; the one-vertex base case is
`markedPathFactor_const_one`. -/
theorem markedPathFactor_const_succ_succ (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) (m : ℕ) (a b : S) :
    markedPathFactor M t (m + 2) (fun _ ↦ mark) a b =
      ∫ y : S, (t * M.kernel a y) *
        Real.exp (-t * M.degreeFunction y) * mark y *
        markedPathFactor M t (m + 1) (fun _ ↦ mark) y b ∂M.mu := by
  let F : C((Fin (m + 2) → S), ℝ) :=
    ⟨fun x ↦ (∏ i : Fin (m + 2), mark (x i)) *
      interiorPathObservable M t (m + 1) a b x, by fun_prop⟩
  change (∫ x : Fin (m + 2) → S, F x
      ∂Measure.pi (fun _ : Fin (m + 2) ↦ M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous M (m + 1) F]
  apply integral_congr_ae
  filter_upwards [] with y
  have hpoint (z : Fin (m + 1) → S) :
      F (Fin.insertNth 0 y z) =
        ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y) * mark y) *
          ((∏ i : Fin (m + 1), mark (z i)) *
            interiorPathObservable M t m y b z) := by
    have hprod :
        (∏ i : Fin (m + 2),
            mark ((Fin.insertNth (0 : Fin (m + 2)) y z :
              Fin (m + 2) → S) i)) =
          mark y * ∏ i : Fin (m + 1), mark (z i) := by
      rw [Fin.prod_univ_succ]
      simp
    have hobs :
        interiorPathObservable M t (m + 1) a b
            (Fin.insertNth 0 y z) =
          ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
            interiorPathObservable M t m y b z := by
      change
        (t * M.kernel a
          ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S) 0)) *
          M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 2))
            (Fin.insertNth 0 y z) *
          (t * M.kernel
            ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S)
              (Fin.last (m + 1))) b) = _
      rw [pathGraph_integrand_first_split M t m y z]
      simp only [Fin.insertNth_apply_same, insertNth_zero_last]
      change _ =
        ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
          ((t * M.kernel y (z 0)) *
            M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 1)) z *
            (t * M.kernel (z (Fin.last m)) b))
      ring
    change
      (∏ i : Fin (m + 2),
          mark ((Fin.insertNth (0 : Fin (m + 2)) y z :
            Fin (m + 2) → S) i)) *
        interiorPathObservable M t (m + 1) a b
          (Fin.insertNth 0 y z) = _
    rw [hprod, hobs]
    ring
  calc
    (∫ z : Fin (m + 1) → S, F (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ M.mu)) =
      ∫ z : Fin (m + 1) → S,
        ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y) * mark y) *
          ((∏ i : Fin (m + 1), mark (z i)) *
            interiorPathObservable M t m y b z)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ M.mu) := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact hpoint z
    _ = ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y) * mark y) *
        markedPathFactor M t (m + 1) (fun _ ↦ mark) y b := by
          rw [integral_const_mul]
          rfl

/-- Uniform one-step recurrence, including the one-internal-vertex base
case.  This is the precise literal interface consumed by the operator-power
proof below. -/
theorem markedPathFactor_const_succ (M : CompactBJRModel S) (t : ℝ)
    (mark : C(S, ℝ)) (n : ℕ) (a b : S) :
    markedPathFactor M t (n + 1) (fun _ ↦ mark) a b =
      ∫ y : S, (t * M.kernel a y) *
        Real.exp (-t * M.degreeFunction y) * mark y *
        markedPathFactor M t n (fun _ ↦ mark) y b ∂M.mu := by
  cases n with
  | zero =>
      change markedPathFactor M t 1 (fun _ ↦ mark) a b =
        ∫ y : S, (t * M.kernel a y) *
          Real.exp (-t * M.degreeFunction y) * mark y *
          (t * M.kernel y b) ∂M.mu
      exact markedPathFactor_const_one M t mark a b
  | succ m =>
      change markedPathFactor M t (m + 2) (fun _ ↦ mark) a b =
        ∫ y : S, (t * M.kernel a y) *
          Real.exp (-t * M.degreeFunction y) * mark y *
          markedPathFactor M t (m + 1) (fun _ ↦ mark) y b ∂M.mu
      exact markedPathFactor_const_succ_succ M t mark m a b

/-- The exact operator-power formula for the literal constant-mark path.
No generating-function or resolvent identity is assumed. -/
theorem markedPathFactor_const_eq_operatorPower
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    (n : ℕ) (a b : S) :
    ((markedPathFactor M t n (fun _ ↦ mark) a b : ℝ) : ℂ) =
      (((markedPathOperator M t mark) ^ n)
        (markedPathTerminalColumn M t b)) a := by
  induction n generalizing a with
  | zero =>
      change ((t * M.kernel a b : ℝ) : ℂ) =
        (((markedPathOperator M t mark) ^ 0)
          (markedPathTerminalColumn M t b)) a
      rw [pow_zero, one_apply_eq_self, markedPathTerminalColumn_apply]
  | succ n ih =>
      rw [markedPathFactor_const_succ]
      rw [← integral_complex_ofReal]
      rw [show (((markedPathOperator M t mark) ^ (n + 1))
          (markedPathTerminalColumn M t b)) a =
          markedPathOperator M t mark
            (((markedPathOperator M t mark) ^ n)
              (markedPathTerminalColumn M t b)) a by
            rw [pow_succ', mul_apply_eq_comp]]
      rw [markedPathOperator_apply]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← ih y]
      simp only [markedPathProfile_apply]
      push_cast
      ring

end PerronWright.GraphCore
