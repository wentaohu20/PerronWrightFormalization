import PerronWright.Enumeration.CubicKernelPathGeneratingSeries
import PerronWright.Analysis.AnalyticFiniteAmplitude

/-!
# Finite forbidden-length corrections for a cubic kernel

The unrestricted product of marked-path resolvents sums over every assignment
of a nonnegative internal length to every labelled kernel edge.  The literal
simple-graph reconstruction keeps only the admissible assignments.  This file
isolates the finite difference exactly.

There are only two kinds of local failure:

* a loop has length zero or one;
* two distinct kernel edges with the same unordered endpoints both have
  length zero.

Both failures freeze at least one edge at length at most one.  Hence every
forbidden cylinder contains at most `3 * ell - 1` genuinely summed path
factors.  The last elementary lemma records the corresponding extra-`X`
gain once its remaining finite analytic amplitude has been assembled.  The
actual analytic cylinder assembly is intentionally left to the following
module; no new analytic hypothesis or asymptotic assertion is introduced
here.
-/

open PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

/-! ## Concrete finite witnesses -/

/-- A loop edge together with one of its two forbidden internal lengths. -/
structure CubicKernelShortLoopWitness
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) where
  edge : Fin (3 * ell)
  isLoop : (H.endpoints edge).IsDiag
  length : Fin 2

/-- Two different edge labels with the same unordered endpoints.  If both
receive length zero, the reconstructed graph would contain parallel edges. -/
structure CubicKernelRepeatedZeroWitness
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) where
  first : Fin (3 * ell)
  second : Fin (3 * ell)
  ne : first ≠ second
  endpoints_eq : H.endpoints first = H.endpoints second

/-- The finite type of all local witnesses to failure of cubic admissibility. -/
abbrev CubicKernelForbiddenLengthWitness
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :=
  CubicKernelShortLoopWitness H ⊕ CubicKernelRepeatedZeroWitness H

/-- A concrete forbidden witness occurs in a length assignment. -/
def CubicKernelForbiddenLengthWitness.Occurs
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H)
    (l : Fin (3 * ell) →₀ ℕ) : Prop :=
  match w with
  | Sum.inl w => l w.edge = w.length.val
  | Sum.inr w => l w.first = 0 ∧ l w.second = 0

/-- Failure of the two admissibility clauses is equivalent to occurrence of
one of the two explicit finite witness types. -/
theorem not_cubicKernelLengthAssignment_admissible_iff
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (l : Fin (3 * ell) →₀ ℕ) :
    ¬ CubicKernelLengthAssignment.IsAdmissible H l ↔
      ∃ w : CubicKernelForbiddenLengthWitness H, w.Occurs l := by
  classical
  constructor
  · intro h
    rw [CubicKernelLengthAssignment.IsAdmissible, not_and_or] at h
    rcases h with hloop | hparallel
    · push Not at hloop
      obtain ⟨e, heLoop, heShort⟩ := hloop
      let n : Fin 2 := ⟨l e, heShort⟩
      exact ⟨Sum.inl ⟨e, heLoop, n⟩, rfl⟩
    · obtain ⟨e, f, hef, hne⟩ :=
        Function.not_injective_iff.mp hparallel
      let w : CubicKernelRepeatedZeroWitness H :=
        { first := e.1
          second := f.1
          ne := by
            intro hval
            apply hne
            exact Subtype.ext hval
          endpoints_eq := hef }
      exact ⟨Sum.inr w, ⟨e.2, f.2⟩⟩
  · rintro ⟨w, hw⟩ hadm
    rcases w with w | w
    · have hge := hadm.1 w.edge w.isLoop
      have heq : l w.edge = w.length.val := hw
      rw [heq] at hge
      omega
    · let e : {a : Fin (3 * ell) // l a = 0} := ⟨w.first, hw.1⟩
      let f : {a : Fin (3 * ell) // l a = 0} := ⟨w.second, hw.2⟩
      have heq : e = f := hadm.2 (by simpa only [e, f] using w.endpoints_eq)
      exact w.ne (congrArg Subtype.val heq)

/-- Every forbidden local witness freezes at least one edge at length zero or
one.  This is the exact combinatorial source of the loss of one pole factor. -/
theorem CubicKernelForbiddenLengthWitness.exists_edge_length_le_one
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H)
    (l : Fin (3 * ell) →₀ ℕ) (hw : w.Occurs l) :
    ∃ e : Fin (3 * ell), l e ≤ 1 := by
  rcases w with w | w
  · refine ⟨w.edge, ?_⟩
    rw [hw]
    omega
  · exact ⟨w.first, by simp only [hw.1, Nat.zero_le]⟩

/-- The forbidden part of the finite length antidiagonal. -/
abbrev CubicKernelForbiddenLengthAntidiagonal
    (d ell : ℕ) (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :=
  {l : (Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)) //
    ¬ CubicKernelLengthAssignment.IsAdmissible H l.1}

/-- Every member of the forbidden antidiagonal has a frozen edge of length at
most one. -/
theorem CubicKernelForbiddenLengthAntidiagonal.exists_edge_length_le_one
    {d ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (A : CubicKernelForbiddenLengthAntidiagonal d ell H) :
    ∃ e : Fin (3 * ell), A.1.1 e ≤ 1 := by
  obtain ⟨w, hw⟩ :=
    (not_cubicKernelLengthAssignment_admissible_iff H A.1.1).mp A.2
  exact w.exists_edge_length_le_one A.1.1 hw

/-! ## Exact admissible/forbidden splitting of the coefficient -/

/-- The explicitly forbidden part of the unrestricted fixed-kernel path
coefficient. -/
def cubicKernelForbiddenPathCoefficient
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (d : ℕ) : ℂ :=
  ∑ A : CubicKernelForbiddenLengthAntidiagonal d ell K.graph,
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (A.1.1 e)

/-- The unrestricted product coefficient is exactly the sum of its
admissible profile part and its finite forbidden correction. -/
theorem cubicKernelPathProductSeries_coeff_eq_admissible_add_forbidden
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (d : ℕ) :
    PowerSeries.coeff d (cubicKernelPathProductSeries M tau K x) =
      cubicKernelAdmissiblePathCoefficient M tau K x d +
        cubicKernelForbiddenPathCoefficient M tau K x d := by
  classical
  let A := (Finset.univ.finsuppAntidiag d :
    Finset (Fin (3 * ell) →₀ ℕ))
  let p : A → Prop := fun l ↦
    CubicKernelLengthAssignment.IsAdmissible K.graph l.1
  let f : A → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l.1 e)
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  have hattach :
      (∑ l ∈ (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)) =
        ∑ l : A, f l := by
    change (∑ l ∈ A,
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)) = _
    rw [← Finset.sum_attach]
    rfl
  rw [cubicKernelPathProductSeries_coeff,
    hattach, cubicKernelAdmissiblePathCoefficient_eq_antidiagonal]
  unfold cubicKernelForbiddenPathCoefficient
  simpa only [A, p, f] using hsplit.symm

/-! ## The abstract one-edge gain -/

/-- Once a forbidden cylinder has been assembled as an analytic amplitude
with at most `3 * ell - 1` pole factors, normalization by the cubic pole order
leaves an explicit factor `X`.  This is a direct specialization of the
generic finite-amplitude lemma, not an additional analytic interface. -/
theorem forbidden_cubicCylinder_normalized_eq_X_mul
    {ell : ℕ} (hell : 0 < ell)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧
      ∀ X,
        X ^ (3 * ell - (3 * ell - 1)) * F X = X * R X := by
  apply PerronWright.AnalyticFiniteAmplitude.noncubic_normalizedAmplitude_eq_X_mul
  · omega
  · exact hF

end PerronWright.GraphCore
