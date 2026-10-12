import PerronWright.Enumeration.NoncubicVariableKernelRegroup
import PerronWright.Enumeration.CubicKernelSubdivision
import Mathlib.Data.Fintype.Perm

/-!
# Variable-valence bounded-kernel subdivision data

This is the parameter-free subdivision datum needed for the noncubic
positive-surplus remainder.  Unlike `CubicKernelSubdivision`, the numbers of
branch vertices and suppressed edges are read from a bounded kernel shape;
they are not fixed to `2 * ell` and `3 * ell`.

The slot labelling count is nevertheless still exactly `k!`.  This is the
factor which cancels the labelled-EGF denominator before the remaining
finite kernel-coordinate multiplicity is handled.
-/

open PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

/-- Regard a bounded endpoint table as an edge-labelled multigraph. -/
def boundedKernelFiniteMultiGraph {ell : ℕ}
    (D : BoundedKernelShape ell) :
    PerronWright.FiniteMultiGraph D.1.val D.2.1.val :=
  ⟨D.2.2⟩

/-- A bounded edge-labelled kernel table with minimum degree at least three
and exact excess `ell`.  Connectivity is deliberately not stored here:
reconstruction is defined for raw kernels, and the converse connectivity
theorem later recovers connectivity from an actual connected core. -/
structure LabelledBoundedKernel (ell : ℕ) where
  shape : BoundedKernelShape ell
  minDegree : ∀ v, 3 ≤ (boundedKernelFiniteMultiGraph shape).degree v
  excess : shape.2.1.val = shape.1.val + ell

/-- A raw bounded kernel whose non-loop support is connected. -/
structure LabelledConnectedBoundedKernel (ell : ℕ) extends
    LabelledBoundedKernel ell where
  connected :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph toLabelledBoundedKernel.shape)).Connected

/-- The genuinely noncubic members of the preceding finite kernel type. -/
abbrev LabelledConnectedNoncubicKernel (ell : ℕ) :=
  {K : LabelledConnectedBoundedKernel ell //
    K.toLabelledBoundedKernel.shape.2.1.val < 3 * ell}

/-- A raw bounded kernel is determined by its endpoint table. -/
theorem LabelledBoundedKernel.ext
    {ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K.shape = L.shape) : K = L := by
  cases K
  cases L
  cases h
  rfl

noncomputable instance labelledBoundedKernelFintype (ell : ℕ) :
    Fintype (LabelledBoundedKernel ell) := by
  apply Fintype.ofInjective
    (fun K : LabelledBoundedKernel ell ↦ K.shape)
  intro K L h
  exact LabelledBoundedKernel.ext h

/-- A connected variable-valence kernel is determined by its bounded table. -/
theorem LabelledConnectedBoundedKernel.ext
    {ell : ℕ} {K L : LabelledConnectedBoundedKernel ell}
    (h : K.toLabelledBoundedKernel.shape =
      L.toLabelledBoundedKernel.shape) : K = L := by
  cases K with
  | mk K hK =>
      cases L with
      | mk L hL =>
          have hKL : K = L := LabelledBoundedKernel.ext h
          cases hKL
          rfl

noncomputable instance labelledConnectedBoundedKernelFintype (ell : ℕ) :
    Fintype (LabelledConnectedBoundedKernel ell) := by
  apply Fintype.ofInjective
    (fun K : LabelledConnectedBoundedKernel ell ↦
      K.toLabelledBoundedKernel.shape)
  intro K L h
  exact LabelledConnectedBoundedKernel.ext h

noncomputable instance labelledConnectedNoncubicKernelFintype (ell : ℕ) :
    Fintype (LabelledConnectedNoncubicKernel ell) := by
  unfold LabelledConnectedNoncubicKernel
  infer_instance

/-- Edge labels whose endpoint pair is diagonal. -/
abbrev BoundedKernelLoopEdge {ell : ℕ}
    (K : LabelledBoundedKernel ell) :=
  {e : Fin K.shape.2.1.val // (K.shape.2.2 e).IsDiag}

/-- An admissible internal-length assignment for a variable-valence bounded
kernel.  The two local restrictions are exactly those forced by a simple
subdivision graph. -/
structure BoundedKernelLengthProfile
    (k : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) where
  length : Fin K.shape.2.1.val → Fin (k + 1)
  totalLength :
    K.shape.1.val + ∑ e, (length e).val = k
  loopLength :
    ∀ e, (K.shape.2.2 e).IsDiag → 2 ≤ (length e).val
  directEndpointsInjective :
    Function.Injective
      (fun e : {e : Fin K.shape.2.1.val // (length e).val = 0} ↦
        K.shape.2.2 e.1)

/-- Branch slots followed by the ordered internal slots on every suppressed
edge. -/
def BoundedKernelSubdivisionSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) :=
  Fin K.shape.1.val ⊕
    Σ e : Fin K.shape.2.1.val, Fin (L.length e).val

noncomputable instance boundedKernelSubdivisionSlotFintype
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) :
    Fintype (BoundedKernelSubdivisionSlot L) := by
  unfold BoundedKernelSubdivisionSlot
  infer_instance

/-- One labelled subdivision of a fixed variable-valence kernel. -/
structure BoundedKernelSubdivisionDatum
    (k : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) where
  profile : BoundedKernelLengthProfile k K
  labels : BoundedKernelSubdivisionSlot profile ≃ Fin k

/-- Forgetting the labels identifies a datum with a length profile and one
equivalence from its subdivision slots to the original labels. -/
def boundedKernelSubdivisionDatumEquivProfileLabels
    {k ell : ℕ} (K : LabelledBoundedKernel ell) :
    BoundedKernelSubdivisionDatum k K ≃
      Σ L : BoundedKernelLengthProfile k K,
        BoundedKernelSubdivisionSlot L ≃ Fin k where
  toFun D := ⟨D.profile, D.labels⟩
  invFun Q := ⟨Q.1, Q.2⟩
  left_inv D := by cases D; rfl
  right_inv Q := by cases Q; rfl

/-- A length profile is determined by its finite length table. -/
@[instance_reducible] noncomputable def boundedKernelLengthProfileFintype
    (k : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelLengthProfile k K) := by
  apply Fintype.ofInjective
    (fun L : BoundedKernelLengthProfile k K ↦ L.length)
  intro L L' h
  cases L
  cases L'
  cases h
  rfl

@[instance_reducible] noncomputable def boundedKernelSubdivisionDatumFintype
    (k : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelSubdivisionDatum k K) := by
  letI : Fintype (BoundedKernelLengthProfile k K) :=
    boundedKernelLengthProfileFintype k K
  exact Fintype.ofEquiv
    (Σ L : BoundedKernelLengthProfile k K,
      BoundedKernelSubdivisionSlot L ≃ Fin k)
    (boundedKernelSubdivisionDatumEquivProfileLabels K).symm

/-- The subdivision slots have exactly the prescribed number of original
vertices. -/
theorem boundedKernelSubdivisionSlot_card
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) :
    Fintype.card (BoundedKernelSubdivisionSlot L) = k := by
  change Fintype.card
      (Fin K.shape.1.val ⊕
        Σ e : Fin K.shape.2.1.val, Fin (L.length e).val) = k
  calc
    Fintype.card
        (Fin K.shape.1.val ⊕
          Σ e : Fin K.shape.2.1.val, Fin (L.length e).val) =
      Fintype.card (Fin K.shape.1.val) +
        Fintype.card
          (Σ e : Fin K.shape.2.1.val, Fin (L.length e).val) :=
      Fintype.card_sum
    _ = K.shape.1.val +
        ∑ e : Fin K.shape.2.1.val, (L.length e).val := by
      simp only [Fintype.card_fin, Fintype.card_sigma]
    _ = k := L.totalLength

/-- Consequently a fixed length profile has exactly `k!` slot labellings. -/
theorem boundedKernelSubdivisionLabelEquiv_card
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) :
    Fintype.card (BoundedKernelSubdivisionSlot L ≃ Fin k) =
      k.factorial := by
  let e : BoundedKernelSubdivisionSlot L ≃ Fin k :=
    Fintype.equivFinOfCardEq (boundedKernelSubdivisionSlot_card L)
  calc
    Fintype.card (BoundedKernelSubdivisionSlot L ≃ Fin k) =
        (Fintype.card (BoundedKernelSubdivisionSlot L)).factorial :=
      Fintype.card_equiv e
    _ = k.factorial := by rw [boundedKernelSubdivisionSlot_card L]

/-- Summing a quantity which depends only on the length profile over all
labelled subdivision data contributes exactly `k!`. -/
theorem sum_boundedKernelSubdivisionDatum_profile
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (F : BoundedKernelLengthProfile k K → R) :
    letI := boundedKernelLengthProfileFintype k K
    letI := boundedKernelSubdivisionDatumFintype k K
    (∑ D : BoundedKernelSubdivisionDatum k K, F D.profile) =
      k.factorial •
        ∑ L : BoundedKernelLengthProfile k K, F L := by
  let _ : Fintype (BoundedKernelLengthProfile k K) :=
    boundedKernelLengthProfileFintype k K
  let _ : Fintype (BoundedKernelSubdivisionDatum k K) :=
    boundedKernelSubdivisionDatumFintype k K
  let e : BoundedKernelSubdivisionDatum k K ≃
      Σ L : BoundedKernelLengthProfile k K,
        BoundedKernelSubdivisionSlot L ≃ Fin k :=
    boundedKernelSubdivisionDatumEquivProfileLabels (k := k) K
  calc
    (∑ D : BoundedKernelSubdivisionDatum k K, F D.profile) =
        ∑ Q : Σ L : BoundedKernelLengthProfile k K,
            BoundedKernelSubdivisionSlot L ≃ Fin k,
          F Q.1 := by
      exact Fintype.sum_equiv e
        (fun D : BoundedKernelSubdivisionDatum k K ↦ F D.profile)
        (fun Q : Σ L : BoundedKernelLengthProfile k K,
          BoundedKernelSubdivisionSlot L ≃ Fin k ↦ F Q.1)
        (by intro D; rfl)
    _ = ∑ L : BoundedKernelLengthProfile k K,
          ∑ _labels : BoundedKernelSubdivisionSlot L ≃ Fin k,
            F L := by
      rw [Fintype.sum_sigma]
    _ = ∑ L : BoundedKernelLengthProfile k K,
          k.factorial • F L := by
      apply Fintype.sum_congr
      intro L
      rw [← boundedKernelSubdivisionLabelEquiv_card L]
      simp
    _ = k.factorial •
          ∑ L : BoundedKernelLengthProfile k K, F L := by
      simp only [Finset.smul_sum]

/-- The remaining global coordinate multiplicity suggested by branch- and
edge-label permutations and independent loop reversals.  Its exact fibre
interpretation is proved only after reconstruction coordinates are
recovered. -/
def LabelledBoundedKernel.coordinateMultiplicity
    {ell : ℕ} (K : LabelledBoundedKernel ell) : ℕ :=
  K.shape.1.val.factorial * K.shape.2.1.val.factorial *
    2 ^ Fintype.card (BoundedKernelLoopEdge K)

theorem LabelledBoundedKernel.coordinateMultiplicity_pos
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    0 < K.coordinateMultiplicity := by
  unfold LabelledBoundedKernel.coordinateMultiplicity
  positivity

end PerronWright.GraphCore
