import PerronWright.Enumeration.VariableKernelSubdivisionData
import Mathlib.Data.Fintype.Perm

/-!
# Exact coordinate and slot-labelling multiplicities for bounded kernels

This module isolates the two finite cancellations needed by the eventual
variable-valence EGF regrouping:

* a fixed length profile has exactly `k!` original-label assignments; and
* branch coordinates, edge coordinates, and loop orientations have exactly
  `nv! * ne! * 2^(#loops)` choices.

The second statement counts coordinate codes.  Identifying those codes with
the full reconstruction fibre is a separate recovery theorem; no such
identification is smuggled into the cardinality calculation below.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical BigOperators

/-- Simultaneous permutations of the branch and kernel-edge coordinates of
one bounded endpoint table. -/
abbrev BoundedKernelCoordinatePerm {ell : ℕ}
    (K : LabelledBoundedKernel ell) :=
  Equiv.Perm (Fin K.shape.1.val) × Equiv.Perm (Fin K.shape.2.1.val)

/-- Coordinate permutations together with one independent Boolean
orientation choice for every loop edge. -/
abbrev BoundedKernelCoordinateCode {ell : ℕ}
    (K : LabelledBoundedKernel ell) :=
  BoundedKernelCoordinatePerm K × (BoundedKernelLoopEdge K → Bool)

noncomputable instance boundedKernelCoordinateCodeFintype
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelCoordinateCode K) := by
  unfold BoundedKernelCoordinateCode BoundedKernelCoordinatePerm
  infer_instance

/-- Exact factorial count of the two coordinate permutation families. -/
theorem boundedKernelCoordinatePerm_card
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype.card (BoundedKernelCoordinatePerm K) =
      K.shape.1.val.factorial * K.shape.2.1.val.factorial := by
  change Fintype.card
      (Equiv.Perm (Fin K.shape.1.val) ×
        Equiv.Perm (Fin K.shape.2.1.val)) = _
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]
  simp only [Fintype.card_fin]

/-- Exact global coordinate-code cardinality. -/
theorem boundedKernelCoordinateCode_card
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype.card (BoundedKernelCoordinateCode K) =
      K.coordinateMultiplicity := by
  unfold BoundedKernelCoordinateCode
    LabelledBoundedKernel.coordinateMultiplicity
  rw [Fintype.card_prod, boundedKernelCoordinatePerm_card,
    Fintype.card_fun]
  simp only [Fintype.card_bool]

/-- The inverse coordinate multiplicity cancels a constant sum over all
coordinate codes.  This is the exact finite algebraic cancellation later
used after a genuine fibre equivalence has been supplied. -/
theorem inverseCoordinateMultiplicity_mul_sum_codes
    {ell : ℕ} (K : LabelledBoundedKernel ell) (A : ℂ) :
    (K.coordinateMultiplicity : ℂ)⁻¹ *
        ∑ _c : BoundedKernelCoordinateCode K, A = A := by
  rw [Finset.sum_const, Finset.card_univ,
    boundedKernelCoordinateCode_card]
  simp only [nsmul_eq_mul]
  have hne : (K.coordinateMultiplicity : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt K.coordinateMultiplicity_pos)
  field_simp

/-- Dividing a fixed-kernel labelled-subdivision sum by `k!` removes exactly
the original-label equivalence and leaves the admissible length-profile
sum. -/
theorem inv_factorial_mul_sum_subdivisionData_profile
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (F : BoundedKernelLengthProfile k K → ℂ) :
    letI := boundedKernelLengthProfileFintype k K
    letI := boundedKernelSubdivisionDatumFintype k K
    ((k.factorial : ℂ)⁻¹ *
        ∑ D : BoundedKernelSubdivisionDatum k K, F D.profile) =
      ∑ L : BoundedKernelLengthProfile k K, F L := by
  let _ : Fintype (BoundedKernelLengthProfile k K) :=
    boundedKernelLengthProfileFintype k K
  let _ : Fintype (BoundedKernelSubdivisionDatum k K) :=
    boundedKernelSubdivisionDatumFintype k K
  rw [sum_boundedKernelSubdivisionDatum_profile]
  simp only [nsmul_eq_mul]
  have hne : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp

/-- Both finite cancellations can be performed independently.  The
right-hand side is the unlabelled admissible-profile sum for one fixed raw
kernel. -/
theorem inverseCoordinateAndFactorial_mul_doubleCodeSum
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (F : BoundedKernelLengthProfile k K → ℂ) :
    letI := boundedKernelLengthProfileFintype k K
    letI := boundedKernelSubdivisionDatumFintype k K
    (K.coordinateMultiplicity : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹ *
        ∑ _c : BoundedKernelCoordinateCode K,
          ∑ D : BoundedKernelSubdivisionDatum k K, F D.profile =
      ∑ L : BoundedKernelLengthProfile k K, F L := by
  let _ : Fintype (BoundedKernelLengthProfile k K) :=
    boundedKernelLengthProfileFintype k K
  let _ : Fintype (BoundedKernelSubdivisionDatum k K) :=
    boundedKernelSubdivisionDatumFintype k K
  rw [Finset.sum_const, Finset.card_univ,
    boundedKernelCoordinateCode_card]
  simp only [nsmul_eq_mul]
  have hcoord : (K.coordinateMultiplicity : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt K.coordinateMultiplicity_pos)
  rw [sum_boundedKernelSubdivisionDatum_profile]
  simp only [nsmul_eq_mul]
  have hfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos k).ne'
  field_simp

end PerronWright.GraphCore
