import PerronWright.Enumeration.CubicGlobalWeightedRegroup
import PerronWright.Enumeration.CubicKernelSubdivisionCount
import PerronWright.Enumeration.CubicReconstructionFieldWeight

/-!
# Regrouping cubic presentations by their length profiles

For one fixed edge-labelled cubic kernel, a subdivision datum consists of an
admissible length profile and a bijection from its `k` subdivision slots to
`Fin k`.  The latter fibre has cardinality `k!`.  This file uses that exact
cardinality to remove the original labels from every summand which depends
only on the length profile.

Combining the fixed-kernel identity with the already proved global
presentation multiplicity gives the finite positive-surplus factor

`k! / ((2 * ell)! * (3 * ell)!)`.

What remains is a sum over labelled connected cubic kernels, weighted by the
reciprocal of `2 ^ (# loop labels)`, and over admissible length profiles.  No
automorphism quotient or analytic interchange of an infinite sum is used.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical BigOperators

/-- Forgetting the label bijection identifies fixed-kernel subdivision data
with a dependent pair consisting of a length profile and one labelling of its
subdivision slots. -/
def cubicKernelSubdivisionDatumEquivProfileLabels
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)} :
    CubicKernelSubdivisionDatum k ell H ≃
      Σ L : CubicKernelLengthProfile k ell H,
        CubicKernelSubdivisionSlot L ≃ Fin k where
  toFun D := ⟨D.profile, D.labels⟩
  invFun Q := ⟨Q.1, Q.2⟩
  left_inv D := by cases D; rfl
  right_inv Q := by cases Q; rfl

/-- The finite structure on admissible length profiles, obtained by embedding
each profile into its finite length table. -/
@[instance_reducible] noncomputable def cubicKernelLengthProfileFintype
    (k ell : ℕ)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype (CubicKernelLengthProfile k ell H) := by
  apply Fintype.ofInjective
    (fun L : CubicKernelLengthProfile k ell H ↦ L.length)
  intro L L' h
  cases L with
  | mk length totalLength loopLength directEndpointsInjective =>
      cases L' with
      | mk length' totalLength' loopLength' directEndpointsInjective' =>
          cases h
          rfl

/-- The finite structure on fixed-kernel subdivision data, built from the
profile and label-bijection description above. -/
@[instance_reducible] noncomputable def cubicKernelSubdivisionDatumFintype
    (k ell : ℕ)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype (CubicKernelSubdivisionDatum k ell H) := by
  letI : Fintype (CubicKernelLengthProfile k ell H) :=
    cubicKernelLengthProfileFintype k ell H
  exact Fintype.ofEquiv
    (Σ L : CubicKernelLengthProfile k ell H,
      CubicKernelSubdivisionSlot L ≃ Fin k)
    cubicKernelSubdivisionDatumEquivProfileLabels.symm

/-- The finite structure on labelled connected cubic kernels, obtained by
embedding each kernel into its finite endpoint table. -/
@[instance_reducible] noncomputable def labelledConnectedCubicKernelFintype (ell : ℕ) :
    Fintype (LabelledConnectedCubicKernel ell) := by
  apply Fintype.ofInjective
    (fun K : LabelledConnectedCubicKernel ell ↦ K.graph)
  intro K K' h
  cases K with
  | mk graph cubic connected =>
      cases K' with
      | mk graph' cubic' connected' =>
          cases h
          rfl

/-- If a fixed-kernel summand sees only the admissible length profile, then
summing it over all original vertex labellings contributes exactly `k!`.
The proof uses the literal cardinality of the label-equivalence fibre. -/
theorem sum_cubicKernelSubdivisionDatum_profile
    {R : Type*} [AddCommMonoid R]
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (F : CubicKernelLengthProfile k ell K.graph → R) :
    letI := cubicKernelLengthProfileFintype k ell K.graph
    letI := cubicKernelSubdivisionDatumFintype k ell K.graph
    (∑ D : CubicKernelSubdivisionDatum k ell K.graph, F D.profile) =
      k.factorial •
        ∑ L : CubicKernelLengthProfile k ell K.graph, F L := by
  let _ : Fintype (CubicKernelLengthProfile k ell K.graph) :=
    cubicKernelLengthProfileFintype k ell K.graph
  let _ : Fintype (CubicKernelSubdivisionDatum k ell K.graph) :=
    cubicKernelSubdivisionDatumFintype k ell K.graph
  let e := cubicKernelSubdivisionDatumEquivProfileLabels
    (k := k) (ell := ell) (H := K.graph)
  calc
    (∑ D : CubicKernelSubdivisionDatum k ell K.graph, F D.profile) =
        ∑ Q : Σ L : CubicKernelLengthProfile k ell K.graph,
            CubicKernelSubdivisionSlot L ≃ Fin k,
          F Q.1 := by
      exact Fintype.sum_equiv e
        (fun D : CubicKernelSubdivisionDatum k ell K.graph ↦ F D.profile)
        (fun Q : Σ L : CubicKernelLengthProfile k ell K.graph,
          CubicKernelSubdivisionSlot L ≃ Fin k ↦ F Q.1)
        (by intro D; rfl)
    _ = ∑ L : CubicKernelLengthProfile k ell K.graph,
          ∑ _labels : CubicKernelSubdivisionSlot L ≃ Fin k, F L := by
      rw [Fintype.sum_sigma]
    _ = ∑ L : CubicKernelLengthProfile k ell K.graph,
          k.factorial • F L := by
      apply Fintype.sum_congr
      intro L
      rw [← cubicKernelSubdivisionLabelEquiv_card L]
      simp
    _ = k.factorial •
          ∑ L : CubicKernelLengthProfile k ell K.graph, F L := by
      simp only [Finset.smul_sum]

/-- The elementary scalar identity which separates the two coordinate
factorials from the independent loop-reversal factor. -/
theorem factorial_mul_globalMultiplicity_inv_eq_profileFactor
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    (k.factorial : 𝕜) *
        (((2 * ell).factorial * (3 * ell).factorial *
          2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : 𝕜)⁻¹ =
      (k.factorial : 𝕜) /
          (((2 * ell).factorial : 𝕜) *
            ((3 * ell).factorial : 𝕜)) *
        (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : 𝕜)⁻¹) := by
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact profile regrouping of the global inverse-multiplicity presentation
sum.  The left side ranges over the literal sigma type of all labelled
connected cubic kernels and all subdivision data over each kernel. -/
theorem sum_cubicKernelPresentations_invMultiplicity_profile
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ}
    (F : (K : LabelledConnectedCubicKernel ell) →
      CubicKernelLengthProfile k ell K.graph → 𝕜) :
    letI := labelledConnectedCubicKernelFintype ell
    letI : ∀ K : LabelledConnectedCubicKernel ell,
        Fintype (CubicKernelLengthProfile k ell K.graph) :=
      fun K ↦ cubicKernelLengthProfileFintype k ell K.graph
    letI : ∀ K : LabelledConnectedCubicKernel ell,
        Fintype (CubicKernelSubdivisionDatum k ell K.graph) :=
      fun K ↦ cubicKernelSubdivisionDatumFintype k ell K.graph
    (∑ P : CubicKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ * F P.1 P.2.profile) =
      (k.factorial : 𝕜) /
          (((2 * ell).factorial : 𝕜) *
            ((3 * ell).factorial : 𝕜)) *
        ∑ K : LabelledConnectedCubicKernel ell,
          (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : 𝕜)⁻¹ *
            ∑ L : CubicKernelLengthProfile k ell K.graph, F K L) := by
  let _ : Fintype (LabelledConnectedCubicKernel ell) :=
    labelledConnectedCubicKernelFintype ell
  let _ (K : LabelledConnectedCubicKernel ell) :
      Fintype (CubicKernelLengthProfile k ell K.graph) :=
    cubicKernelLengthProfileFintype k ell K.graph
  let _ (K : LabelledConnectedCubicKernel ell) :
      Fintype (CubicKernelSubdivisionDatum k ell K.graph) :=
    cubicKernelSubdivisionDatumFintype k ell K.graph
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Fintype.sum_congr
  intro K
  let m : ℕ :=
    (2 * ell).factorial * (3 * ell).factorial *
      2 ^ Fintype.card (CubicKernelLoopEdge K.graph)
  have hfixed := sum_cubicKernelSubdivisionDatum_profile
    (K := K) (F := fun L ↦ (m : 𝕜)⁻¹ * F K L)
  have hleft :
      (∑ D : CubicKernelSubdivisionDatum k ell K.graph,
          (CubicKernelPresentation.globalMultiplicity
            (⟨K, D⟩ : CubicKernelPresentation k ell) : 𝕜)⁻¹ *
            F K D.profile) =
        k.factorial •
          ∑ L : CubicKernelLengthProfile k ell K.graph,
            (m : 𝕜)⁻¹ * F K L := by
    simpa only [CubicKernelPresentation.globalMultiplicity, m] using hfixed
  rw [hleft]
  calc
    k.factorial •
          ∑ L : CubicKernelLengthProfile k ell K.graph,
            (m : 𝕜)⁻¹ * F K L =
        ∑ L : CubicKernelLengthProfile k ell K.graph,
          ((k.factorial : 𝕜) * (m : 𝕜)⁻¹) * F K L := by
      simp only [nsmul_eq_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ L : CubicKernelLengthProfile k ell K.graph,
          ((k.factorial : 𝕜) /
              (((2 * ell).factorial : 𝕜) *
                ((3 * ell).factorial : 𝕜)) *
            (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : 𝕜)⁻¹) *
              F K L) := by
      apply Fintype.sum_congr
      intro L
      rw [factorial_mul_globalMultiplicity_inv_eq_profileFactor
        (𝕜 := 𝕜) (k := k) K]
    _ = (k.factorial : 𝕜) /
          (((2 * ell).factorial : 𝕜) *
            ((3 * ell).factorial : 𝕜)) *
        (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : 𝕜)⁻¹ *
          ∑ L : CubicKernelLengthProfile k ell K.graph, F K L) := by
      simp only [Finset.mul_sum, mul_assoc]

/-- The constant-mark kernel integral written directly as a function of the
admissible length profile; the original label bijection does not occur. -/
def cubicLengthProfileConstantMarkedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (L : CubicKernelLengthProfile k ell K.graph) : ℝ :=
  ∫ x : Fin (2 * ell) → S,
    (∏ i : Fin (2 * ell),
        mark (x i) * Real.exp (-t * M.degreeFunction (x i))) *
      ∏ e : Fin (3 * ell),
        constantMarkedPathEdgeFactor M t mark
          (L.length e).val x (K.graph.endpoints e)
    ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)

@[simp]
theorem cubicLengthProfileConstantMarkedKernelIntegral_profile
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    cubicLengthProfileConstantMarkedKernelIntegral M t mark K D.profile =
      cubicSubdivisionConstantMarkedKernelIntegral M t mark K D :=
  rfl

/-- Fixed-kernel specialization of the profile regrouping identity to the
literal constant-mark kernel integral. -/
theorem sum_cubicSubdivisionConstantMarkedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    letI := cubicKernelLengthProfileFintype k ell K.graph
    letI := cubicKernelSubdivisionDatumFintype k ell K.graph
    (∑ D : CubicKernelSubdivisionDatum k ell K.graph,
        cubicSubdivisionConstantMarkedKernelIntegral M t mark K D) =
      k.factorial •
        ∑ L : CubicKernelLengthProfile k ell K.graph,
          cubicLengthProfileConstantMarkedKernelIntegral M t mark K L := by
  simpa only [cubicLengthProfileConstantMarkedKernelIntegral_profile] using
    (sum_cubicKernelSubdivisionDatum_profile
      (K := K)
      (F := cubicLengthProfileConstantMarkedKernelIntegral M t mark K))

/-- Complex-valued global specialization for the constant-mark kernel
integral.  This is the finite cubic profile sum used by the analytic
positive-surplus expansion. -/
theorem sum_cubicKernelPresentations_invMultiplicity_constantMarkedIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (mark : C(S, ℝ))
    {k ell : ℕ} :
    letI := labelledConnectedCubicKernelFintype ell
    letI : ∀ K : LabelledConnectedCubicKernel ell,
        Fintype (CubicKernelLengthProfile k ell K.graph) :=
      fun K ↦ cubicKernelLengthProfileFintype k ell K.graph
    letI : ∀ K : LabelledConnectedCubicKernel ell,
        Fintype (CubicKernelSubdivisionDatum k ell K.graph) :=
      fun K ↦ cubicKernelSubdivisionDatumFintype k ell K.graph
    (∑ P : CubicKernelPresentation k ell,
        (P.globalMultiplicity : ℂ)⁻¹ *
          (cubicSubdivisionConstantMarkedKernelIntegral
            M t mark P.1 P.2 : ℂ)) =
      (k.factorial : ℂ) /
          (((2 * ell).factorial : ℂ) *
            ((3 * ell).factorial : ℂ)) *
        ∑ K : LabelledConnectedCubicKernel ell,
          (((2 ^ Fintype.card (CubicKernelLoopEdge K.graph) : ℕ) : ℂ)⁻¹ *
            ∑ L : CubicKernelLengthProfile k ell K.graph,
              (cubicLengthProfileConstantMarkedKernelIntegral
                M t mark K L : ℂ)) := by
  simpa only [cubicLengthProfileConstantMarkedKernelIntegral_profile] using
    (sum_cubicKernelPresentations_invMultiplicity_profile
      (𝕜 := ℂ) (k := k) (ell := ell)
      (fun K L ↦
        (cubicLengthProfileConstantMarkedKernelIntegral M t mark K L : ℂ)))

end PerronWright.GraphCore
