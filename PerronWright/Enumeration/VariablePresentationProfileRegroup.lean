import PerronWright.Enumeration.VariableGlobalWeightedRegroup
import PerronWright.Enumeration.NoncubicVariableKernelRegroup

/-!
# Length-profile regrouping for variable noncubic presentations

The bounded-kernel profile integral depends on the endpoint table and the
intrinsic length table, but not on the original vertex-labelling
equivalence.  It is also invariant under simultaneous branch/edge
coordinate relabelling and under the independent loop reversals occurring
in a global symmetry code.

Combining those facts with the exact global presentation fibre gives a
literal equality between the actual fixed-size noncubic core sum and a
finite weighted sum over connected noncubic bounded kernels and admissible
length profiles.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Forget the admissibility proofs and package a bounded kernel together
with one admissible length profile as the raw bounded table/length datum. -/
def boundedKernelLengthDatumOfProfile
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (L : BoundedKernelLengthProfile k K) :
    BoundedKernelLengthDatum k ell :=
  ⟨K.shape.1, K.shape.2.1, K.shape.2.2, L.length⟩

/-- Complex profile integral attached to one bounded kernel and one
admissible internal-length profile. -/
def boundedKernelLengthProfileIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (L : BoundedKernelLengthProfile k K) : ℂ :=
  boundedKernelProfileLengthIntegral M tau
    (boundedKernelLengthDatumOfProfile K L)

/-- Path factors commute with a relabelling of their endpoint coordinates. -/
theorem profilePathEdgeFactor_map_equiv
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {n : ℕ} (gamma : Equiv.Perm (Fin n))
    (x : Fin n → S) (m : ℕ) (z : Sym2 (Fin n)) :
    profilePathEdgeFactor M tau
        (fun i ↦ x (gamma.symm i)) m (Sym2.map gamma z) =
      profilePathEdgeFactor M tau x m z := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      simp [profilePathEdgeFactor]

/-- The profile integral is unchanged by simultaneous branch- and
kernel-edge-coordinate relabelling. -/
theorem boundedKernelLengthProfileIntegral_coordinateRelabel
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (K : LabelledBoundedKernel ell)
    (L : BoundedKernelLengthProfile k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    boundedKernelLengthProfileIntegral M tau
        (K.coordinateRelabel gamma) (L.coordinateRelabel gamma) =
      boundedKernelLengthProfileIntegral M tau K L := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin K.shape.1.val ↦ S) gamma.1
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin K.shape.1.val ↦ M.mu))
      (Measure.pi (fun _ : Fin K.shape.1.val ↦ M.mu)) :=
    measurePreserving_piCongrLeft
      (fun _ : Fin K.shape.1.val ↦ M.mu) gamma.1
  have he (x : Fin K.shape.1.val → S) :
      e x = fun i ↦ x (gamma.1.symm i) := by
    funext i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  let oldEdgeFactor (x : Fin K.shape.1.val → S)
      (j : Fin K.shape.2.1.val) : ℂ :=
    profilePathEdgeFactor M tau x (L.length j).val (K.shape.2.2 j)
  let newIntegrand (x : Fin K.shape.1.val → S) : ℂ :=
    (∏ i : Fin K.shape.1.val, tau (x i)) *
      ∏ j : Fin K.shape.2.1.val,
        profilePathEdgeFactor M tau x
          ((L.coordinateRelabel gamma).length j).val
          ((K.coordinateRelabel gamma).shape.2.2 j)
  have hvert (x : Fin K.shape.1.val → S) :
      (∏ i : Fin K.shape.1.val, tau ((e x) i)) =
        ∏ i : Fin K.shape.1.val, tau (x i) := by
    rw [he]
    exact Equiv.prod_comp gamma.1.symm (fun i ↦ tau (x i))
  have hedge (x : Fin K.shape.1.val → S) :
      (∏ j : Fin K.shape.2.1.val,
          profilePathEdgeFactor M tau (e x)
            ((L.coordinateRelabel gamma).length j).val
            ((K.coordinateRelabel gamma).shape.2.2 j)) =
        ∏ j : Fin K.shape.2.1.val, oldEdgeFactor x j := by
    calc
      (∏ j : Fin K.shape.2.1.val,
          profilePathEdgeFactor M tau (e x)
            ((L.coordinateRelabel gamma).length j).val
            ((K.coordinateRelabel gamma).shape.2.2 j)) =
          ∏ j : Fin K.shape.2.1.val,
            oldEdgeFactor x (gamma.2.symm j) := by
        apply Finset.prod_congr rfl
        intro j _hj
        rw [he]
        exact profilePathEdgeFactor_map_equiv M tau gamma.1 x
          (L.length (gamma.2.symm j)).val
          (K.shape.2.2 (gamma.2.symm j))
      _ = ∏ j : Fin K.shape.2.1.val, oldEdgeFactor x j :=
        Equiv.prod_comp gamma.2.symm (oldEdgeFactor x)
  have hintegrand (x : Fin K.shape.1.val → S) :
      newIntegrand (e x) =
        (∏ i : Fin K.shape.1.val, tau (x i)) *
          ∏ j : Fin K.shape.2.1.val, oldEdgeFactor x j := by
    dsimp only [newIntegrand]
    rw [hvert x, hedge x]
  unfold boundedKernelLengthProfileIntegral
    boundedKernelProfileLengthIntegral boundedKernelLengthDatumOfProfile
  change (∫ x : Fin K.shape.1.val → S, newIntegrand x
      ∂Measure.pi (fun _ : Fin K.shape.1.val ↦ M.mu)) = _
  symm
  simpa only [hintegrand, oldEdgeFactor, newIntegrand] using
    (hmp.integral_comp' newIntegrand)

/-- Coordinate relabelling preserves the exact coordinate multiplicity. -/
theorem LabelledBoundedKernel.coordinateMultiplicity_coordinateRelabel
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (gamma : BoundedKernelCoordinatePerm K) :
    (K.coordinateRelabel gamma).coordinateMultiplicity =
      K.coordinateMultiplicity := by
  unfold LabelledBoundedKernel.coordinateMultiplicity
  change K.shape.1.val.factorial * K.shape.2.1.val.factorial *
      2 ^ Fintype.card (BoundedKernelLoopEdge (K.coordinateRelabel gamma)) =
    K.shape.1.val.factorial * K.shape.2.1.val.factorial *
      2 ^ Fintype.card (BoundedKernelLoopEdge K)
  rw [boundedKernelLoopEdge_card_coordinateRelabel]

namespace BoundedKernelPresentation

/-- The length-profile integral displayed by a global bounded-kernel
presentation. -/
def profileIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (P : BoundedKernelPresentation k ell) : ℂ :=
  boundedKernelLengthProfileIntegral M tau
    P.1.toLabelledBoundedKernel P.2.profile

/-- The length profile and its integral are invariant under every global
symmetry code: coordinate permutations merely relabel the integration and
loop reversals do not alter the length table. -/
@[simp] theorem profileIntegral_applySymmetry
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    (P.applySymmetry c).profileIntegral M tau =
      P.profileIntegral M tau := by
  change boundedKernelLengthProfileIntegral M tau
      (P.1.toLabelledBoundedKernel.coordinateRelabel c.1)
      (((P.2.coordinateRelabel c.1).reverseLoops
        (P.targetLoopSet c)).profile) = _
  rw [BoundedKernelSubdivisionDatum.reverseLoops_profile]
  exact boundedKernelLengthProfileIntegral_coordinateRelabel
    M tau P.1.toLabelledBoundedKernel P.2.profile c.1

/-- The multiplicity is likewise invariant under every global symmetry
code. -/
@[simp] theorem globalMultiplicity_applySymmetry
    {k ell : ℕ} (P : BoundedKernelPresentation k ell)
    (c : BoundedKernelCoordinateCode P.1.toLabelledBoundedKernel) :
    (P.applySymmetry c).globalMultiplicity = P.globalMultiplicity := by
  exact LabelledBoundedKernel.coordinateMultiplicity_coordinateRelabel
    P.1.toLabelledBoundedKernel c.1

end BoundedKernelPresentation

/-- The canonical base presentation displays exactly the canonical bounded
kernel/length datum of the actual core. -/
theorem noncubicAdmissibleAttachmentCoreBasePresentation_profileIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (hell : 0 < ell)
    (G : NoncubicAdmissibleAttachmentCore k ell) :
    BoundedKernelPresentation.profileIntegral M tau
        (noncubicAdmissibleAttachmentCoreBasePresentation hell G).1 =
      boundedKernelProfileLengthIntegral M tau
        (noncubicCoreKernelLengthDatum hell G) := by
  rfl

/-- Every connected noncubic presentation displays the exact complex
weight of its reconstructed actual core.  The proof transports the
canonical actual-core identity through the proved global symmetry fibre. -/
theorem finiteComplexGraphWeight_eq_presentationProfileIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (hell : 0 < ell)
    (P : ConnectedNoncubicBoundedKernelPresentation k ell)
    (s₀ : S) :
    finiteComplexGraphWeight M tau P.2.reconstructedGraph =
      P.toBoundedKernelPresentation.profileIntegral M tau := by
  let G : NoncubicAdmissibleAttachmentCore k ell :=
    ⟨P.2.reconstructedGraph,
      P.reconstructedGraph_isNoncubicAdmissibleAttachmentCore hell⟩
  let B := noncubicAdmissibleAttachmentCoreBasePresentation hell G
  let Q : BoundedKernelPresentation.ReconstructionFibre
      (ell := ell) G.1 :=
    ⟨P.toBoundedKernelPresentation, rfl⟩
  obtain ⟨c, hc⟩ :=
    BoundedKernelPresentation.symmetryFibreMap_surjective hell B Q
  have hpresentation : B.1.applySymmetry c =
      P.toBoundedKernelPresentation :=
    congrArg Subtype.val hc
  calc
    finiteComplexGraphWeight M tau P.2.reconstructedGraph =
        finiteComplexGraphWeight M tau G.1 := rfl
    _ = boundedKernelProfileLengthIntegral M tau
          (noncubicCoreKernelLengthDatum hell G) :=
      finiteComplexGraphWeight_eq_boundedKernelProfileLengthIntegral
        M tau hell G s₀
    _ = B.1.profileIntegral M tau :=
      (noncubicAdmissibleAttachmentCoreBasePresentation_profileIntegral
        M tau hell G).symm
    _ = (B.1.applySymmetry c).profileIntegral M tau :=
      (BoundedKernelPresentation.profileIntegral_applySymmetry
        M tau B.1 c).symm
    _ = P.toBoundedKernelPresentation.profileIntegral M tau := by
      rw [hpresentation]

/-- Algebraic profile regrouping of the inverse-multiplicity presentation
sum.  A fixed kernel contributes exactly `k!` copies of each admissible
length profile, one for every original-label equivalence. -/
theorem sum_connectedNoncubicPresentations_invMultiplicity_profile
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {k ell : ℕ} (hell : 0 < ell)
    (F : (K : LabelledConnectedNoncubicKernel ell) →
      BoundedKernelLengthProfile k K.1.toLabelledBoundedKernel → 𝕜) :
    letI := connectedNoncubicBoundedKernelPresentationFintype
      (k := k) (ell := ell) hell
    letI : ∀ K : LabelledConnectedNoncubicKernel ell,
        Fintype (BoundedKernelLengthProfile k
          K.1.toLabelledBoundedKernel) :=
      fun K ↦ boundedKernelLengthProfileFintype k
        K.1.toLabelledBoundedKernel
    letI : ∀ K : LabelledConnectedNoncubicKernel ell,
        Fintype (BoundedKernelSubdivisionDatum k
          K.1.toLabelledBoundedKernel) :=
      fun K ↦ boundedKernelSubdivisionDatumFintype k
        K.1.toLabelledBoundedKernel
    (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
        (P.globalMultiplicity : 𝕜)⁻¹ * F P.1 P.2.profile) =
      (k.factorial : 𝕜) *
        ∑ K : LabelledConnectedNoncubicKernel ell,
          (K.1.toLabelledBoundedKernel.coordinateMultiplicity : 𝕜)⁻¹ *
            ∑ L : BoundedKernelLengthProfile k
                K.1.toLabelledBoundedKernel, F K L := by
  let _ : Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) :=
    connectedNoncubicBoundedKernelPresentationFintype hell
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelLengthProfile k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelLengthProfileFintype k
      K.1.toLabelledBoundedKernel
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelSubdivisionDatum k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelSubdivisionDatumFintype k
      K.1.toLabelledBoundedKernel
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Fintype.sum_congr
  intro K
  let m : ℕ := K.1.toLabelledBoundedKernel.coordinateMultiplicity
  have hfixed := sum_boundedKernelSubdivisionDatum_profile
    (K := K.1.toLabelledBoundedKernel)
    (F := fun L ↦ (m : 𝕜)⁻¹ * F K L)
  have hleft :
      (∑ D : BoundedKernelSubdivisionDatum k
          K.1.toLabelledBoundedKernel,
          (ConnectedNoncubicBoundedKernelPresentation.globalMultiplicity
            (⟨K, D⟩ :
              ConnectedNoncubicBoundedKernelPresentation k ell) : 𝕜)⁻¹ *
            F K D.profile) =
        k.factorial •
          ∑ L : BoundedKernelLengthProfile k
              K.1.toLabelledBoundedKernel,
            (m : 𝕜)⁻¹ * F K L := by
    simpa only [ConnectedNoncubicBoundedKernelPresentation.globalMultiplicity,
      ConnectedNoncubicBoundedKernelPresentation.toBoundedKernelPresentation,
      BoundedKernelPresentation.globalMultiplicity, m] using hfixed
  rw [hleft]
  calc
    k.factorial •
          ∑ L : BoundedKernelLengthProfile k
              K.1.toLabelledBoundedKernel,
            (m : 𝕜)⁻¹ * F K L =
        (k.factorial : 𝕜) *
          ((m : 𝕜)⁻¹ *
            ∑ L : BoundedKernelLengthProfile k
              K.1.toLabelledBoundedKernel, F K L) := by
      simp only [nsmul_eq_mul, Finset.mul_sum]
    _ = (k.factorial : 𝕜) *
          ((K.1.toLabelledBoundedKernel.coordinateMultiplicity : 𝕜)⁻¹ *
            ∑ L : BoundedKernelLengthProfile k
              K.1.toLabelledBoundedKernel, F K L) := by
      rfl

/-- Exact fixed-size weighted regrouping of actual noncubic cores into
connected noncubic bounded kernels and admissible length profiles. -/
theorem fixedSurplusNoncubicCoreWeightSum_eq_connectedKernelProfiles
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (hell : 0 < ell) (s₀ : S) :
    letI : ∀ K : LabelledConnectedNoncubicKernel ell,
        Fintype (BoundedKernelLengthProfile k
          K.1.toLabelledBoundedKernel) :=
      fun K ↦ boundedKernelLengthProfileFintype k
        K.1.toLabelledBoundedKernel
    fixedSurplusNoncubicCoreWeightSum M tau ell k =
      (k.factorial : ℂ) *
        ∑ K : LabelledConnectedNoncubicKernel ell,
          (K.1.toLabelledBoundedKernel.coordinateMultiplicity : ℂ)⁻¹ *
            ∑ L : BoundedKernelLengthProfile k
                K.1.toLabelledBoundedKernel,
              boundedKernelLengthProfileIntegral M tau
                K.1.toLabelledBoundedKernel L := by
  let _ : Fintype (ConnectedNoncubicBoundedKernelPresentation k ell) :=
    connectedNoncubicBoundedKernelPresentationFintype hell
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelLengthProfile k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelLengthProfileFintype k
      K.1.toLabelledBoundedKernel
  let _ (K : LabelledConnectedNoncubicKernel ell) :
      Fintype (BoundedKernelSubdivisionDatum k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelSubdivisionDatumFintype k
      K.1.toLabelledBoundedKernel
  have hglobal :=
    sum_connectedNoncubicPresentations_invMultiplicity_graphInvariant
      (k := k) (ell := ell) hell
      (fun G ↦ finiteComplexGraphWeight M tau G)
  have hpresentation :
      (∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
          (P.globalMultiplicity : ℂ)⁻¹ *
            finiteComplexGraphWeight M tau P.2.reconstructedGraph) =
        ∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
          (P.globalMultiplicity : ℂ)⁻¹ *
            boundedKernelLengthProfileIntegral M tau
              P.1.1.toLabelledBoundedKernel P.2.profile := by
    apply Fintype.sum_congr
    intro P
    rw [finiteComplexGraphWeight_eq_presentationProfileIntegral
      M tau hell P s₀]
    rfl
  have hprofile :=
    sum_connectedNoncubicPresentations_invMultiplicity_profile
      (𝕜 := ℂ) (k := k) (ell := ell) hell
      (fun K L ↦ boundedKernelLengthProfileIntegral M tau
        K.1.toLabelledBoundedKernel L)
  unfold fixedSurplusNoncubicCoreWeightSum
  calc
    (∑ G : NoncubicAdmissibleAttachmentCore k ell,
        finiteComplexGraphWeight M tau G.1) =
        ∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
          (P.globalMultiplicity : ℂ)⁻¹ *
            finiteComplexGraphWeight M tau P.2.reconstructedGraph :=
      hglobal.symm
    _ = ∑ P : ConnectedNoncubicBoundedKernelPresentation k ell,
          (P.globalMultiplicity : ℂ)⁻¹ *
            boundedKernelLengthProfileIntegral M tau
              P.1.1.toLabelledBoundedKernel P.2.profile := hpresentation
    _ = (k.factorial : ℂ) *
        ∑ K : LabelledConnectedNoncubicKernel ell,
          (K.1.toLabelledBoundedKernel.coordinateMultiplicity : ℂ)⁻¹ *
            ∑ L : BoundedKernelLengthProfile k
                K.1.toLabelledBoundedKernel,
              boundedKernelLengthProfileIntegral M tau
                K.1.toLabelledBoundedKernel L := hprofile

end PerronWright.GraphCore
