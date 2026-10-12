import PerronWright.Enumeration.NoncubicBoundedKernelRemainder
import PerronWright.Enumeration.KernelLengthRegroup
import PerronWright.Enumeration.ComplexProfileCorePathFactorization

/-!
# Exact variable-valence kernel regrouping at fixed core size

For a literal noncubic admissible core this file records, canonically and
without a cubicity hypothesis,

* the bounded relabelled kernel table;
* the number of degree-two vertices carried by every suppressed edge;
* the exact complex profile integral represented by that table; and
* the finite fibre multiplicity of the map from actual cores to bounded
  table/length data.

The final theorem is an exact weighted finite regrouping of the actual
fixed-size noncubic core sum.  It is the finite-size combinatorial input for
the joint analytic extra-`X` theorem in
`NoncubicBoundedKernelRemainder`.  Passing from these finite length fibres
to one unrestricted marked-path resolvent product is a separate all-length
generating-series step.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Canonical bounded kernel/length datum -/

/-- The minimum-degree-two fact attached to a noncubic admissible core. -/
theorem noncubicCore_minDegree_two
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell) :
    ∀ v, 2 ≤ H.1.degree v :=
  minDegree_two_of_isTwoCore_univ H.2.1.2.1

/-- The exact positive-surplus edge count of a noncubic admissible core. -/
theorem noncubicCore_edgeCount
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell) :
    H.1.edgeFinset.card = Fintype.card (Fin q) + ell := by
  simpa only [Fintype.card_fin] using H.2.1.2.2

/-- The induced degree-two graph of a positive-surplus noncubic core is a
forest. -/
theorem noncubicCore_twoGraph_isAcyclic
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (twoGraph H.1).IsAcyclic :=
  degreeTwo_induced_isAcyclic H.1 H.2.1.1
    (noncubicCore_minDegree_two H) hell (noncubicCore_edgeCount H)

/-- Canonical relabelling of the actual branch vertices. -/
def noncubicCoreBranchEquiv
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell) :
    (branchingVertices H.1 : Set (Fin q)) ≃
      Fin (branchingVertices H.1).card :=
  Finset.equivFin (branchingVertices H.1)

/-- Canonical relabelling of all suppressed kernel-edge labels. -/
def noncubicCoreKernelEdgeEquiv
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell) :
    KernelEdgeLabel H.1 ≃ Fin (Nat.card (KernelEdgeLabel H.1)) := by
  letI : Fintype (twoGraph H.1).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin q) // e ∈ directBranchEdges H.1} :=
    FinsetCoe.fintype (directBranchEdges H.1)
  letI : Fintype (KernelEdgeLabel H.1) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  apply Fintype.equivFinOfCardEq
  simp only [Nat.card_eq_fintype_card]

/-- Intrinsic number of degree-two vertices on a suppressed edge; direct
branch edges carry length zero. -/
def noncubicCoreKernelEdgeLengthNat
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell) :
    KernelEdgeLabel H.1 → ℕ
  | Sum.inl C => Nat.card C
  | Sum.inr _ => 0

theorem noncubicCoreKernelEdgeLengthNat_le
    {q ell : ℕ} (H : NoncubicAdmissibleAttachmentCore q ell)
    (e : KernelEdgeLabel H.1) :
    noncubicCoreKernelEdgeLengthNat H e ≤ q := by
  cases e with
  | inl C =>
      have hcard : Fintype.card C ≤ q := by
        simpa only [Fintype.card_fin] using
          (Fintype.card_le_of_injective
            (fun x : C ↦ x.val.val)
            (fun x y hxy ↦ Subtype.ext (Subtype.ext hxy)))
      simpa only [noncubicCoreKernelEdgeLengthNat,
        Nat.card_eq_fintype_card] using hcard
  | inr d =>
      simp only [noncubicCoreKernelEdgeLengthNat]
      exact Nat.zero_le q

/-- Canonical bounded endpoint table together with the intrinsic path
length on every suppressed edge of one literal noncubic core. -/
def noncubicCoreKernelLengthDatum
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    BoundedKernelLengthDatum q ell := by
  let hmin := noncubicCore_minDegree_two H
  let hacyc := noncubicCore_twoGraph_isAcyclic hell H
  let B := branchingVertices H.1
  let E := KernelEdgeLabel H.1
  have hb : B.card ≤ 2 * ell :=
    branchingVertices_card_le_two_surplus H.1 hmin
      (noncubicCore_edgeCount H)
  have he : Nat.card E ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus H.1 H.2.1.1 hmin hell
      (noncubicCore_edgeCount H)
  let nv : Fin (2 * ell + 1) := ⟨B.card, by omega⟩
  let ne : Fin (3 * ell + 1) := ⟨Nat.card E, by omega⟩
  let eB : (B : Set (Fin q)) ≃ Fin nv.val :=
    noncubicCoreBranchEquiv H
  let eE : E ≃ Fin ne.val := noncubicCoreKernelEdgeEquiv H
  let table : Fin ne.val → Sym2 (Fin nv.val) := fun j ↦
    Sym2.map eB (kernelBranchEndpoints H.1 hmin hacyc (eE.symm j))
  let length : Fin ne.val → Fin (q + 1) := fun j ↦
    ⟨noncubicCoreKernelEdgeLengthNat H (eE.symm j),
      Nat.lt_succ_of_le
        (noncubicCoreKernelEdgeLengthNat_le H (eE.symm j))⟩
  exact ⟨nv, ne, table, length⟩

@[simp] theorem noncubicCoreKernelLengthDatum_vertexCount
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (noncubicCoreKernelLengthDatum hell H).1.val =
      (branchingVertices H.1).card := by
  rfl

@[simp] theorem noncubicCoreKernelLengthDatum_edgeCount
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (noncubicCoreKernelLengthDatum hell H).2.1.val =
      Nat.card (KernelEdgeLabel H.1) := by
  rfl

/-- The strict noncubic edge gap is visible directly on the canonical
bounded length datum. -/
theorem noncubicCoreKernelLengthDatum_edgeCount_lt
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (noncubicCoreKernelLengthDatum hell H).2.1.val < 3 * ell := by
  rw [noncubicCoreKernelLengthDatum_edgeCount]
  exact kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic hell H.2

/-! ## Exact profile integral of the canonical datum -/

/-- Complex profile integral represented by one bounded endpoint table and
one fixed internal-length assignment. -/
def boundedKernelProfileLengthIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q ell : ℕ} (D : BoundedKernelLengthDatum q ell) : ℂ :=
  ∫ x : Fin D.1.val → S,
    (∏ i : Fin D.1.val, tau (x i)) *
      ∏ j : Fin D.2.1.val,
        profilePathEdgeFactor M tau x (D.2.2.2 j).val (D.2.2.1 j)
    ∂Measure.pi (fun _ : Fin D.1.val ↦ M.mu)

/-- Complex-valued version of the branch-coordinate relabelling identity. -/
theorem integral_coreBranch_relabel_complex
    (M : CompactBJRModel S)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {nv : ℕ}
    (eB : (branchingVertices G : Set V) ≃ Fin nv)
    (F : (coreBranchIndex G → S) → ℂ) :
    (∫ b : coreBranchIndex G → S, F b
        ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu)) =
      ∫ x : Fin nv → S,
        F (fun b ↦ x (eB (coreBranchEquivBranching G hmin b)))
        ∂Measure.pi (fun _ : Fin nv ↦ M.mu) := by
  let e : coreBranchIndex G ≃ Fin nv :=
    (coreBranchEquivBranching G hmin).trans eB
  let φ := MeasurableEquiv.piCongrLeft
    (fun _ : coreBranchIndex G ↦ S) e.symm
  have hmp : MeasurePreserving φ
      (Measure.pi (fun _ : Fin nv ↦ M.mu))
      (Measure.pi (fun _ : coreBranchIndex G ↦ M.mu)) :=
    measurePreserving_piCongrLeft
      (fun _ : coreBranchIndex G ↦ M.mu) e.symm
  have hφ (x : Fin nv → S) :
      φ x = fun b ↦ x (eB (coreBranchEquivBranching G hmin b)) := by
    funext b
    simp [φ, e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  symm
  simpa only [hφ] using hmp.integral_comp' F

set_option linter.style.haveILetI false in
/-- Exact graph--profile reconstruction identity for the canonical bounded
table/length datum of one actual noncubic core. -/
theorem finiteComplexGraphWeight_eq_boundedKernelProfileLengthIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) (s₀ : S) :
    finiteComplexGraphWeight M tau H.1 =
      boundedKernelProfileLengthIntegral M tau
        (noncubicCoreKernelLengthDatum hell H) := by
  classical
  let G := H.1
  let hmin := noncubicCore_minDegree_two H
  let hacyc := noncubicCore_twoGraph_isAcyclic hell H
  let B := branchingVertices G
  let E := KernelEdgeLabel G
  let nv : Fin (2 * ell + 1) :=
    ⟨B.card, by
      exact Nat.lt_succ_of_le
        (branchingVertices_card_le_two_surplus G hmin
          (noncubicCore_edgeCount H))⟩
  let ne : Fin (3 * ell + 1) :=
    ⟨Nat.card E, by
      exact Nat.lt_succ_of_le
        (kernelEdgeLabel_card_le_three_surplus G H.2.1.1 hmin hell
          (noncubicCore_edgeCount H))⟩
  let eB : (B : Set (Fin q)) ≃ Fin nv.val :=
    noncubicCoreBranchEquiv H
  let eE : E ≃ Fin ne.val := noncubicCoreKernelEdgeEquiv H
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin q) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  have hchoice := fun C : (twoGraph G).ConnectedComponent ↦
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  choose n hn e qL qR hne hL hR using hchoice
  rw [finiteComplexGraphWeight_eq_integral_branch_mul_pathEdgeCoefficients
    M tau G hacyc s₀ n e qL qR hne hL hR]
  rw [integral_coreBranch_relabel_complex M G hmin eB]
  unfold boundedKernelProfileLengthIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  let b : coreBranchIndex G → S :=
    fun c ↦ x (eB (coreBranchEquivBranching G hmin c))
  change
    complexProfileCoreBranchFactor M tau G s₀ b *
        ∏ C : (twoGraph G).ConnectedComponent,
          profilePathEdgeCoefficient M tau
            (b (componentBoundaryStubBranchIndex G C (qL C)))
            (b (componentBoundaryStubBranchIndex G C (qR C)))
            (n C + 1) = _
  rw [complexProfileCoreBranchFactor_relabel_eq_kernelFactors
    M tau G hmin hacyc s₀ eB x]
  have hcomp :
      (∏ C : (twoGraph G).ConnectedComponent,
          profilePathEdgeCoefficient M tau
            (b (componentBoundaryStubBranchIndex G C (qL C)))
            (b (componentBoundaryStubBranchIndex G C (qR C)))
            (n C + 1)) =
        ∏ C : (twoGraph G).ConnectedComponent,
          profilePathEdgeFactor M tau x (Nat.card C)
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro C _
    have hcard : Nat.card C = n C + 1 := by
      simpa only [Nat.card_eq_fintype_card] using hn C
    rw [hcard]
    have hend := degreeTwoPathEndpoints_eq_boundaryStubPair
      G hacyc C (qL C) (qR C) (hne C)
    let bL : (branchingVertices G : Set (Fin q)) :=
      ⟨(qL C).val.2, by
        have hne2 := (componentBoundaryStubBranchIndex G C (qL C)).property
        change G.degree (qL C).val.2 ≠ 2 at hne2
        have htwo := hmin (qL C).val.2
        change 2 ≤ G.degree (qL C).val.2 at htwo
        simp only [branchingVertices, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
    let bR : (branchingVertices G : Set (Fin q)) :=
      ⟨(qR C).val.2, by
        have hne2 := (componentBoundaryStubBranchIndex G C (qR C)).property
        change G.degree (qR C).val.2 ≠ 2 at hne2
        have htwo := hmin (qR C).val.2
        change 2 ≤ G.degree (qR C).val.2 at htwo
        simp only [branchingVertices, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
    have hendBranch :
        kernelBranchEndpoints G hmin hacyc
            (Sum.inl C : KernelEdgeLabel G) = s(bL, bR) := by
      apply Sym2.map.injective Subtype.val_injective
      calc
        Sym2.map Subtype.val
            (kernelBranchEndpoints G hmin hacyc
              (Sum.inl C : KernelEdgeLabel G)) =
            kernelEdgeEndpoints G hacyc
              (Sum.inl C : KernelEdgeLabel G) :=
          kernelBranchEndpoints_map_val G hmin hacyc _
        _ = degreeTwoPathEndpoints G hacyc C := rfl
        _ = s((qL C).val.2, (qR C).val.2) := hend
        _ = Sym2.map Subtype.val s(bL, bR) := by simp [bL, bR]
    rw [hendBranch, Sym2.map_mk, profilePathEdgeFactor_mk]
    rfl
  rw [hcomp]
  let actualFactor : E → ℂ := fun a ↦
    profilePathEdgeFactor M tau x
      (noncubicCoreKernelEdgeLengthNat H a)
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc a))
  have hsplit :
      (∏ a : E, actualFactor a) =
        (∏ C : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C : KernelEdgeLabel G)) *
        ∏ d : {a // a ∈ directBranchEdges G},
          actualFactor (Sum.inr d : KernelEdgeLabel G) := by
    change
      (∏ a : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor a) = _
    exact Fintype.prod_sum_type actualFactor
  have hlength (j : Fin ne.val) :
      noncubicCoreKernelEdgeLengthNat H (eE.symm j) =
        ((noncubicCoreKernelLengthDatum hell H).2.2.2 j).val := by
    rfl
  have hendpoint (j : Fin ne.val) :
      Sym2.map eB (kernelBranchEndpoints G hmin hacyc (eE.symm j)) =
        (noncubicCoreKernelLengthDatum hell H).2.2.1 j := by
    rfl
  have hrelabel :
      (∏ a : E, actualFactor a) =
        ∏ j : Fin ne.val,
          profilePathEdgeFactor M tau x
            ((noncubicCoreKernelLengthDatum hell H).2.2.2 j).val
            ((noncubicCoreKernelLengthDatum hell H).2.2.1 j) := by
    exact Fintype.prod_equiv eE actualFactor
      (fun j : Fin ne.val ↦
        profilePathEdgeFactor M tau x
          ((noncubicCoreKernelLengthDatum hell H).2.2.2 j).val
          ((noncubicCoreKernelLengthDatum hell H).2.2.1 j))
      (fun a ↦ by
        dsimp only [actualFactor]
        rw [← hlength (eE a), ← hendpoint (eE a)]
        simp only [Equiv.symm_apply_apply])
  have hdirect :
      (∏ d : {a // a ∈ directBranchEdges G},
          profilePathEdgeCoefficient M tau
            (x (Sym2.sortEquiv
              (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G)))).1.1)
            (x (Sym2.sortEquiv
              (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G)))).1.2) 0) =
        ∏ d : {a // a ∈ directBranchEdges G},
          actualFactor (Sum.inr d : KernelEdgeLabel G) := by
    apply Finset.prod_congr rfl
    intro d _
    let z := Sym2.map eB (kernelBranchEndpoints G hmin hacyc
      (Sum.inr d : KernelEdgeLabel G))
    calc
      profilePathEdgeCoefficient M tau
          (x (Sym2.sortEquiv z).1.1)
          (x (Sym2.sortEquiv z).1.2) 0 =
        complexKernelEdgeFactor M x z :=
          profilePathEdgeCoefficient_zero_eq_complexKernelEdgeFactor
            M tau x z
      _ = profilePathEdgeFactor M tau x 0 z := by
        symm
        induction z using Sym2.inductionOn with
        | _ i j =>
            rw [profilePathEdgeFactor_mk, complexKernelEdgeFactor_mk]
            change (M.kernel (x i) (x j) : ℂ) =
              (M.kernel (x i) (x j) : ℂ)
            rfl
      _ = actualFactor (Sum.inr d : KernelEdgeLabel G) := rfl
  calc
    ((∏ i : Fin nv.val, tau (x i)) *
          ∏ d : {a // a ∈ directBranchEdges G},
            profilePathEdgeCoefficient M tau
              (x (Sym2.sortEquiv
                (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.1)
              (x (Sym2.sortEquiv
                (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.2) 0) *
        ∏ C : (twoGraph G).ConnectedComponent,
          profilePathEdgeFactor M tau x (Nat.card C)
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) =
      ((∏ i : Fin nv.val, tau (x i)) *
          ∏ d : {a // a ∈ directBranchEdges G},
            actualFactor (Sum.inr d : KernelEdgeLabel G)) *
        ∏ C : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C : KernelEdgeLabel G) := by
            rw [hdirect]
            rfl
    _ = (∏ i : Fin nv.val, tau (x i)) *
        ((∏ C : (twoGraph G).ConnectedComponent,
            actualFactor (Sum.inl C : KernelEdgeLabel G)) *
          ∏ d : {a // a ∈ directBranchEdges G},
            actualFactor (Sum.inr d : KernelEdgeLabel G)) := by ring
    _ = (∏ i : Fin nv.val, tau (x i)) *
        ∏ a : E, actualFactor a := by rw [hsplit]
    _ = (∏ i : Fin nv.val, tau (x i)) *
        ∏ j : Fin ne.val,
          profilePathEdgeFactor M tau x
            ((noncubicCoreKernelLengthDatum hell H).2.2.2 j).val
            ((noncubicCoreKernelLengthDatum hell H).2.2.1 j) := by
              rw [hrelabel]

/-! ## Exact finite fibre multiplicity -/

/-- Number of literal noncubic cores which have a given canonical bounded
kernel/length datum. -/
def noncubicCoreKernelLengthFibreMultiplicity
    {q ell : ℕ} (hell : 0 < ell)
    (D : BoundedKernelLengthDatum q ell) : ℕ :=
  ((Finset.univ : Finset (NoncubicAdmissibleAttachmentCore q ell)).filter
    (fun H ↦ noncubicCoreKernelLengthDatum hell H = D)).card

/-- Exact weighted regrouping of the actual fixed-size noncubic core sum by
canonical bounded table and intrinsic path lengths. -/
theorem fixedSurplusNoncubicCoreWeightSum_eq_kernelLengthFibres
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q ell : ℕ} (hell : 0 < ell) (s₀ : S) :
    fixedSurplusNoncubicCoreWeightSum M tau ell q =
      ∑ D : BoundedKernelLengthDatum q ell,
        (noncubicCoreKernelLengthFibreMultiplicity hell D : ℂ) *
          boundedKernelProfileLengthIntegral M tau D := by
  classical
  unfold fixedSurplusNoncubicCoreWeightSum
  calc
    (∑ H : NoncubicAdmissibleAttachmentCore q ell,
        finiteComplexGraphWeight M tau H.1) =
        ∑ H : NoncubicAdmissibleAttachmentCore q ell,
          boundedKernelProfileLengthIntegral M tau
            (noncubicCoreKernelLengthDatum hell H) := by
      apply Fintype.sum_congr
      intro H
      exact finiteComplexGraphWeight_eq_boundedKernelProfileLengthIntegral
        M tau hell H s₀
    _ = ∑ D : BoundedKernelLengthDatum q ell,
          ∑ H : NoncubicAdmissibleAttachmentCore q ell,
            if noncubicCoreKernelLengthDatum hell H = D then
              boundedKernelProfileLengthIntegral M tau D
            else 0 := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro H
      simp
    _ = ∑ D : BoundedKernelLengthDatum q ell,
        (noncubicCoreKernelLengthFibreMultiplicity hell D : ℂ) *
          boundedKernelProfileLengthIntegral M tau D := by
      apply Fintype.sum_congr
      intro D
      unfold noncubicCoreKernelLengthFibreMultiplicity
      rw [← Finset.sum_filter]
      simp

end PerronWright.GraphCore
