import PerronWright.Enumeration.CubicKernelPathGeneratingSeries
import PerronWright.Enumeration.ComplexProfileCorePathFactorization

/-!
# Actual cubic subdivisions as generic profile path integrals

The resolvent-side cubic amplitude is written in the canonical branch
coordinates of a labelled cubic kernel.  The exact core enumeration, on the
other hand, starts from the reconstructed labelled simple graph.  This file
closes that coordinate gap for one subdivision datum.

For an arbitrary complex vertex profile, the genuine finite graph weight of
the reconstructed graph is exactly the product of the branch profiles and
the generic path coefficients attached to the kernel-edge length table.
The proof uses the already established core-component factorization and the
literal recovered-kernel endpoint and length identities; no comparison
hypothesis is introduced.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem integral_coreBranch_relabel_complex
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

/-- Complex profile integral carried by one labelled cubic kernel and one
admissible internal-length profile. -/
def cubicLengthProfileComplexKernelIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (L : CubicKernelLengthProfile k ell K.graph) : ℂ :=
  ∫ x : Fin (2 * ell) → S,
    (∏ v : Fin (2 * ell), tau (x v)) *
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2)
          (L.length e).val
    ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu)

@[simp] theorem cubicLengthProfileComplexKernelIntegral_profile
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    cubicLengthProfileComplexKernelIntegral M tau K D.profile =
      ∫ x : Fin (2 * ell) → S,
        (∏ v : Fin (2 * ell), tau (x v)) *
          ∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2)
              (D.profile.length e).val
        ∂Measure.pi (fun _ : Fin (2 * ell) ↦ M.mu) :=
  rfl

set_option linter.style.haveILetI false in
/-- Exact complex-profile factorization of the genuine reconstructed cubic
core in the canonical coordinates of its labelled kernel. -/
theorem finiteComplexGraphWeight_reconstructedGraph_eq_cubicLengthProfileIntegral
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) (s₀ : S) :
    finiteComplexGraphWeight M tau D.reconstructedGraph =
      cubicLengthProfileComplexKernelIntegral M tau K D.profile := by
  classical
  let G : SimpleGraph (Fin k) := D.reconstructedGraph
  let hmin : ∀ v, 2 ≤ G.degree v :=
    D.reconstructedGraph_minDegree_two K.cubic K.connected
  let hacyc : (twoGraph G).IsAcyclic :=
    D.reconstructedTwoGraph_isAcyclic K
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin k) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  let eB : (branchingVertices G : Set (Fin k)) ≃ Fin (2 * ell) :=
    (D.branchLabelEquivBranching K).symm
  let eE : KernelEdgeLabel G ≃ Fin (3 * ell) :=
    D.recoveredKernelEdgeEquiv K
  have hchoice := fun C : (twoGraph G).ConnectedComponent ↦
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  choose n hn e qL qR hne hL hR using hchoice
  rw [finiteComplexGraphWeight_eq_integral_branch_mul_pathEdgeCoefficients
    M tau G hacyc s₀ n e qL qR hne hL hR]
  rw [integral_coreBranch_relabel_complex M G hmin eB]
  unfold cubicLengthProfileComplexKernelIntegral
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
          profilePathEdgeFactor M tau x (n C + 1)
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro C _
    have hend := degreeTwoPathEndpoints_eq_boundaryStubPair
      G hacyc C (qL C) (qR C) (hne C)
    let bL : (branchingVertices G : Set (Fin k)) :=
      ⟨(qL C).val.2, by
        have hne2 := (componentBoundaryStubBranchIndex G C (qL C)).property
        change G.degree (qL C).val.2 ≠ 2 at hne2
        have htwo := hmin (qL C).val.2
        simp only [branchingVertices, Finset.mem_coe,
          Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
    let bR : (branchingVertices G : Set (Fin k)) :=
      ⟨(qR C).val.2, by
        have hne2 := (componentBoundaryStubBranchIndex G C (qR C)).property
        change G.degree (qR C).val.2 ≠ 2 at hne2
        have htwo := hmin (qR C).val.2
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
        _ = Sym2.map Subtype.val s(bL,bR) := by simp [bL, bR]
    rw [hendBranch, Sym2.map_mk, profilePathEdgeFactor_mk]
    rfl
  rw [hcomp]
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => n C + 1
    | Sum.inr _ => 0
  have hedgeLength (a : KernelEdgeLabel G) :
      edgeLength a = kernelEdgeInternalLength G a := by
    cases a with
    | inl C =>
        simp only [edgeLength, kernelEdgeInternalLength,
          Nat.card_eq_fintype_card]
        exact (hn C).symm
    | inr d => rfl
  have hlength (a : Fin (3 * ell)) :
      edgeLength (eE.symm a) = (D.profile.length a).val := by
    calc
      edgeLength (eE.symm a) =
          kernelEdgeInternalLength G (eE.symm a) :=
        hedgeLength (eE.symm a)
      _ = D.recoveredKernelEdgeLength K a := rfl
      _ = (D.profile.length a).val :=
        D.recoveredKernelEdgeLength_eq K a
  have hendpoint (a : Fin (3 * ell)) :
      Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc (eE.symm a)) =
        K.graph.endpoints a := by
    exact D.recoveredKernelBranchEndpoints_exact K hmin hacyc a
  let actualFactor : KernelEdgeLabel G → ℂ := fun a ↦
    profilePathEdgeFactor M tau x (edgeLength a)
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc a))
  have hsplit :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        (∏ C : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C)) *
        ∏ d : {a // a ∈ directBranchEdges G},
          actualFactor (Sum.inr d) := by
    change
      (∏ a : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor a) = _
    exact Fintype.prod_sum_type actualFactor
  have hrelabel :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        ∏ j : Fin (3 * ell),
          profilePathEdgeFactor M tau x (D.profile.length j).val
            (K.graph.endpoints j) := by
    exact Fintype.prod_equiv eE actualFactor
      (fun j : Fin (3 * ell) ↦
        profilePathEdgeFactor M tau x (D.profile.length j).val
          (K.graph.endpoints j))
      (fun a ↦ by
        dsimp only [actualFactor]
        have hlen : edgeLength a =
            (D.profile.length (eE a)).val := by
          simpa only [Equiv.symm_apply_apply] using hlength (eE a)
        have hend :
            Sym2.map eB (kernelBranchEndpoints G hmin hacyc a) =
              K.graph.endpoints (eE a) := by
          simpa only [Equiv.symm_apply_apply] using hendpoint (eE a)
        rw [hlen, hend])
  have hordered :
      (∏ j : Fin (3 * ell),
          profilePathEdgeFactor M tau x (D.profile.length j).val
            (K.graph.endpoints j)) =
        ∏ j : Fin (3 * ell),
          profilePathEdgeCoefficient M tau
            (x (cubicKernelOrderedEndpoints K.graph j).1)
            (x (cubicKernelOrderedEndpoints K.graph j).2)
            (D.profile.length j).val := by
    apply Finset.prod_congr rfl
    intro j _
    rw [← cubicKernelOrderedEndpoints_mk K.graph j,
      profilePathEdgeFactor_mk]
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
          profilePathEdgeFactor M tau x 0
            (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
              (Sum.inr d : KernelEdgeLabel G))) := by
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
  rw [← hordered, ← hrelabel, hsplit, hdirect]
  dsimp only [actualFactor, edgeLength]
  ring

end PerronWright.GraphCore
