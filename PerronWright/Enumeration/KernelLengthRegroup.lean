import PerronWright.Enumeration.NormalizedKernelIntegral

/-!
# Bounded kernel/length data and coarse exact fibres

This stage is finite and entirely combinatorial.  It normalizes only the
terminal two-core and deliberately retains the literal `pruneAll` marks in
the innermost graph sum.  No decorated integral or marked-path analysis is
used here.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- A bounded normalized endpoint table together with the actual number of
internal degree-two vertices carried by every suppressed edge. -/
abbrev BoundedKernelLengthDatum (k ell : ℕ) :=
  Σ nv : Fin (2 * ell + 1),
    Σ ne : Fin (3 * ell + 1),
      (Fin ne.val → Sym2 (Fin nv.val)) × (Fin ne.val → Fin (k + 1))

instance boundedKernelLengthDatumFintype (k ell : ℕ) :
    Fintype (BoundedKernelLengthDatum k ell) := by
  unfold BoundedKernelLengthDatum
  infer_instance

/-- The literal normalized path-kernel integral represented by one bounded
kernel/length datum. -/
def boundedKernelLengthIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k ell : ℕ}
    (D : BoundedKernelLengthDatum k ell) : ℝ :=
  ∫ x : Fin D.1.val → S,
    (∏ i : Fin D.1.val,
        Real.exp (-t * M.degreeFunction (x i))) *
      ∏ j : Fin D.2.1.val,
        pathKernelEdgeFactor M t (D.2.2.2 j).val x (D.2.2.1 j)
    ∂Measure.pi (fun _ : Fin D.1.val => M.mu)

/-- The actual admissible labelled two-cores at original size `k`. -/
abbrev AdmissibleCoreIndex (k ell : ℕ) :=
  {I : CoreIndex k // I ∈ admissibleCoreIndices k ell}

set_option linter.style.haveILetI false in
/-- Canonical finite kernel/length data of an actual admissible two-core.
The endpoint relabellings are the concrete `equivFin` relabellings already
used by `normalizedBoundedKernelShape`; a path-component edge carries its
actual component cardinality, while a direct edge has length zero. -/
def admissibleCoreKernelLengthDatum {k ell : ℕ} (hell : 0 < ell)
    (I : AdmissibleCoreIndex k ell) : BoundedKernelLengthDatum k ell := by
  classical
  let H : SimpleGraph (Fin I.1.1.val) := I.1.2
  have hI : H.Connected ∧ (∀ v, 2 ≤ H.degree v) ∧
      H.edgeFinset.card = I.1.1.val + ell ∧
      (branchingVertices H).card ≤ 2 * ell := by
    simpa only [H, admissibleCoreIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using I.2
  let hconn : H.Connected := hI.1
  let hmin : ∀ v, 2 ≤ H.degree v := hI.2.1
  let hs : H.edgeFinset.card = Fintype.card (Fin I.1.1.val) + ell := by
    simpa only [Fintype.card_fin] using hI.2.2.1
  let hacyc : (twoGraph H).IsAcyclic :=
    degreeTwo_induced_isAcyclic H hconn hmin hell hs
  let B := branchingVertices H
  let E := KernelEdgeLabel H
  have hb : B.card ≤ 2 * ell := hI.2.2.2
  have he : Nat.card E ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus H hconn hmin hell hs
  let nv : Fin (2 * ell + 1) := ⟨B.card, by omega⟩
  let ne : Fin (3 * ell + 1) := ⟨Nat.card E, by omega⟩
  letI : Fintype (twoGraph H).ConnectedComponent := Fintype.ofFinite _
  letI : ∀ C : (twoGraph H).ConnectedComponent, Fintype C :=
    fun C => Fintype.ofFinite C
  letI : Fintype {e : Sym2 (Fin I.1.1.val) // e ∈ directBranchEdges H} :=
    FinsetCoe.fintype (directBranchEdges H)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  let eB : B ≃ Fin nv.val := Finset.equivFin B
  let eE : E ≃ Fin ne.val := by
    apply Fintype.equivFinOfCardEq
    simp only [ne, Nat.card_eq_fintype_card]
  let table : Fin ne.val → Sym2 (Fin nv.val) := fun j =>
    Sym2.map eB (kernelBranchEndpoints H hmin hacyc (eE.symm j))
  let edgeLength : E → ℕ
    | Sum.inl C => Fintype.card C
    | Sum.inr _ => 0
  have hcomponentCard (C : (twoGraph H).ConnectedComponent) :
      Fintype.card C ≤ I.1.1.val := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective
        (fun x : C => x.val.val)
        (fun x y hxy => Subtype.ext (Subtype.ext hxy)))
  have hcoreCard : I.1.1.val ≤ k := by omega
  have hedgeLength (e : E) : edgeLength e ≤ k := by
    cases e with
    | inl C => exact (hcomponentCard C).trans hcoreCard
    | inr d =>
        simp only [edgeLength]
        exact Nat.zero_le _
  let length : Fin ne.val → Fin (k + 1) := fun j =>
    ⟨edgeLength (eE.symm j),
      Nat.lt_succ_of_le (hedgeLength (eE.symm j))⟩
  exact ⟨nv, ne, table, length⟩

/-- The contribution of all original labelled graphs whose deterministic
pruning has the given labelled two-core.  The exact terminal marks retain
all attached-tree information at this coarse stage. -/
def admissibleCoreAttachedTreeContribution
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ)
    (I : AdmissibleCoreIndex k ell) : ℝ :=
  ∑ G ∈ (fixedSurplusGraphs k ell).filter (fun G => coreIndex G = I.1),
    markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
      ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1))

/-- Exact finite regrouping by bounded normalized shape and actual path
lengths.  The inner term remains the literal attached-tree contribution, so
this theorem makes no classification or analytic approximation claim. -/
theorem connectedWeight_eq_kernelLength_attachedTree_fibers
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell) :
    M.connectedWeight t k (ell + 1) =
      ∑ D : BoundedKernelLengthDatum k ell,
        ∑ I : AdmissibleCoreIndex k ell,
          if admissibleCoreKernelLengthDatum hell I = D then
            admissibleCoreAttachedTreeContribution M t k ell I
          else 0 := by
  classical
  rw [connectedWeight_eq_admissible_core_fibers M t k ell]
  calc
    (∑ I ∈ admissibleCoreIndices k ell,
        ∑ G ∈ (fixedSurplusGraphs k ell).filter (fun G => coreIndex G = I),
          markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
            ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1))) =
        ∑ I : AdmissibleCoreIndex k ell,
          admissibleCoreAttachedTreeContribution M t k ell I := by
      exact Finset.sum_subtype (admissibleCoreIndices k ell)
        (fun _ => Iff.rfl)
        (fun I =>
          ∑ G ∈ (fixedSurplusGraphs k ell).filter (fun G => coreIndex G = I),
            markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
              ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)))
    _ = ∑ D : BoundedKernelLengthDatum k ell,
          ∑ I : AdmissibleCoreIndex k ell,
            if admissibleCoreKernelLengthDatum hell I = D then
              admissibleCoreAttachedTreeContribution M t k ell I
            else 0 := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro I
      simp

end PerronWright.GraphCore
