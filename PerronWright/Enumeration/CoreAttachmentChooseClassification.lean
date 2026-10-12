import PerronWright.Enumeration.CoreAttachmentCoreIdentity
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Explicit original-label multiplicity for core/forest assemblies

The outer size index is a literal antidiagonal pair `(q,n)` with `q+n=k`.
For fixed admissible ordered core `H : SimpleGraph (Fin q)` and fixed genuine
attachment datum `D`, an original `Fin k` labelling is obtained by choosing the
actual `q`-element core-label subset.  The inverse sends a graph to its literal
greatest-two-core finset.  Thus no representative of an abstract fibre is
chosen, and the multiplicity is exactly `Nat.choose k q`.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-- The ordered core conditions needed by the exact attachment
classification at graph surplus `ell`: connected, internally a two-core,
and with exactly `q + ell` edges. -/
def IsAdmissibleAttachmentCore (q ell : ℕ)
    (H : SimpleGraph (Fin q)) : Prop :=
  H.Connected ∧ IsTwoCore H Set.univ ∧
    H.edgeFinset.card = q + ell

/-- The finite set of admissible ordered cores of size `q`. -/
def admissibleAttachmentCores (q ell : ℕ) :
    Finset (SimpleGraph (Fin q)) := by
  classical
  exact Finset.univ.filter (IsAdmissibleAttachmentCore q ell)

@[simp] theorem mem_admissibleAttachmentCores
    {q ell : ℕ} {H : SimpleGraph (Fin q)} :
    H ∈ admissibleAttachmentCores q ell ↔
      IsAdmissibleAttachmentCore q ell H := by
  classical
  simp [admissibleAttachmentCores]

/-- The finite antidiagonal of possible `(core size, off-core size)` pairs. -/
def coreOffSizePairs (k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.antidiagonal k

@[simp] theorem mem_coreOffSizePairs {k : ℕ} {p : ℕ × ℕ} :
    p ∈ coreOffSizePairs k ↔ p.1 + p.2 = k := by
  simp [coreOffSizePairs]

/-- A genuine ordered-core/attachment datum at a fixed size pair. -/
def AdmissibleCoreAttachmentDatum (ell q n : ℕ) :=
  {H : SimpleGraph (Fin q) // IsAdmissibleAttachmentCore q ell H} ×
    LabelledCoreForestAttachment q n

/-- The exact finite global data index before restoring the original labels. -/
def AntidiagonalCoreAttachmentDatum (k ell : ℕ) :=
  Σ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    AdmissibleCoreAttachmentDatum ell p.1.1 p.1.2

/-- Actual choices of the `q` original labels occupied by the core. -/
def CoreLabelSubset (k q : ℕ) :=
  {C : Finset (Fin k) //
    C ∈ (Finset.univ : Finset (Fin k)).powersetCard q}

noncomputable instance coreLabelSubsetFintype (k q : ℕ) :
    Fintype (CoreLabelSubset k q) := by
  unfold CoreLabelSubset
  infer_instance

theorem CoreLabelSubset.card_eq
    {k q : ℕ} (C : CoreLabelSubset k q) : C.1.card = q :=
  (Finset.mem_powersetCard.mp C.2).2

theorem CoreLabelSubset.compl_card_eq
    {k q n : ℕ} (hp : q + n = k) (C : CoreLabelSubset k q) :
    C.1ᶜ.card = n := by
  rw [Finset.card_compl, Fintype.card_fin, C.card_eq]
  omega

/-- There are exactly `choose k q` possible original core-label subsets. -/
theorem card_coreLabelSubset (k q : ℕ) :
    Fintype.card (CoreLabelSubset k q) = Nat.choose k q := by
  classical
  let s : Finset (Finset (Fin k)) :=
    (Finset.univ : Finset (Fin k)).powersetCard q
  have hfilter :
      (Finset.univ.filter (fun C : Finset (Fin k) => C ∈ s)) = s := by
    ext C
    simp
  calc
    Fintype.card (CoreLabelSubset k q) =
        (Finset.univ.filter
          (fun C : Finset (Fin k) => C ∈ s)).card := by
      exact @Fintype.card_subtype (Finset (Fin k)) inferInstance
        (fun C => C ∈ s) (coreLabelSubsetFintype k q) inferInstance
    _ = s.card := by rw [hfilter]
    _ = Nat.choose k q := by
      simp only [s, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]

/-- The increasing relabelling which places a chosen original core subset on
the left and its complement on the right. -/
def coreLabelEquiv
    {k q n : ℕ} (hp : q + n = k) (C : CoreLabelSubset k q) :
    Fin q ⊕ Fin n ≃ Fin k :=
  finSumEquivOfFinset C.card_eq (C.compl_card_eq hp)

/-- Put an ordered core/attachment assembly back on the original `Fin k`
labels, using the increasing orders on the chosen subset and its complement. -/
def assembleGraphOnCoreSubset
    {k q n : ℕ} (hp : q + n = k) (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    SimpleGraph (Fin k) :=
  (D.assembleGraph H).comap (coreLabelEquiv hp C).symm

/-- Relabelling an assembly to a chosen core subset makes that subset exactly
the literal greatest two-core. -/
theorem greatestTwoCore_assembleGraphOnCoreSubset
    {k q n : ℕ} (hp : q + n = k) (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsTwoCore H Set.univ) :
    greatestTwoCore (assembleGraphOnCoreSubset hp C H D) =
      (C.1 : Set (Fin k)) := by
  classical
  let A : SimpleGraph (Fin q ⊕ Fin n) := D.assembleGraph H
  let e : Fin q ⊕ Fin n ≃ Fin k := coreLabelEquiv hp C
  change greatestTwoCore (A.comap e.symm) = (C.1 : Set (Fin k))
  have hA : greatestTwoCore A =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n) :=
    LabelledCoreForestAttachment.greatestTwoCore_assembleGraph_eq_range_inl
      H D hH
  ext x
  rw [mem_greatestTwoCore_comap_equiv_iff e.symm A x, hA]
  constructor
  · rintro ⟨i, hi⟩
    have hx : x = e (Sum.inl i) := by
      calc
        x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e (Sum.inl i) := (congrArg e hi).symm
    rw [hx]
    simpa only [e, coreLabelEquiv, finSumEquivOfFinset_inl,
      Finset.mem_coe] using
      Finset.orderEmbOfFin_mem C.1 C.card_eq i
  · intro hx
    have hxrange : x ∈ Set.range (C.1.orderEmbOfFin C.card_eq) := by
      rw [C.1.range_orderEmbOfFin C.card_eq]
      exact hx
    obtain ⟨i, hi⟩ := hxrange
    refine ⟨i, ?_⟩
    have hei : e (Sum.inl i) = x := by
      simpa only [e, coreLabelEquiv, finSumEquivOfFinset_inl] using hi
    calc
      Sum.inl i = e.symm (e (Sum.inl i)) :=
        (e.symm_apply_apply _).symm
      _ = e.symm x := congrArg e.symm hei

/-- The finite version of the preceding literal-core identity. -/
theorem canonicalCoreFinset_assembleGraphOnCoreSubset
    {k q n : ℕ} (hp : q + n = k) (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsTwoCore H Set.univ) :
    (greatestTwoCore (assembleGraphOnCoreSubset hp C H D)).toFinset = C.1 := by
  classical
  ext x
  simpa using Set.ext_iff.mp
    (greatestTwoCore_assembleGraphOnCoreSubset hp C H D hH) x

/-- The concrete original-label fibre generated by a fixed ordered core and
fixed attachment datum.  Membership carries only the assertion that the graph
is the explicit assembly on some actual core-label subset. -/
def OriginalLabelCoreAttachmentFiber
    {k q n : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :=
  {G : SimpleGraph (Fin k) //
    ∃ C : CoreLabelSubset k q, G = assembleGraphOnCoreSubset hp C H D}

noncomputable instance originalLabelCoreAttachmentFiberFintype
    {k q n : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n) :
    Fintype (OriginalLabelCoreAttachmentFiber hp H D) := by
  unfold OriginalLabelCoreAttachmentFiber
  infer_instance

/-- The inverse from the concrete original-label fibre is canonical: take the
literal greatest-two-core finset.  The existential fibre witness is used only
to prove its cardinality, never to choose the returned subset. -/
def originalLabelFiberCoreSubset
    {k q n : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsTwoCore H Set.univ)
    (G : OriginalLabelCoreAttachmentFiber hp H D) :
    CoreLabelSubset k q := by
  classical
  refine ⟨(greatestTwoCore G.1).toFinset, ?_⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _, ?_⟩
  obtain ⟨C, hG⟩ := G.2
  rw [hG, canonicalCoreFinset_assembleGraphOnCoreSubset hp C H D hH]
  exact C.card_eq

@[simp] theorem originalLabelFiberCoreSubset_assemble
    {k q n : ℕ} (hp : q + n = k)
    (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsTwoCore H Set.univ) :
    originalLabelFiberCoreSubset hp H D hH
        (⟨assembleGraphOnCoreSubset hp C H D, ⟨C, rfl⟩⟩ :
          OriginalLabelCoreAttachmentFiber hp H D) = C := by
  apply Subtype.ext
  exact canonicalCoreFinset_assembleGraphOnCoreSubset hp C H D hH

/-- Exact finite equivalence: for fixed admissible `(H,D)`, the original
label fibre is the type of `q`-subsets of `Fin k`.  Both maps are explicit. -/
def coreLabelSubsetEquivOriginalLabelFiber
    {k q n ell : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsAdmissibleAttachmentCore q ell H) :
    CoreLabelSubset k q ≃ OriginalLabelCoreAttachmentFiber hp H D where
  toFun C := ⟨assembleGraphOnCoreSubset hp C H D, ⟨C, rfl⟩⟩
  invFun := originalLabelFiberCoreSubset hp H D hH.2.1
  left_inv C := originalLabelFiberCoreSubset_assemble hp C H D hH.2.1
  right_inv G := by
    obtain ⟨C, hGC⟩ := G.2
    have hG : G =
        (⟨assembleGraphOnCoreSubset hp C H D, ⟨C, rfl⟩⟩ :
          OriginalLabelCoreAttachmentFiber hp H D) := by
      apply Subtype.ext
      exact hGC
    rw [hG, originalLabelFiberCoreSubset_assemble]

/-- Hence the relabelling multiplicity is the required binomial coefficient,
with no automorphism or factorial correction. -/
theorem card_originalLabelCoreAttachmentFiber
    {k q n ell : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsAdmissibleAttachmentCore q ell H) :
    Fintype.card (OriginalLabelCoreAttachmentFiber hp H D) =
      Nat.choose k q := by
  calc
    Fintype.card (OriginalLabelCoreAttachmentFiber hp H D) =
        Fintype.card (CoreLabelSubset k q) :=
      (Fintype.card_congr
        (coreLabelSubsetEquivOriginalLabelFiber hp H D hH)).symm
    _ = Nat.choose k q := card_coreLabelSubset k q

/-- Every member of a fixed admissible fibre is one of the original connected
fixed-surplus graphs. -/
theorem assembleGraphOnCoreSubset_mem_fixedSurplusGraphs
    {k q n ell : ℕ} (hp : q + n = k)
    (C : CoreLabelSubset k q)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsAdmissibleAttachmentCore q ell H) :
    assembleGraphOnCoreSubset hp C H D ∈ fixedSurplusGraphs k ell := by
  classical
  have hHedge : H.edgeFinset.card = q + ell := hH.2.2
  let A : SimpleGraph (Fin q ⊕ Fin n) := D.assembleGraph H
  let e : Fin q ⊕ Fin n ≃ Fin k := coreLabelEquiv hp C
  let φ : A.comap e.symm ≃g A := SimpleGraph.Iso.comap e.symm A
  have hconnA : A.Connected :=
    @LabelledCoreForestAttachment.assembleGraph_connected q n H D
      hH.1 hH.1.nonempty
  have hconn : (A.comap e.symm).Connected := φ.connected_iff.mpr hconnA
  have hedge : (A.comap e.symm).edgeFinset.card + 1 =
      Fintype.card (Fin k) + (ell + 1) := by
    rw [φ.card_edgeFinset_eq]
    change (D.assembleGraph H).edgeFinset.card + 1 = _
    rw [D.assembleGraph_edge_count H]
    simp only [Fintype.card_fin]
    omega
  simpa only [fixedSurplusGraphs, Finset.mem_filter, Finset.mem_univ,
    true_and, assembleGraphOnCoreSubset, A, e] using ⟨hconn, hedge⟩

theorem OriginalLabelCoreAttachmentFiber.mem_fixedSurplusGraphs
    {k q n ell : ℕ} (hp : q + n = k)
    (H : SimpleGraph (Fin q)) (D : LabelledCoreForestAttachment q n)
    (hH : IsAdmissibleAttachmentCore q ell H)
    (G : OriginalLabelCoreAttachmentFiber hp H D) :
    G.1 ∈ fixedSurplusGraphs k ell := by
  obtain ⟨C, hG⟩ := G.2
  rw [hG]
  exact assembleGraphOnCoreSubset_mem_fixedSurplusGraphs hp C H D hH

/-!
The global classification layer can now use the genuine forward construction on
each `G ∈ fixedSurplusGraphs k ell` to produce its unique antidiagonal
`(q,n)`, admissible ordered core `H`, attachment datum `D`, and literal core
subset `C`.  The theorem above supplies the exact fibre cardinal
`Nat.choose k q`; no abstract fibre cardinal remains in that sum.
-/

end GraphCore
end PerronWright
