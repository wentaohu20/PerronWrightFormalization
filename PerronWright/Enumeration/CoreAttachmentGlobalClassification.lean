import PerronWright.Enumeration.CoreAttachmentChooseClassification

/-!
# Deterministic global core/attachment classification

This is the next layer after the explicit `Nat.choose` fibre calculation.
The forward map assembles a literal core-label subset, an admissible ordered
core, and genuine rooted-forest attachment data.  The inverse is completely
deterministic: it takes the literal greatest-two-core subset, uses the
increasing core/complement split, and then applies
`forwardSplitCoreAttachment`.

No inverse is selected from an unspecified fibre.  Global disjointness is
proved first, and the left-inverse law is then deduced from that injectivity
and exact forward recovery.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-- The actual finite type underlying `fixedSurplusGraphs`.  The longer name
avoids collision with a similarly named downstream regrouping abbreviation. -/
abbrev AttachmentFixedSurplusGraph (k ell : ℕ) :=
  {G : SimpleGraph (Fin k) // G ∈ fixedSurplusGraphs k ell}

theorem attachmentFixedSurplusGraph_spec
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    G.1.Connected ∧ G.1.edgeFinset.card + 1 = k + (ell + 1) := by
  simpa only [fixedSurplusGraphs, Finset.mem_filter, Finset.mem_univ,
    true_and, Fintype.card_fin] using G.2

/-- At fixed sizes, the full explicitly labelled datum consists of the
actual original core-label subset and the ordered `(H,D)` datum. -/
def SubsetLabelledCoreAttachmentDatumAt
    (k ell q n : ℕ) :=
  CoreLabelSubset k q × AdmissibleCoreAttachmentDatum ell q n

noncomputable instance admissibleCoreAttachmentDatumFintype
    (ell q n : ℕ) :
    Fintype (AdmissibleCoreAttachmentDatum ell q n) := by
  unfold AdmissibleCoreAttachmentDatum
  infer_instance

noncomputable instance subsetLabelledCoreAttachmentDatumAtFintype
    (k ell q n : ℕ) :
    Fintype (SubsetLabelledCoreAttachmentDatumAt k ell q n) := by
  unfold SubsetLabelledCoreAttachmentDatumAt
  infer_instance

/-- The explicit global index: an antidiagonal size pair followed by an
actual core-label subset, an admissible ordered core, and an attachment. -/
def AntidiagonalSubsetLabelledCoreAttachmentDatum
    (k ell : ℕ) :=
  Σ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    SubsetLabelledCoreAttachmentDatumAt k ell p.1.1 p.1.2

noncomputable instance antidiagonalSubsetLabelledCoreAttachmentDatumFintype
    (k ell : ℕ) :
    Fintype (AntidiagonalSubsetLabelledCoreAttachmentDatum k ell) := by
  unfold AntidiagonalSubsetLabelledCoreAttachmentDatum
  infer_instance

/-- Assembly at one fixed antidiagonal size pair. -/
def subsetLabelledCoreAttachmentAssembly
    {k ell q n : ℕ} (hp : q + n = k)
    (X : SubsetLabelledCoreAttachmentDatumAt k ell q n) :
    SimpleGraph (Fin k) :=
  assembleGraphOnCoreSubset hp X.1 X.2.1.1 X.2.2

theorem subsetLabelledCoreAttachmentAssembly_mem_fixedSurplusGraphs
    {k ell q n : ℕ} (hp : q + n = k)
    (X : SubsetLabelledCoreAttachmentDatumAt k ell q n) :
    subsetLabelledCoreAttachmentAssembly hp X ∈
      fixedSurplusGraphs k ell :=
  assembleGraphOnCoreSubset_mem_fixedSurplusGraphs
    hp X.1 X.2.1.1 X.2.2 X.2.1.2

/-- At fixed `(q,n)`, equality of subset-labelled assemblies recovers all
three pieces `C`, `H`, and `D`.  First the new core-identity theorem recovers
`C`; after pulling both graphs back along the common increasing split,
`assembleGraph_injective` recovers `H` and `D`. -/
theorem subsetLabelledCoreAttachmentAssembly_injective
    {k ell q n : ℕ} (hp : q + n = k) :
    Function.Injective
      (subsetLabelledCoreAttachmentAssembly
        (ell := ell) hp) := by
  intro X Y hgraph
  rcases X with ⟨C, ⟨⟨H, hH⟩, D⟩⟩
  rcases Y with ⟨C', ⟨⟨H', hH'⟩, D'⟩⟩
  change assembleGraphOnCoreSubset hp C H D =
    assembleGraphOnCoreSubset hp C' H' D' at hgraph
  have hgreatest := congrArg greatestTwoCore hgraph
  rw [greatestTwoCore_assembleGraphOnCoreSubset
        hp C H D hH.2.1,
      greatestTwoCore_assembleGraphOnCoreSubset
        hp C' H' D' hH'.2.1] at hgreatest
  have hC : C = C' := by
    apply Subtype.ext
    exact Finset.coe_injective hgreatest
  subst C'
  let e : Fin q ⊕ Fin n ≃ Fin k := coreLabelEquiv hp C
  have hpull := congrArg
    (fun G : SimpleGraph (Fin k) => G.comap e) hgraph
  have hassembly : D.assembleGraph H = D'.assembleGraph H' := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    have hadj := (congrArg
      (fun G : SimpleGraph (Fin q ⊕ Fin n) => G.Adj u v) hpull).to_iff
    simpa only [assembleGraphOnCoreSubset, e, SimpleGraph.comap_adj,
      Equiv.symm_apply_apply] using hadj
  obtain ⟨hcore, hattachment⟩ :=
    LabelledCoreForestAttachment.assembleGraph_injective hassembly
  subst H'
  subst D'
  rfl

/-- Global subset-labelled assembly, now bundled with the proof that its
value belongs to the original fixed-surplus graph set. -/
def antidiagonalSubsetLabelledCoreAttachmentAssembly
    {k ell : ℕ}
    (X : AntidiagonalSubsetLabelledCoreAttachmentDatum k ell) :
    AttachmentFixedSurplusGraph k ell := by
  let hp : X.1.1.1 + X.1.1.2 = k :=
    mem_coreOffSizePairs.mp X.1.2
  exact ⟨subsetLabelledCoreAttachmentAssembly hp X.2,
    subsetLabelledCoreAttachmentAssembly_mem_fixedSurplusGraphs hp X.2⟩

/-- A useful finite-graph fact for the deterministic inverse: the induced
greatest two-core of a connected positive-surplus `Fin` graph is connected.
It follows from maximal leaf pruning and its canonical core isomorphism. -/
theorem greatestTwoCore_induce_connected_fin
    {k r : ℕ} (G : SimpleGraph (Fin k))
    (hconn : G.Connected) (hr : 0 < r)
    (hs : G.edgeFinset.card + 1 = k + r) :
    (G.induce (greatestTwoCore G)).Connected := by
  let p := LeafPruning.pruneAll k G
  have hterminal : p.terminalGraph.Connected := p.terminal_connected hconn
  have hs' : G.edgeFinset.card + 1 = Fintype.card (Fin k) + r := by
    simpa only [Fintype.card_fin] using hs
  have hiso : p.terminalGraph ≃g
      G.induce (greatestTwoCore G) := by
    exact p.terminalCoreIso hconn hr hs'
  exact hiso.connected_iff.mp hterminal

/-- If the literal greatest two-core of a split graph is its left summand,
then the graph induced on the ordered left labels is internally a two-core. -/
theorem isTwoCore_comap_inl_of_greatestTwoCore_eq_range_inl
    {q n : ℕ} (G : SimpleGraph (Fin q ⊕ Fin n))
    [DecidableRel G.Adj]
    (hcore : greatestTwoCore G =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) :
    IsTwoCore
      (G.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)) Set.univ := by
  have htwo : IsTwoCore G
      (Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n)) := by
    rw [← hcore]
    exact isTwoCore_greatest G
  intro i _
  obtain ⟨w, hw, z, hz, hwz, hiw, hiz⟩ :=
    htwo (Sum.inl i) ⟨i, rfl⟩
  obtain ⟨a, rfl⟩ := hw
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a, Set.mem_univ a, b, Set.mem_univ b,
    fun hab => hwz (congrArg Sum.inl hab), hiw, hiz⟩

/-- The canonical core/off-core sizes really lie on the size antidiagonal. -/
theorem canonicalCoreOffSize_eq
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    greatestTwoCoreSize G.1 +
      greatestTwoCoreComplementSize G.1 = k := by
  classical
  have hcard := Fintype.card_congr (greatestTwoCoreSplitEquiv G.1)
  simpa only [Fintype.card_sum, Fintype.card_fin] using hcard

/-- The deterministic antidiagonal index of a fixed-surplus graph. -/
def canonicalCoreOffSizePair
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    {p : ℕ × ℕ // p ∈ coreOffSizePairs k} :=
  ⟨(greatestTwoCoreSize G.1,
      greatestTwoCoreComplementSize G.1),
    mem_coreOffSizePairs.mpr (canonicalCoreOffSize_eq G)⟩

/-- The actual original labels of the canonical greatest two-core. -/
def canonicalCoreLabelSubset
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    CoreLabelSubset k (greatestTwoCoreSize G.1) := by
  classical
  refine ⟨(greatestTwoCore G.1).toFinset, ?_⟩
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩

/-- The ordered core extracted after the deterministic increasing split. -/
def canonicalSplitCore
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    SimpleGraph (Fin (greatestTwoCoreSize G.1)) :=
  (greatestTwoCoreSplitGraph G.1).comap
    (Sum.inl : Fin (greatestTwoCoreSize G.1) →
      Fin (greatestTwoCoreSize G.1) ⊕
        Fin (greatestTwoCoreComplementSize G.1))

/-- Genuine deterministic attachment data extracted from the increasing
split of an original fixed-surplus graph. -/
def canonicalSplitAttachment
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    LabelledCoreForestAttachment
      (greatestTwoCoreSize G.1)
      (greatestTwoCoreComplementSize G.1) := by
  classical
  let K := greatestTwoCoreSplitGraph G.1
  letI : DecidableRel K.Adj := fun i j =>
    Classical.propDecidable (K.Adj i j)
  have hspec := attachmentFixedSurplusGraph_spec G
  exact forwardSplitCoreAttachment K
    ((greatestTwoCoreSplitIso G.1).connected_iff.mpr hspec.1)
    (Nat.succ_pos ell)
    (by
      rw [(greatestTwoCoreSplitIso G.1).card_edgeFinset_eq]
      have hcard :
          Fintype.card
            (Fin (greatestTwoCoreSize G.1) ⊕
              Fin (greatestTwoCoreComplementSize G.1)) = k := by
        simpa using Fintype.card_congr (greatestTwoCoreSplitEquiv G.1)
      rw [hcard]
      exact hspec.2)
    (greatestTwoCore_splitGraph_eq_range_inl G.1)

set_option linter.style.haveILetI false in
/-- The core extracted by the deterministic split is admissible. -/
theorem canonicalSplitCore_admissible
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    IsAdmissibleAttachmentCore
      (greatestTwoCoreSize G.1) ell (canonicalSplitCore G) := by
  classical
  let q := greatestTwoCoreSize G.1
  let n := greatestTwoCoreComplementSize G.1
  let e : Fin q ⊕ Fin n ≃ Fin k := greatestTwoCoreSplitEquiv G.1
  let K : SimpleGraph (Fin q ⊕ Fin n) := greatestTwoCoreSplitGraph G.1
  letI : DecidableRel K.Adj := fun i j =>
    Classical.propDecidable (K.Adj i j)
  have hspec := attachmentFixedSurplusGraph_spec G
  have hKconn : K.Connected :=
    (greatestTwoCoreSplitIso G.1).connected_iff.mpr hspec.1
  have hKsurplus : K.edgeFinset.card + 1 =
      Fintype.card (Fin q ⊕ Fin n) + (ell + 1) := by
    rw [(greatestTwoCoreSplitIso G.1).card_edgeFinset_eq]
    have hcard : Fintype.card (Fin q ⊕ Fin n) = k := by
      simpa only [q, n, Fintype.card_fin] using
        Fintype.card_congr (greatestTwoCoreSplitEquiv G.1)
    rw [hcard]
    exact hspec.2
  have hcore : greatestTwoCore K =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n) := by
    simpa only [K, q, n] using
      greatestTwoCore_splitGraph_eq_range_inl G.1
  have hInducedG :
      (G.1.induce (greatestTwoCore G.1)).Connected :=
    greatestTwoCore_induce_connected_fin G.1 hspec.1
      (Nat.succ_pos ell) hspec.2
  let coreIso : K.induce (greatestTwoCore K) ≃g
      G.1.induce (greatestTwoCore G.1) := by
    simpa only [K, greatestTwoCoreSplitGraph, e] using
      greatestTwoCoreInduceIsoEquiv e G.1
  have hInducedK : (K.induce (greatestTwoCore K)).Connected :=
    coreIso.connected_iff.mpr hInducedG
  have hconn :
      (K.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)).Connected :=
    (splitCoreIso K hcore).connected_iff.mpr hInducedK
  have htwo : IsTwoCore
      (K.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)) Set.univ :=
    isTwoCore_comap_inl_of_greatestTwoCore_eq_range_inl K hcore
  have hcoreSurplus := greatestTwoCore_surplus_finite K hKconn
    (Nat.succ_pos ell) hKsurplus
  have hcoreCard : Fintype.card (greatestTwoCore K) = q := by
    have hc := Fintype.card_congr (splitCoreEquiv K hcore)
    simpa only [Fintype.card_fin] using hc.symm
  have hedgePlus :
      (K.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)).edgeFinset.card + 1 =
        q + (ell + 1) := by
    calc
      (K.comap
          (Sum.inl : Fin q → Fin q ⊕ Fin n)).edgeFinset.card + 1 =
          (K.induce (greatestTwoCore K)).edgeFinset.card + 1 := by
            rw [(splitCoreIso K hcore).card_edgeFinset_eq]
      _ = Fintype.card (greatestTwoCore K) + (ell + 1) := hcoreSurplus
      _ = q + (ell + 1) := by rw [hcoreCard]
  have hedge :
      (K.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)).edgeFinset.card =
        q + ell := by
    omega
  simpa only [canonicalSplitCore, K, q, n] using
    (show IsAdmissibleAttachmentCore q ell
        (K.comap (Sum.inl : Fin q → Fin q ⊕ Fin n)) from
      ⟨hconn, htwo, hedge⟩)

/-- The fully deterministic datum extracted from an original graph. -/
def canonicalAntidiagonalCoreAttachmentDatum
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    AntidiagonalSubsetLabelledCoreAttachmentDatum k ell :=
  ⟨canonicalCoreOffSizePair G,
    (canonicalCoreLabelSubset G,
      (⟨canonicalSplitCore G, canonicalSplitCore_admissible G⟩,
        canonicalSplitAttachment G))⟩

/-- On the canonical literal core subset, the general increasing split is
the already-existing deterministic greatest-two-core split. -/
theorem coreLabelEquiv_canonicalCoreLabelSubset
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    coreLabelEquiv
      (mem_coreOffSizePairs.mp (canonicalCoreOffSizePair G).2)
      (canonicalCoreLabelSubset G) =
        greatestTwoCoreSplitEquiv G.1 := by
  rfl

/-- Exact forward recovery for the deterministic inverse: assembling the
canonical datum on its literal original core labels returns the original
graph. -/
theorem antidiagonalAssembly_canonicalDatum
    {k ell : ℕ} (G : AttachmentFixedSurplusGraph k ell) :
    antidiagonalSubsetLabelledCoreAttachmentAssembly
      (canonicalAntidiagonalCoreAttachmentDatum G) = G := by
  classical
  apply Subtype.ext
  have hspec := attachmentFixedSurplusGraph_spec G
  have hforward := assembleGraph_forwardArbitraryCoreAttachment
    G.1 hspec.1 (Nat.succ_pos ell) hspec.2
  dsimp only at hforward
  change (canonicalSplitAttachment G).assembleGraph
      (canonicalSplitCore G) = greatestTwoCoreSplitGraph G.1 at hforward
  change ((canonicalSplitAttachment G).assembleGraph
      (canonicalSplitCore G)).comap
        (greatestTwoCoreSplitEquiv G.1).symm = G.1
  rw [hforward]
  unfold greatestTwoCoreSplitGraph
  ext x y
  simp

/-- The global assembly is injective, so the antidiagonal fibres are
pairwise disjoint.  Equality of graphs first forces equality of core sizes;
the antidiagonal equation then forces equality of off-core sizes, reducing
to the fixed-size injectivity theorem above. -/
theorem antidiagonalSubsetLabelledCoreAttachmentAssembly_injective
    {k ell : ℕ} :
    Function.Injective
      (antidiagonalSubsetLabelledCoreAttachmentAssembly
        (k := k) (ell := ell)) := by
  intro X Y hXY
  rcases X with ⟨p, X⟩
  rcases Y with ⟨p', Y⟩
  let hp : p.1.1 + p.1.2 = k := mem_coreOffSizePairs.mp p.2
  let hp' : p'.1.1 + p'.1.2 = k := mem_coreOffSizePairs.mp p'.2
  have hgraph := congrArg
    (fun A : AttachmentFixedSurplusGraph k ell => A.1) hXY
  change subsetLabelledCoreAttachmentAssembly hp X =
    subsetLabelledCoreAttachmentAssembly hp' Y at hgraph
  have hcard := congrArg
    (fun G : SimpleGraph (Fin k) =>
      (greatestTwoCore G).toFinset.card) hgraph
  change
    (greatestTwoCore
      (assembleGraphOnCoreSubset hp X.1 X.2.1.1 X.2.2)).toFinset.card =
    (greatestTwoCore
      (assembleGraphOnCoreSubset hp' Y.1 Y.2.1.1 Y.2.2)).toFinset.card
      at hcard
  rw [canonicalCoreFinset_assembleGraphOnCoreSubset
        hp X.1 X.2.1.1 X.2.2 X.2.1.2.2.1,
      canonicalCoreFinset_assembleGraphOnCoreSubset
        hp' Y.1 Y.2.1.1 Y.2.2 Y.2.1.2.2.1,
      X.1.card_eq, Y.1.card_eq] at hcard
  have hq : p.1.1 = p'.1.1 := hcard
  have hn : p.1.2 = p'.1.2 := by
    have hsizes := mem_coreOffSizePairs.mp p.2
    have hsizes' := mem_coreOffSizePairs.mp p'.2
    omega
  have hpval : p.1 = p'.1 := Prod.ext hq hn
  have hpeq : p = p' := Subtype.ext hpval
  subst p'
  have hgraph' :
      subsetLabelledCoreAttachmentAssembly
          (mem_coreOffSizePairs.mp p.2) X =
        subsetLabelledCoreAttachmentAssembly
          (mem_coreOffSizePairs.mp p.2) Y := by
    simpa only [hp, hp'] using hgraph
  have hdata : X = Y :=
    subsetLabelledCoreAttachmentAssembly_injective
      (mem_coreOffSizePairs.mp p.2) hgraph'
  subst Y
  rfl

/-- The desired genuine global classification equivalence.  Its inverse is
the deterministic forward construction above; no choice of representatives
from abstract fibres occurs. -/
def antidiagonalCoreAttachmentEquivFixedSurplusGraphs
    (k ell : ℕ) :
    AntidiagonalSubsetLabelledCoreAttachmentDatum k ell ≃
      AttachmentFixedSurplusGraph k ell where
  toFun := antidiagonalSubsetLabelledCoreAttachmentAssembly
  invFun := canonicalAntidiagonalCoreAttachmentDatum
  left_inv X := by
    apply antidiagonalSubsetLabelledCoreAttachmentAssembly_injective
    exact antidiagonalAssembly_canonicalDatum
      (antidiagonalSubsetLabelledCoreAttachmentAssembly X)
  right_inv := antidiagonalAssembly_canonicalDatum

theorem antidiagonalSubsetLabelledCoreAttachmentAssembly_surjective
    {k ell : ℕ} :
    Function.Surjective
      (antidiagonalSubsetLabelledCoreAttachmentAssembly
        (k := k) (ell := ell)) :=
  (antidiagonalCoreAttachmentEquivFixedSurplusGraphs k ell).surjective

/-!
This equivalence is the exact coverage/disjointness interface needed for the
next sum theorem.  Expanding the sigma and the first product field gives

`sum_(q+n=k) sum_H sum_D sum_(C in powersetCard q)`.

The fixed-fibre equivalence in `CoreAttachmentChooseClassification` supplies
the exact `Nat.choose k q` cardinal needed to collapse the last sum.  The
corresponding weighted global-sum reindexing is a subsequent theorem, not a
claim of this module.
-/

end GraphCore
end PerronWright
