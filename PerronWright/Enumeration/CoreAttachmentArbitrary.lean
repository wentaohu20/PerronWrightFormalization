import PerronWright.Enumeration.CoreAttachmentSplitForward

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-- Number of vertices in the literal greatest two-core. -/
abbrev greatestTwoCoreSize {k : ℕ} (G : SimpleGraph (Fin k))
    [DecidableRel G.Adj] : ℕ :=
  (greatestTwoCore G).toFinset.card

/-- Number of vertices outside the literal greatest two-core. -/
abbrev greatestTwoCoreComplementSize {k : ℕ} (G : SimpleGraph (Fin k))
    [DecidableRel G.Adj] : ℕ :=
  (greatestTwoCore G).toFinsetᶜ.card

/-- The deterministic increasing relabelling that places the greatest
two-core on the left and its complement on the right. -/
def greatestTwoCoreSplitEquiv {k : ℕ} (G : SimpleGraph (Fin k))
    [DecidableRel G.Adj] :
    Fin (greatestTwoCoreSize G) ⊕
        Fin (greatestTwoCoreComplementSize G) ≃ Fin k :=
  finSumEquivOfFinset rfl rfl

/-- The original graph after the deterministic core/off-core relabelling. -/
def greatestTwoCoreSplitGraph {k : ℕ} (G : SimpleGraph (Fin k))
    [DecidableRel G.Adj] :
    SimpleGraph
      (Fin (greatestTwoCoreSize G) ⊕
        Fin (greatestTwoCoreComplementSize G)) :=
  G.comap (greatestTwoCoreSplitEquiv G)

theorem greatestTwoCoreSplitEquiv_inl_mem
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (i : Fin (greatestTwoCoreSize G)) :
    greatestTwoCoreSplitEquiv G (Sum.inl i) ∈ greatestTwoCore G := by
  apply Set.mem_toFinset.mp
  rw [greatestTwoCoreSplitEquiv, finSumEquivOfFinset_inl]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem greatestTwoCoreSplitEquiv_inr_not_mem
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (i : Fin (greatestTwoCoreComplementSize G)) :
    greatestTwoCoreSplitEquiv G (Sum.inr i) ∉ greatestTwoCore G := by
  intro hi
  have hi' : greatestTwoCoreSplitEquiv G (Sum.inr i) ∈
      (greatestTwoCore G).toFinset := Set.mem_toFinset.mpr hi
  rw [greatestTwoCoreSplitEquiv, finSumEquivOfFinset_inr] at hi'
  have hcompl :
      (greatestTwoCore G).toFinsetᶜ.orderEmbOfFin rfl i ∈
        (greatestTwoCore G).toFinsetᶜ :=
    Finset.orderEmbOfFin_mem _ _ _
  exact (Finset.mem_compl.mp hcompl) hi'

/-- In the deterministic split coordinates, the greatest two-core is
literally the range of the left injection. -/
theorem greatestTwoCore_splitGraph_eq_range_inl
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj] :
    greatestTwoCore (greatestTwoCoreSplitGraph G) =
      Set.range
        (Sum.inl : Fin (greatestTwoCoreSize G) →
          Fin (greatestTwoCoreSize G) ⊕
            Fin (greatestTwoCoreComplementSize G)) := by
  ext x
  change x ∈ greatestTwoCore
      (G.comap (greatestTwoCoreSplitEquiv G)) ↔ x ∈ Set.range Sum.inl
  rw [mem_greatestTwoCore_comap_equiv_iff]
  rcases x with i | j
  · constructor
    · intro _
      exact ⟨i, rfl⟩
    · intro _
      exact greatestTwoCoreSplitEquiv_inl_mem G i
  · constructor
    · intro h
      exact (greatestTwoCoreSplitEquiv_inr_not_mem G j h).elim
    · rintro ⟨i, h⟩
      exact False.elim (Sum.inl_ne_inr h)

/-- The deterministic split relabelling is a graph isomorphism back to the
original graph. -/
def greatestTwoCoreSplitIso {k : ℕ} (G : SimpleGraph (Fin k))
    [DecidableRel G.Adj] : greatestTwoCoreSplitGraph G ≃g G :=
  SimpleGraph.Iso.comap (greatestTwoCoreSplitEquiv G) G

/-- A connected positive-surplus graph with arbitrary original labels is
literally recovered after deterministic splitting, genuine forward
classification, and assembly. -/
theorem assembleGraph_forwardArbitraryCoreAttachment
    {k ell : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = k + ell) :
    let K := greatestTwoCoreSplitGraph G
    letI : DecidableRel K.Adj := fun i j ↦ Classical.propDecidable (K.Adj i j)
    (forwardSplitCoreAttachment K
        ((greatestTwoCoreSplitIso G).connected_iff.mpr hconn)
        hell
        (by
          rw [(greatestTwoCoreSplitIso G).card_edgeFinset_eq]
          have hcard :
              Fintype.card
                (Fin (greatestTwoCoreSize G) ⊕
                  Fin (greatestTwoCoreComplementSize G)) = k := by
            simpa using Fintype.card_congr (greatestTwoCoreSplitEquiv G)
          rw [hcard]
          exact hs)
        (greatestTwoCore_splitGraph_eq_range_inl G)).assembleGraph
      (K.comap
        (Sum.inl : Fin (greatestTwoCoreSize G) →
          Fin (greatestTwoCoreSize G) ⊕
            Fin (greatestTwoCoreComplementSize G))) = K := by
  dsimp only
  apply assembleGraph_forwardSplitCoreAttachment

end GraphCore
end PerronWright
