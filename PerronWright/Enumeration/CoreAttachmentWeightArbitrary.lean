import PerronWright.Enumeration.CoreAttachmentWeightFactor

/-! # Arbitrary-label core attachment weight factorization -/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The canonical forward core/forest decomposition of an arbitrarily
labelled connected positive-surplus graph preserves its annealed weight
exactly.  This is the bridge from the coordinate-free split theorem back to
the paper's `Fin k` convention. -/
theorem finiteGraphWeight_forwardArbitraryCoreAttachment
    (M : CompactBJRModel S)
    {k ell : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = k + ell) :
    let K := greatestTwoCoreSplitGraph G
    letI : DecidableRel K.Adj := fun i j ↦ Classical.propDecidable (K.Adj i j)
    let D := forwardSplitCoreAttachment K
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
      (greatestTwoCore_splitGraph_eq_range_inl G)
    finiteGraphWeight M 1
        (D.assembleGraph
          (K.comap
            (Sum.inl : Fin (greatestTwoCoreSize G) →
              Fin (greatestTwoCoreSize G) ⊕
                Fin (greatestTwoCoreComplementSize G)))) =
      M.graphWeight 1 G := by
  dsimp only
  rw [assembleGraph_forwardArbitraryCoreAttachment G hconn hell hs]
  exact finiteGraphWeight_splitGraph_eq_graphWeight M 1 G

/-- The graph weight of an arbitrarily labelled connected positive-surplus
graph is the fixed-core integral for its *canonical* greatest-two-core split
and the genuine attachment datum extracted by `forwardSplitCoreAttachment`.

This is the direct bridge from the original `Fin k` graph to the literal
fixed-attachment factorisation; in particular, it assumes no separate
classification bijection. -/
theorem graphWeight_eq_integral_forwardArbitraryCoreAttachment
    (M : CompactBJRModel S)
    {k ell : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = k + ell) :
    let K := greatestTwoCoreSplitGraph G
    letI : DecidableRel K.Adj := fun i j ↦ Classical.propDecidable (K.Adj i j)
    let D := forwardSplitCoreAttachment K
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
      (greatestTwoCore_splitGraph_eq_range_inl G)
    M.graphWeight 1 G =
      ∫ roots : Fin (greatestTwoCoreSize G) → S,
        M.graphWeightIntegrand 1
            (K.comap
              (Sum.inl : Fin (greatestTwoCoreSize G) →
                Fin (greatestTwoCoreSize G) ⊕
                  Fin (greatestTwoCoreComplementSize G))) roots *
          M.labelledCoreForestAttachmentWeight roots D
        ∂Measure.pi
          (fun _ : Fin (greatestTwoCoreSize G) ↦ M.mu) := by
  dsimp only
  rw [← finiteGraphWeight_forwardArbitraryCoreAttachment M G hconn hell hs]
  exact finiteGraphWeight_assembleGraph M _ _

end GraphCore
end PerronWright
