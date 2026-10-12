import PerronWright.Enumeration.CoreAttachmentArbitrary
import PerronWright.Enumeration.CorePathIntegral

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Annealed graph weight on an arbitrary finite vertex type.  This is the
coordinate-free companion of `CompactBJRModel.graphWeight`. -/
def finiteGraphWeight (M : CompactBJRModel S) (t : ℝ)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact ∫ x : V → S, finiteGraphWeightIntegrand M t G x
    ∂Measure.pi (fun _ : V => M.mu)

/-- The arbitrary-finite-type definition specializes definitionally to the
paper's labelled `Fin k` graph weight. -/
theorem finiteGraphWeight_fin_eq
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) :
    finiteGraphWeight M t G = M.graphWeight t G := by
  classical
  unfold finiteGraphWeight CompactBJRModel.graphWeight
  apply integral_congr_ae
  filter_upwards [] with x
  exact finiteGraphWeightIntegrand_fin_eq M t G x

/-- Annealed graph weight is invariant under an actual finite graph
isomorphism; the proof explicitly reindexes the iid product type law. -/
theorem finiteGraphWeight_iso
    (M : CompactBJRModel S) (t : ℝ)
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V)
    (H : SimpleGraph W)
    (e : G ≃g H) :
    finiteGraphWeight M t G = finiteGraphWeight M t H := by
  classical
  unfold finiteGraphWeight
  rw [integral_pi_reindex M.mu e.toEquiv]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (finiteGraphWeightIntegrand_iso M t H G e.symm x).symm

/-- The deterministic core/off-core split preserves the literal annealed
weight of the original labelled graph. -/
theorem finiteGraphWeight_splitGraph_eq_graphWeight
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj] :
    finiteGraphWeight M t (greatestTwoCoreSplitGraph G) =
      M.graphWeight t G := by
  rw [finiteGraphWeight_iso M t
    (greatestTwoCoreSplitGraph G) G (greatestTwoCoreSplitIso G)]
  exact finiteGraphWeight_fin_eq M t G

end GraphCore
end PerronWright
