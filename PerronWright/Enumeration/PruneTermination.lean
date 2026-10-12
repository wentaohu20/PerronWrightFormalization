import PerronWright.Enumeration.GraphCore

noncomputable section

namespace PerronWright.GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One literal step of leaf pruning on a finite vertex label set.  The
graph at the current step is the induced graph on the surviving labels. -/
def LeafPruneStep (s t : Finset V) : Prop :=
  ∃ v : (s : Set V), (G.induce (s : Set V)).degree v = 1 ∧
    t = s.erase v.val

omit [Fintype V] in
/-- Every leaf-pruning step strictly lowers the number of surviving labels. -/
theorem leafPruneStep_card_lt {s t : Finset V} (h : LeafPruneStep G s t) :
    t.card < s.card := by
  obtain ⟨v, -, rfl⟩ := h
  exact Finset.card_erase_lt_of_mem v.property

omit [Fintype V] in
/-- No infinite sequence of leaf-pruning steps exists: the next-state
relation is well founded by the literal count of surviving vertices. -/
theorem leafPruneStep_wellFounded :
    WellFounded (fun t s : Finset V => LeafPruneStep G s t) := by
  apply Subrelation.wf _ (measure Finset.card).wf
  intro t s h
  exact leafPruneStep_card_lt G h

end PerronWright.GraphCore
