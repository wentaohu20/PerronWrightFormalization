import PerronWright.Enumeration.LeafFactor
import PerronWright.Enumeration.FieldWeight
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges remaining after incidence deletion are *exactly* the edges
of the induced graph on the surviving labels, mapped back to the original
unordered-pair type.  This holds without a leaf assumption. -/
theorem map_edgeFinset_induce_compl_eq_delete (v : V) :
    (G.induce ({v}ᶜ : Set V)).edgeFinset.map
        (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V))).sym2Map =
      (G.deleteIncidenceSet v).edgeFinset := by
  rw [G.map_edgeFinset_induce, G.edgeFinset_deleteIncidenceSet_eq_filter]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sym2_iff,
    Set.mem_toFinset, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨he, by
      intro hv
      exact h v hv rfl⟩
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    intro a ha hae
    subst a
    exact h ha

/-- Reindex the residual vertex product onto the actual surviving subtype. -/
theorem prod_surviving_vertices {R : Type*} [CommMonoid R]
    (v : V) (a : V → R) :
    (∏ i ∈ (Finset.univ.erase v), a i) =
      ∏ i : ({v}ᶜ : Set V), a i.val := by
  exact Finset.prod_subtype (Finset.univ.erase v) (by intro x; simp) a

/-- Reindex the residual edge product onto the actual induced graph. -/
theorem prod_surviving_edges {R : Type*} [CommMonoid R]
    (v : V) (b : Sym2 V → R) :
    (∏ e ∈ (G.deleteIncidenceSet v).edgeFinset, b e) =
      ∏ e ∈ (G.induce ({v}ᶜ : Set V)).edgeFinset,
        b ((Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V))).sym2Map e) := by
  rw [← map_edgeFinset_induce_compl_eq_delete G v]
  exact Finset.prod_map _ _ _

/-- Fubini for the *actual* annealed fixed-graph weight after singling out
one labelled vertex.  The graph integrand is integrable because the type
space is compact and its exact finite product is continuous. -/
theorem graphWeight_fubini_at_vertex
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    M.graphWeight t H =
      ∫ y : S, ∫ z : Fin n → S,
        M.graphWeightIntegrand t H (Fin.insertNth v y z)
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hf : Integrable (M.graphWeightIntegrand t H)
      (Measure.pi (fun _ : Fin (n + 1) => M.mu)) :=
    M.graphWeightIntegrand_integrable t H
  have hprod : Integrable
      (fun p : S × (Fin n → S) => M.graphWeightIntegrand t H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    M.graphWeight t H =
        ∫ p : S × (Fin n → S),
          M.graphWeightIntegrand t H (e.symm p)
            ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
              exact (hmp.symm.integral_comp' (M.graphWeightIntegrand t H)).symm
    _ = ∫ y : S, ∫ z : Fin n → S,
          M.graphWeightIntegrand t H (Fin.insertNth v y z)
            ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
      rw [integral_prod _ hprod]
      rfl

open scoped Classical in
/-- Fubini combined with the *exact* leaf factor of the actual graph
weight.  The remaining products are subsequently reindexed by the two
preceding lemmas. -/
theorem graphWeight_leaf_fubini
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) {v w : Fin (n + 1)}
    (hv : H.degree v = 1) (hvw : H.Adj v w) :
    M.graphWeight t H =
      ∫ y : S, ∫ z : Fin n → S,
        (Real.exp (-t * M.degreeFunction y) *
          (t * M.kernel y (((Fin.insertNth v y z : Fin (n + 1) → S)) w))) *
          ((∏ i ∈ (Finset.univ.erase v),
              Real.exp (-t * M.degreeFunction
                ((Fin.insertNth v y z : Fin (n + 1) → S) i))) *
            (∏ f ∈ (H.deleteIncidenceSet v).edgeFinset,
              M.edgeFactor t (Fin.insertNth v y z) f))
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
  rw [graphWeight_fubini_at_vertex M t H v]
  congr 1
  funext y
  congr 1
  funext z
  simpa only [Fin.insertNth_apply_same] using
    (leaf_graphWeightIntegrand_split_at_neighbor M t H
      (Fin.insertNth v y z) hv hvw)

end PerronWright.GraphCore
