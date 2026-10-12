import PerronWright.Enumeration.GraphCore
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

noncomputable section

namespace PerronWright.GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sole edge incident to a leaf, with an exact finite-set identity
for the edges left after removing that vertex's incidences. -/
theorem leaf_unique_incident_edge {v : V} (hv : G.degree v = 1) :
    ∃ e : Sym2 V, e ∈ G.edgeFinset ∧
      (G.deleteIncidenceSet v).edgeFinset = G.edgeFinset.erase e := by
  have hcard : (G.incidenceFinset v).card = 1 := by
    simpa only [G.card_incidenceFinset_eq_degree] using hv
  obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hcard
  have hie : e ∈ G.incidenceFinset v := by rw [heq]; simp
  have he : e ∈ G.edgeFinset := G.incidenceFinset_subset v hie
  refine ⟨e, he, ?_⟩
  rw [G.edgeFinset_deleteIncidenceSet_eq_sdiff, heq,
    Finset.sdiff_singleton_eq_erase]

/-- Identifies the unique incident edge with the actual neighbor's
unordered endpoint pair. -/
theorem leaf_incident_edge_eq_pair {v w : V} (hv : G.degree v = 1)
    (hvw : G.Adj v w) :
    (G.deleteIncidenceSet v).edgeFinset = G.edgeFinset.erase s(v,w) := by
  have hcard : (G.incidenceFinset v).card = 1 := by
    simpa only [G.card_incidenceFinset_eq_degree] using hv
  obtain ⟨e, heq⟩ := Finset.card_eq_one.mp hcard
  have hpair : s(v,w) ∈ G.incidenceFinset v := by
    rw [G.mem_incidenceFinset]
    exact G.mk'_mem_incidenceSet_left_iff.mpr hvw
  have he : e = s(v,w) := by
    have : s(v,w) = e := by simpa [heq] using hpair
    exact this.symm
  rw [G.edgeFinset_deleteIncidenceSet_eq_sdiff, heq, he,
    Finset.sdiff_singleton_eq_erase]

/-- Exact factorization of arbitrary commutative vertex and edge weights
under deletion of a degree-one vertex.  No asymptotic approximation is used. -/
theorem leaf_weight_product_split {R : Type*} [CommMonoid R]
    {v : V} (hv : G.degree v = 1) (a : V → R) (b : Sym2 V → R) :
    ∃ e : Sym2 V, e ∈ G.edgeFinset ∧
      (∏ x : V, a x) * (∏ f ∈ G.edgeFinset, b f) =
      (a v * b e) *
        ((∏ x ∈ (Finset.univ.erase v), a x) *
          (∏ f ∈ (G.deleteIncidenceSet v).edgeFinset, b f)) := by
  obtain ⟨e, he, hdel⟩ := leaf_unique_incident_edge G hv
  refine ⟨e, he, ?_⟩
  have hvert := Finset.mul_prod_erase (Finset.univ : Finset V) a (Finset.mem_univ v)
  have hedge := Finset.mul_prod_erase G.edgeFinset b he
  rw [hdel, ← hvert, ← hedge]
  ac_rfl

/-- The same product identity with the edge explicitly identified as
the pair consisting of the leaf and its unique neighbor. -/
theorem leaf_weight_product_split_at_neighbor {R : Type*} [CommMonoid R]
    {v w : V} (hv : G.degree v = 1) (hvw : G.Adj v w)
    (a : V → R) (b : Sym2 V → R) :
    (∏ x : V, a x) * (∏ f ∈ G.edgeFinset, b f) =
      (a v * b s(v,w)) *
        ((∏ x ∈ (Finset.univ.erase v), a x) *
          (∏ f ∈ (G.deleteIncidenceSet v).edgeFinset, b f)) := by
  have he : s(v,w) ∈ G.edgeFinset := by simpa using hvw
  have hdel := leaf_incident_edge_eq_pair G hv hvw
  have hvert := Finset.mul_prod_erase (Finset.univ : Finset V) a (Finset.mem_univ v)
  have hedge := Finset.mul_prod_erase G.edgeFinset b he
  rw [hdel, ← hvert, ← hedge]
  ac_rfl

open scoped Classical in
/-- Specialization to the manuscript's exact connected-graph integrand.
The still-present type vector `x` will be integrated only after applying
this literal product decomposition and the product-law factorization. -/
theorem leaf_graphWeightIntegrand_split
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (H : SimpleGraph (Fin k))
    (x : Fin k → S) {v : Fin k} (hv : H.degree v = 1) :
    ∃ e : Sym2 (Fin k), e ∈ H.edgeFinset ∧
      M.graphWeightIntegrand t H x =
        (Real.exp (-t * M.degreeFunction (x v)) * M.edgeFactor t x e) *
          ((∏ i ∈ (Finset.univ.erase v),
              Real.exp (-t * M.degreeFunction (x i))) *
            (∏ f ∈ (H.deleteIncidenceSet v).edgeFinset,
              M.edgeFactor t x f)) := by
  simpa [CompactBJRModel.graphWeightIntegrand, SimpleGraph.edgeFinset] using
    (leaf_weight_product_split H hv
      (fun i => Real.exp (-t * M.degreeFunction (x i)))
      (M.edgeFactor t x))

open scoped Classical in
/-- The exact manuscript integrand factors at a leaf as the exponential
vertex factor times the actual kernel edge factor. -/
theorem leaf_graphWeightIntegrand_split_at_neighbor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (H : SimpleGraph (Fin k))
    (x : Fin k → S) {v w : Fin k}
    (hv : H.degree v = 1) (hvw : H.Adj v w) :
    M.graphWeightIntegrand t H x =
      (Real.exp (-t * M.degreeFunction (x v)) *
        (t * M.kernel (x v) (x w))) *
          ((∏ i ∈ (Finset.univ.erase v),
              Real.exp (-t * M.degreeFunction (x i))) *
            (∏ f ∈ (H.deleteIncidenceSet v).edgeFinset,
              M.edgeFactor t x f)) := by
  simpa only [CompactBJRModel.graphWeightIntegrand,
    CompactBJRModel.edgeFactor_mk] using
    (leaf_weight_product_split_at_neighbor H hv hvw
      (fun i => Real.exp (-t * M.degreeFunction (x i)))
      (M.edgeFactor t x))

end PerronWright.GraphCore
