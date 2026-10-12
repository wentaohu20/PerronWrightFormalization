import PerronWright.Enumeration.LeafTransfer

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory

open scoped Classical in
theorem map_survivor_graph_eq_delete {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    ((H.comap v.succAbove).map v.succAboveEmb) =
      H.deleteIncidenceSet v := by
  ext a b
  rw [SimpleGraph.map_adj, SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · rintro ⟨i, j, hij, rfl, rfl⟩
    exact ⟨hij, Fin.succAbove_ne v i, Fin.succAbove_ne v j⟩
  · rintro ⟨hab, ha, hb⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
    exact ⟨i, j, hab, rfl, rfl⟩

open scoped Classical in
/-- The deleted-leaf residual is exactly the integrand of the graph
induced on the remaining `Fin n` labels. -/
theorem leaf_residual_eq_smaller_graph_integrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1))
    (y₀ : S) (z : Fin n → S) :
    ((∏ i ∈ Finset.univ.erase v,
        Real.exp (-t * M.degreeFunction
          ((Fin.insertNth v y₀ z : Fin (n + 1) → S) i))) *
      (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
        M.edgeFactor t (Fin.insertNth v y₀ z) e)) =
      M.graphWeightIntegrand t (H.comap v.succAbove) z := by
  unfold CompactBJRModel.graphWeightIntegrand
  congr 1
  · rw [Fin.univ_succAbove n v]
    simp [Finset.prod_map, Fin.succAboveEmb]
  · have heq : (H.deleteIncidenceSet v).edgeFinset =
        ((H.comap v.succAbove).map v.succAboveEmb).edgeFinset := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [map_survivor_graph_eq_delete H v]
    rw [heq]
    have hmap :
        ((H.comap v.succAbove).map v.succAboveEmb).edgeFinset =
          (H.comap v.succAbove).edgeFinset.map v.succAboveEmb.sym2Map := by
      have hmap₀ := SimpleGraph.edgeFinset_map v.succAboveEmb
        (H.comap v.succAbove)
      ext e
      rw [← hmap₀]
      simp only [SimpleGraph.mem_edgeFinset]
    rw [hmap]
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e _
    induction e using Sym2.inductionOn with
    | _ i j =>
        change M.edgeFactor t (Fin.insertNth v y₀ z)
            (Sym2.map v.succAbove s(i, j)) = M.edgeFactor t z s(i, j)
        rw [Sym2.map_mk]
        simp only [CompactBJRModel.edgeFactor_mk,
          Fin.insertNth_apply_succAbove]

/-- The graph weight of a smaller labelled graph with one type-dependent
mark at vertex `j`; the ordinary graph weight is the case `mark = 1`. -/
def graphWeightWithMark
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : Fin n) (mark : S → ℝ) : ℝ :=
  ∫ z : Fin n → S, mark (z j) * M.graphWeightIntegrand t G z
    ∂Measure.pi (fun _ : Fin n => M.mu)

open scoped Classical in
/-- Exact one-step pruning transfer: integrating a leaf of an actual
labelled graph creates one response mark at its neighbor in the
smaller induced graph.  No auxiliary type value is required. -/
theorem graphWeight_leaf_transfer_induced
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (j : Fin n)
    (hv : H.degree v = 1) (hvw : H.Adj v (v.succAbove j)) :
    M.graphWeight t H =
      graphWeightWithMark M t (H.comap v.succAbove) j (leafResponse M t) := by
  rw [graphWeight_fubini_survivors_first M t H v]
  unfold graphWeightWithMark
  congr 1
  funext z
  have hpoint (y : S) :
      M.graphWeightIntegrand t H (Fin.insertNth v y z) =
      (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (z j))) *
        M.graphWeightIntegrand t (H.comap v.succAbove) z := by
    rw [leaf_graphWeightIntegrand_split_at_neighbor M t H
      (Fin.insertNth v y z) hv hvw]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    congr 1
    exact leaf_residual_eq_smaller_graph_integrand M t H v y z
  calc
    (∫ y : S, M.graphWeightIntegrand t H (Fin.insertNth v y z) ∂M.mu) =
      ∫ y : S, (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (z j))) *
        M.graphWeightIntegrand t (H.comap v.succAbove) z ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = leafResponse M t (z j) *
        M.graphWeightIntegrand t (H.comap v.succAbove) z := by
      rw [integral_mul_const]
      rfl

open scoped Classical in
/-- Any specified neighbor of a deleted leaf has a canonical coordinate
among the surviving labels, so the transfer identity needs no extra
mathematical hypothesis about the smaller graph. -/
theorem graphWeight_leaf_transfer_induced_exists
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) {v w : Fin (n + 1)}
    (hv : H.degree v = 1) (hvw : H.Adj v w) :
    ∃ j : Fin n, v.succAbove j = w ∧
      M.graphWeight t H =
        graphWeightWithMark M t (H.comap v.succAbove) j (leafResponse M t) := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (H.ne_of_adj hvw).symm
  exact ⟨j, hj, graphWeight_leaf_transfer_induced M t H v j hv (hj ▸ hvw)⟩

/-- A unit mark recovers the ordinary annealed graph weight exactly. -/
theorem graphWeightWithMark_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : Fin n) :
    graphWeightWithMark M t G j (fun _ => 1) = M.graphWeight t G := by
  unfold graphWeightWithMark CompactBJRModel.graphWeight
  simp only [one_mul]


end PerronWright.GraphCore
