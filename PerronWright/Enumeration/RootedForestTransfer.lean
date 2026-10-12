import PerronWright.Enumeration.LeafIterate

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory

/-- The unmarked exponential vertex factor of the actual compact-type
graph weight, bundled so that successive pruning marks stay continuous. -/
def leafVertexFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : C(S, ℝ) :=
  ⟨fun x => Real.exp (-t * M.degreeFunction x), by fun_prop⟩

/-- The exact response obtained when a leaf already carries a continuous
mark from previously pruned descendants. -/
def leafMarkUpdate
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (f : C(S, ℝ)) : C(S, ℝ) :=
  t • M.kernel.action M.mu (leafVertexFactor M t * f)

theorem leafMarkUpdate_apply
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (f : C(S, ℝ)) (a : S) :
    leafMarkUpdate M t f a =
      ∫ y : S, f y *
        (Real.exp (-t * M.degreeFunction y) * (t * M.kernel y a)) ∂M.mu := by
  simp only [leafMarkUpdate, ContinuousMap.smul_apply, smul_eq_mul,
    ContinuousKernel.action_apply, ContinuousMap.mul_apply, leafVertexFactor]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change t * (M.kernel a y *
      (Real.exp (-t * M.degreeFunction y) * f y)) =
    f y * (Real.exp (-t * M.degreeFunction y) * (t * M.kernel y a))
  rw [M.kernel.symmetric a y]
  ring

/-- Exact graph integrand with one continuous factor attached to each
labelled vertex. -/
def markedGraphIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) (marks : Fin k → C(S, ℝ))
    (x : Fin k → S) : ℝ :=
  (∏ i : Fin k, marks i (x i)) * M.graphWeightIntegrand t G x

/-- Annealed weight carrying arbitrary continuous vertex marks. -/
def markedGraphWeight
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) (marks : Fin k → C(S, ℝ)) : ℝ :=
  ∫ x : Fin k → S, markedGraphIntegrand M t G marks x
    ∂Measure.pi (fun _ : Fin k => M.mu)

theorem markedGraphIntegrand_continuous
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) (marks : Fin k → C(S, ℝ)) :
    Continuous (markedGraphIntegrand M t G marks) := by
  unfold markedGraphIntegrand
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact (marks i).continuous.comp (continuous_apply i)
  · exact M.graphWeightIntegrand_continuous t G

theorem markedGraphIntegrand_integrable
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) (marks : Fin k → C(S, ℝ)) :
    Integrable (markedGraphIntegrand M t G marks)
      (Measure.pi (fun _ : Fin k => M.mu)) :=
  (markedGraphIntegrand_continuous M t G marks).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- Fubini for a graph with actual continuous marks; the deleted vertex
is integrated first, so its mark can be absorbed into the neighbor. -/
theorem markedGraphWeight_fubini_survivors_first
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (marks : Fin (n + 1) → C(S, ℝ)) (v : Fin (n + 1)) :
    markedGraphWeight M t H marks =
      ∫ z : Fin n → S, ∫ y : S,
        markedGraphIntegrand M t H marks (Fin.insertNth v y z)
          ∂M.mu ∂Measure.pi (fun _ : Fin n => M.mu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hf := markedGraphIntegrand_integrable M t H marks
  have hprod : Integrable
      (fun p : S × (Fin n → S) => markedGraphIntegrand M t H marks (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    markedGraphWeight M t H marks =
        ∫ p : S × (Fin n → S), markedGraphIntegrand M t H marks (e.symm p)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
            exact (hmp.symm.integral_comp' (markedGraphIntegrand M t H marks)).symm
    _ = ∫ y : S, ∫ z : Fin n → S,
          markedGraphIntegrand M t H marks (Fin.insertNth v y z)
            ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
      rw [integral_prod _ hprod]
      rfl
    _ = ∫ z : Fin n → S, ∫ y : S,
          markedGraphIntegrand M t H marks (Fin.insertNth v y z)
            ∂M.mu ∂Measure.pi (fun _ : Fin n => M.mu) := by
      exact integral_integral_swap hprod

/-- Preserve every surviving mark and multiply the neighbor mark by the
response of the deleted leaf mark. -/
def descendMarks
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (marks : Fin (n + 1) → C(S, ℝ)) (v : Fin (n + 1))
    (j : Fin n) : Fin n → C(S, ℝ) :=
  Function.update (fun i => marks (v.succAbove i)) j
    (marks (v.succAbove j) * leafMarkUpdate M t (marks v))

open scoped Classical in
theorem descendMarks_product
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (marks : Fin (n + 1) → C(S, ℝ)) (v : Fin (n + 1))
    (j : Fin n) (z : Fin n → S) :
    (∏ i : Fin n, descendMarks M t marks v j i (z i)) =
      leafMarkUpdate M t (marks v) (z j) *
        (∏ i : Fin n, marks (v.succAbove i) (z i)) := by
  let f : Fin n → ℝ := fun i => marks (v.succAbove i) (z i)
  let L : ℝ := leafMarkUpdate M t (marks v) (z j)
  have heval (i : Fin n) :
      descendMarks M t marks v j i (z i) =
        Function.update f j (f j * L) i := by
    by_cases hi : i = j
    · subst i
      simp [descendMarks, f, L]
    · simp [descendMarks, f, L, hi]
  calc
    (∏ i : Fin n, descendMarks M t marks v j i (z i)) =
        ∏ i : Fin n, Function.update f j (f j * L) i := by
          apply Finset.prod_congr rfl
          intro i _
          exact heval i
    _ = (f j * L) * ∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, f i := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        Finset.prod_update_of_mem (Finset.mem_univ j) f (f j * L)
    _ = L * ∏ i : Fin n, f i := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
      ring

open scoped Classical in
theorem markedGraphIntegrand_leaf_split
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (marks : Fin (n + 1) → C(S, ℝ)) (v : Fin (n + 1)) (j : Fin n)
    (hv : H.degree v = 1) (hvw : H.Adj v (v.succAbove j))
    (y : S) (z : Fin n → S) :
    markedGraphIntegrand M t H marks (Fin.insertNth v y z) =
      (marks v y * (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (z j)))) *
      ((∏ i : Fin n, marks (v.succAbove i) (z i)) *
        M.graphWeightIntegrand t (H.comap v.succAbove) z) := by
  unfold markedGraphIntegrand
  rw [Fin.prod_univ_succAbove
    (fun i => marks i ((Fin.insertNth v y z : Fin (n + 1) → S) i)) v]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [leaf_graphWeightIntegrand_split_at_neighbor M t H
    (Fin.insertNth v y z) hv hvw]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [leaf_residual_eq_smaller_graph_integrand M t H v y z]
  ring

open scoped Classical in
/-- One exact pruning step with arbitrary continuous marks.  Any mark
already accumulated on the leaf is integrated and transferred to its
unique neighbor, while all other vertex marks and labels are preserved. -/
theorem markedGraphWeight_leaf_transfer
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (marks : Fin (n + 1) → C(S, ℝ)) (v : Fin (n + 1)) (j : Fin n)
    (hv : H.degree v = 1) (hvw : H.Adj v (v.succAbove j)) :
    markedGraphWeight M t H marks =
      markedGraphWeight M t (H.comap v.succAbove)
        (descendMarks M t marks v j) := by
  rw [markedGraphWeight_fubini_survivors_first M t H marks v]
  unfold markedGraphWeight
  congr 1
  funext z
  let R : ℝ :=
    (∏ i : Fin n, marks (v.succAbove i) (z i)) *
      M.graphWeightIntegrand t (H.comap v.succAbove) z
  calc
    (∫ y : S, markedGraphIntegrand M t H marks (Fin.insertNth v y z) ∂M.mu) =
        ∫ y : S,
          (marks v y * (Real.exp (-t * M.degreeFunction y) *
            (t * M.kernel y (z j)))) * R ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact markedGraphIntegrand_leaf_split M t H marks v j hv hvw y z
    _ = leafMarkUpdate M t (marks v) (z j) * R := by
      rw [integral_mul_const, leafMarkUpdate_apply]
    _ = markedGraphIntegrand M t (H.comap v.succAbove)
          (descendMarks M t marks v j) z := by
      unfold markedGraphIntegrand
      rw [descendMarks_product]
      ring

open scoped Classical in
/-- A concrete finite sequence of legitimate leaf deletions.  Every
step records the position of the deleted label and the surviving
coordinate of its unique neighbor.  The sequence may stop at an
induced core or at any earlier graph. -/
inductive LeafPruning : (k : ℕ) → SimpleGraph (Fin k) → Type where
  | done {k : ℕ} (G : SimpleGraph (Fin k))
      (hstop : ¬∃ v : Fin k, G.degree v = 1) : LeafPruning k G
  | step {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
      (v : Fin (n + 1)) (j : Fin n)
      (hv : H.degree v = 1) (hvw : H.Adj v (v.succAbove j))
      (tail : LeafPruning n (H.comap v.succAbove)) :
      LeafPruning (n + 1) H

namespace LeafPruning

def terminalCount : {k : ℕ} → {G : SimpleGraph (Fin k)} →
    LeafPruning k G → ℕ
  | k, _, .done _ _ => k
  | _, _, .step _ _ _ _ _ tail => tail.terminalCount

def terminalGraph : {k : ℕ} → {G : SimpleGraph (Fin k)} →
    (p : LeafPruning k G) → SimpleGraph (Fin p.terminalCount)
  | _, _, .done G _ => G
  | _, _, .step _ _ _ _ _ tail => tail.terminalGraph

def terminalLabels : {k : ℕ} → {G : SimpleGraph (Fin k)} →
    (p : LeafPruning k G) → Fin p.terminalCount ↪ Fin k
  | _, _, .done _ _ => Function.Embedding.refl _
  | _, _, .step _ v _ _ _ tail => tail.terminalLabels.trans v.succAboveEmb

def terminalMarks
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) :
    {k : ℕ} → {G : SimpleGraph (Fin k)} →
    (p : LeafPruning k G) →
    (Fin k → C(S, ℝ)) → Fin p.terminalCount → C(S, ℝ)
  | _, _, .done _ _, marks => marks
  | _, _, .step _ v j _ _ tail, marks =>
      tail.terminalMarks M t (descendMarks M t marks v j)

/-- A literal finite leaf-pruning algorithm.  It uses a leaf whenever
one exists and otherwise stops; recursion on the vertex count proves
termination directly. -/
noncomputable def pruneAll : (k : ℕ) →
    (G : SimpleGraph (Fin k)) → LeafPruning k G
  | 0, G => by
      classical
      have hstop : ¬∃ v : Fin 0, G.degree v = 1 := by
        rintro ⟨v, _⟩
        exact Fin.elim0 v
      exact .done G hstop
  | n + 1, G => by
      classical
      by_cases h : ∃ v : Fin (n + 1), G.degree v = 1
      · let v := Classical.choose h
        have hv : G.degree v = 1 := Classical.choose_spec h
        have hwExists : ∃ w : Fin (n + 1), G.Adj v w := by
          obtain ⟨w, hw, _⟩ :=
            (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hv
          exact ⟨w, hw⟩
        let w := Classical.choose hwExists
        have hw : G.Adj v w := Classical.choose_spec hwExists
        have hjExists := Fin.exists_succAbove_eq (G.ne_of_adj hw).symm
        let j := Classical.choose hjExists
        have hj : v.succAbove j = w := Classical.choose_spec hjExists
        exact .step G v j hv (hj ▸ hw)
          (pruneAll n (G.comap v.succAbove))
      · exact .done G h

end LeafPruning

open scoped Classical in
/-- Finite induction of the exact leaf transfer.  In particular, any
finite rooted forest whose nonroot vertices can be pruned in leaf order
reduces to its labelled induced root graph, with all tree responses
recorded in continuous marks on the surviving vertices. -/
theorem markedGraphWeight_leafPruning
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) (marks : Fin k → C(S, ℝ)) :
    markedGraphWeight M t G marks =
      markedGraphWeight M t p.terminalGraph
        (p.terminalMarks M t marks) := by
  induction p with
  | done G hstop => rfl
  | step H v j hv hvw tail ih =>
      exact (markedGraphWeight_leaf_transfer M t H marks v j hv hvw).trans
        (ih (descendMarks M t marks v j))

/-- The surviving labels are embedded back into the original labels;
the terminal graph is literally the original graph induced on that
embedded vertex set. -/
theorem LeafPruning.terminalGraph_eq_comap
    {k : ℕ} {G : SimpleGraph (Fin k)} (p : LeafPruning k G) :
    p.terminalGraph = G.comap p.terminalLabels := by
  induction p with
  | done G hstop => rfl
  | step H v j hv hvw tail ih =>
      change tail.terminalGraph =
        H.comap (tail.terminalLabels.trans v.succAboveEmb)
      rw [ih]
      rfl

theorem markedGraphWeight_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    markedGraphWeight M t G (fun _ => 1) = M.graphWeight t G := by
  unfold markedGraphWeight markedGraphIntegrand CompactBJRModel.graphWeight
  simp only [ContinuousMap.one_apply, Finset.prod_const_one, one_mul]

open scoped Classical in
/-- Exact rooted-forest reduction for the original, unmarked graph
weight.  All contributions from deleted tree vertices are transported
to the terminal induced graph as continuous vertex marks. -/
theorem graphWeight_leafPruning
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) :
    M.graphWeight t G =
      markedGraphWeight M t p.terminalGraph
        (p.terminalMarks M t (fun _ => 1)) := by
  rw [← markedGraphWeight_one M t G]
  exact markedGraphWeight_leafPruning M t p (fun _ => 1)

/-- The finite pruning algorithm gives an unconditional exact identity
for every labelled graph, with no externally supplied pruning sequence. -/
theorem graphWeight_pruneAll
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (G : SimpleGraph (Fin k)) :
    M.graphWeight t G =
      markedGraphWeight M t
        (LeafPruning.pruneAll k G).terminalGraph
        ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)) :=
  graphWeight_leafPruning M t (LeafPruning.pruneAll k G)

open scoped Classical in
/-- Maximality is certified by the constructors: the final graph of
every valid pruning sequence has no degree-one vertex. -/
theorem LeafPruning.terminal_noLeaf
    {k : ℕ} {G : SimpleGraph (Fin k)} (p : LeafPruning k G) :
    ¬∃ u : Fin p.terminalCount, p.terminalGraph.degree u = 1 := by
  induction p with
  | done G hstop => exact hstop
  | step H v j hv hvw tail ih => exact ih

#print axioms PerronWright.GraphCore.leafMarkUpdate_apply
#print axioms PerronWright.GraphCore.markedGraphWeight_leaf_transfer
#print axioms PerronWright.GraphCore.markedGraphWeight_leafPruning
#print axioms PerronWright.GraphCore.LeafPruning.terminalGraph_eq_comap
#print axioms PerronWright.GraphCore.graphWeight_pruneAll
#print axioms PerronWright.GraphCore.LeafPruning.terminal_noLeaf

end PerronWright.GraphCore

