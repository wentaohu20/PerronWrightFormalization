import PerronWright.Enumeration.ConnectedWeight
import PerronWright.Enumeration.KernelValence

/-!
Pointwise exact partition of a genuine finite core's vertex and edge
weights into one branch block and one block for every degree-two
component.  This is a scratch proof before the simultaneous integral.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

abbrev twoGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  G.induce {v | G.degree v = 2}

/-- The unique degree-two component owning a vertex, when it is
degree two. -/
def coreVertexOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Option (twoGraph G).ConnectedComponent :=
  if h : G.degree v = 2 then
    some ((twoGraph G).connectedComponentMk ⟨v, h⟩)
  else none

/-- An edge is assigned to the component of one of its degree-two
endpoints, if it has one; otherwise it is a direct branch edge. -/
def coreEdgeOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) :
    Option (twoGraph G).ConnectedComponent :=
  if h : ∃ v ∈ e, G.degree v = 2 then
    some ((twoGraph G).connectedComponentMk ⟨h.choose, h.choose_spec.2⟩)
  else none

/-- If both ends of an actual edge have degree two, they belong to
the same induced degree-two component. -/
theorem sameTwoComponent_of_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset)
    {v w : V} (hv : v ∈ e) (hw : w ∈ e)
    (hvd : G.degree v = 2) (hwd : G.degree w = 2) :
    (twoGraph G).connectedComponentMk ⟨v, hvd⟩ =
      (twoGraph G).connectedComponentMk ⟨w, hwd⟩ := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · rcases Sym2.mem_iff.mp hw with rfl | rfl
      · rfl
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (twoGraph G).Adj ⟨v, hvd⟩ ⟨w, hwd⟩ from hab)
    · rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (twoGraph G).Adj ⟨w, hwd⟩ ⟨v, hvd⟩ from hab)).symm
      · rfl

/-- The edge-owner choice is independent of which incident
degree-two vertex witnesses the edge. -/
theorem coreEdgeOwner_eq_component_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset)
    {v : V} (hv : v ∈ e) (hvd : G.degree v = 2) :
    coreEdgeOwner G e =
      some ((twoGraph G).connectedComponentMk ⟨v, hvd⟩) := by
  unfold coreEdgeOwner
  split_ifs with h
  · congr 1
    exact sameTwoComponent_of_edge G he h.choose_spec.1 hv h.choose_spec.2 hvd
  · exact False.elim (h ⟨v, hv, hvd⟩)

/-- On actual core edges, the owner is a component exactly when the
edge touches a vertex of that component. -/
theorem coreEdgeOwner_eq_some_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (C : (twoGraph G).ConnectedComponent) :
    coreEdgeOwner G e = some C ↔
      ∃ x : C, x.val.val ∈ e := by
  constructor
  · intro ho
    unfold coreEdgeOwner at ho
    split_ifs at ho with h
    · have hc := Option.some_inj.mp ho
      let z : {v : V // G.degree v = 2} := ⟨h.choose, h.choose_spec.2⟩
      have hz : z ∈ C := by
        change (twoGraph G).connectedComponentMk z = C
        exact hc
      exact ⟨⟨z, hz⟩, h.choose_spec.1⟩
  · rintro ⟨x, hx⟩
    rw [coreEdgeOwner_eq_component_of_mem G he hx x.val.property]
    congr 1
    exact x.property

/-- Each component's edge block is the set of its actual incident
edges, including both boundary stubs and every internal edge. -/
theorem coreComponentEdges_eq_incident
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) :
    G.edgeFinset.filter (fun e => coreEdgeOwner G e = some C) =
      G.edgeFinset.filter (fun e => ∃ x : C, x.val.val ∈ e) := by
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, ho⟩
    exact ⟨he, (coreEdgeOwner_eq_some_iff G he C).mp ho⟩
  · rintro ⟨he, hx⟩
    exact ⟨he, (coreEdgeOwner_eq_some_iff G he C).mpr hx⟩

/-- The vertex block indexed by a degree-two component contains
precisely that component's actual vertices. -/
theorem coreComponentVertices_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent)
    [Fintype C] :
    (Finset.univ : Finset V).filter
        (fun v => coreVertexOwner G v = some C) =
      (Finset.univ : Finset C).image (fun x => x.val.val) := by
  ext v
  constructor
  · intro hv
    have ho : coreVertexOwner G v = some C := (Finset.mem_filter.mp hv).2
    unfold coreVertexOwner at ho
    split_ifs at ho with h
    · have hc := Option.some_inj.mp ho
      exact Finset.mem_image.mpr
        ⟨⟨⟨v, h⟩, hc⟩, Finset.mem_univ _, rfl⟩
  · intro hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      unfold coreVertexOwner
      split_ifs with h
      · exact congrArg some x.property
      · exact False.elim (h x.val.property)⟩

/-- On a minimum-degree-two core, non-degree-two vertices are exactly
the branch vertices, so the branch block has no hidden vertices. -/
theorem coreVertexOwner_none_iff_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) (v : V) :
    coreVertexOwner G v = none ↔ v ∈ branchingVertices G := by
  have hB := mem_branchingVertices_iff_degree_ne_two G hmin v
  by_cases h : G.degree v = 2
  · simp [coreVertexOwner, h, hB]
  · simp [coreVertexOwner, h, hB]

/-- On a minimum-degree-two core, edges without a degree-two endpoint
are exactly the original direct branch-to-branch edges. -/
theorem coreEdgeOwner_none_iff_direct
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    coreEdgeOwner G e = none ↔ e ∈ directBranchEdges G := by
  have hB (v : V) : v ∈ branchingVertices G ↔ G.degree v ≠ 2 :=
    mem_branchingVertices_iff_degree_ne_two G hmin v
  constructor
  · intro ho
    apply Finset.mem_filter.mpr
    refine ⟨he, ?_⟩
    intro v hv
    apply (hB v).mpr
    intro h2
    have hex : ∃ u ∈ e, G.degree u = 2 := ⟨v, hv, h2⟩
    have : coreEdgeOwner G e ≠ none := by simp [coreEdgeOwner, hex]
    exact this ho
  · intro hd
    have hall := (Finset.mem_filter.mp hd).2
    have hnot : ¬ ∃ v ∈ e, G.degree v = 2 := by
      rintro ⟨v, hv, h2⟩
      exact (hB v).mp (hall v hv) h2
    simp [coreEdgeOwner, hnot]

def coreBranchBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vf : V → ℝ) (ef : Sym2 V → ℝ) : ℝ :=
  (∏ v ∈ (Finset.univ : Finset V).filter (fun v => coreVertexOwner G v = none), vf v) *
  ∏ e ∈ G.edgeFinset.filter (fun e => coreEdgeOwner G e = none), ef e

def coreComponentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vf : V → ℝ) (ef : Sym2 V → ℝ)
    (C : (twoGraph G).ConnectedComponent) : ℝ :=
  (∏ v ∈ (Finset.univ : Finset V).filter
      (fun v => coreVertexOwner G v = some C), vf v) *
  ∏ e ∈ G.edgeFinset.filter (fun e => coreEdgeOwner G e = some C), ef e

/-- All actual vertex/edge factors occur exactly once in the
simultaneous branch-and-path-component product. -/
theorem coreWeight_factor_pointwise
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    (vf : V → ℝ) (ef : Sym2 V → ℝ) :
    (∏ v : V, vf v) * (∏ e ∈ G.edgeFinset, ef e) =
      coreBranchBlock G vf ef *
        ∏ C : (twoGraph G).ConnectedComponent,
          coreComponentBlock G vf ef C := by
  have hv : (∏ v : V, vf v) =
      (∏ v ∈ (Finset.univ : Finset V).filter
        (fun v => coreVertexOwner G v = none), vf v) *
      ∏ C : (twoGraph G).ConnectedComponent,
        ∏ v ∈ (Finset.univ : Finset V).filter
          (fun v => coreVertexOwner G v = some C), vf v := by
    calc
      _ = ∏ o : Option (twoGraph G).ConnectedComponent,
            ∏ v ∈ (Finset.univ : Finset V).filter
              (fun v => coreVertexOwner G v = o), vf v :=
        (Finset.prod_fiberwise (Finset.univ : Finset V)
          (coreVertexOwner G) vf).symm
      _ = _ := by rw [Fintype.prod_option]
  have he : (∏ e ∈ G.edgeFinset, ef e) =
      (∏ e ∈ G.edgeFinset.filter
        (fun e => coreEdgeOwner G e = none), ef e) *
      ∏ C : (twoGraph G).ConnectedComponent,
        ∏ e ∈ G.edgeFinset.filter
          (fun e => coreEdgeOwner G e = some C), ef e := by
    calc
      _ = ∏ o : Option (twoGraph G).ConnectedComponent,
            ∏ e ∈ G.edgeFinset.filter
              (fun e => coreEdgeOwner G e = o), ef e :=
        (Finset.prod_fiberwise G.edgeFinset
          (coreEdgeOwner G) ef).symm
      _ = _ := by rw [Fintype.prod_option]
  rw [hv, he]
  unfold coreBranchBlock coreComponentBlock
  rw [Finset.prod_mul_distrib]
  ring

/-- Literal compact-type BJR core weight factors simultaneously into
the branch block and all actual degree-two component blocks. -/
theorem graphWeightIntegrand_coreFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (x : Fin k → S) :
    M.graphWeightIntegrand t G x =
      coreBranchBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x v)))
        (fun e => M.edgeFactor t x e) *
      ∏ C : (twoGraph G).ConnectedComponent,
        coreComponentBlock G
          (fun v => Real.exp (-t * M.degreeFunction (x v)))
          (fun e => M.edgeFactor t x e) C := by
  unfold CompactBJRModel.graphWeightIntegrand
  exact coreWeight_factor_pointwise G
    (fun v => Real.exp (-t * M.degreeFunction (x v)))
    (fun e => M.edgeFactor t x e)

#print axioms PerronWright.GraphCore.coreWeight_factor_pointwise
#print axioms PerronWright.GraphCore.graphWeightIntegrand_coreFactor

end PerronWright.GraphCore
