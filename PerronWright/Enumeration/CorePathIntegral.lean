import PerronWright.Enumeration.CoreComponentLocality
import PerronWright.Enumeration.PathComponentOrder
import PerronWright.Enumeration.PathKernelFullWeight
import PerronWright.Enumeration.PathKernelSymmetry

/-!
# Exact component-to-path-kernel transfer

This module closes the finite-dimensional bridge from an actual
degree-two connected component of a finite core to the analytic path
kernel.  It proves the literal internal/boundary edge partition,
constructs a path order and its two actual boundary stubs, performs the
product-measure relabelling, and identifies the resulting conditional
integral with `pathKernel`.  No endpoint map or abstract component
factorization is assumed.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Relabelling unordered pairs along a vertex equivalence. -/
def sym2Congr {V W : Type*} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by
    intro q
    induction q using Sym2.inductionOn with
    | _ i j => simp [Sym2.map_mk]
  right_inv := by
    intro q
    induction q using Sym2.inductionOn with
    | _ i j => simp [Sym2.map_mk]

@[simp] theorem sym2Congr_mk {V W : Type*} (e : V ≃ W) (i j : V) :
    sym2Congr e s(i,j) = s(e i, e j) := rfl

/-- The same literal finite-graph integrand as the project's labelled
`Fin k` version, formulated on an arbitrary finite vertex type so that
connected-component coordinates can be used directly. -/
def finiteGraphWeightIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → S) : ℝ :=
  (∏ v : V, Real.exp (-t * M.degreeFunction (x v))) *
    ∏ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun i j => t * M.kernel (x i) (x j), by
        intro i j
        change t * M.kernel (x i) (x j) = t * M.kernel (x j) (x i)
        rw [M.kernel.symmetric (x i) (x j)]⟩ e

theorem finiteGraphWeightIntegrand_fin_eq
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) (x : Fin k → S) :
    finiteGraphWeightIntegrand M t G x = M.graphWeightIntegrand t G x := by
  rfl

/-- The literal compact-BJR graph integrand is invariant under an
actual graph isomorphism and the corresponding relabelling of types. -/
theorem finiteGraphWeightIntegrand_iso
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : G ≃g H) (x : W → S) :
    finiteGraphWeightIntegrand M t G (x ∘ e) =
      finiteGraphWeightIntegrand M t H x := by
  unfold finiteGraphWeightIntegrand
  congr 1
  · exact Equiv.prod_comp e.toEquiv
      (fun i : W => Real.exp (-t * M.degreeFunction (x i)))
  · apply Finset.prod_bijective (sym2Congr e.toEquiv)
    · exact (sym2Congr e.toEquiv).bijective
    · intro q
      induction q using Sym2.inductionOn with
      | _ i j =>
          simp only [sym2Congr_mk, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet]
          exact e.map_adj_iff.symm
    · intro q _
      induction q using Sym2.inductionOn with
      | _ i j => rfl

/-- Reindexing an iid product type law along a finite equivalence.
This is the measure-theoretic coordinate change used for an actual
degree-two component's path ordering. -/
theorem integral_pi_reindex
    {S I J : Type*} [MeasurableSpace S]
    [Fintype I] [Fintype J]
    (mu : Measure S) [SigmaFinite mu]
    (e : I ≃ J) (F : (J → S) → ℝ) :
    (∫ y : J → S, F y ∂Measure.pi (fun _ : J => mu)) =
      ∫ x : I → S, F (fun j => x (e.symm j))
        ∂Measure.pi (fun _ : I => mu) := by
  let φ := MeasurableEquiv.piCongrLeft (fun _ : J => S) e
  have hmp : MeasurePreserving φ
      (Measure.pi (fun _ : I => mu))
      (Measure.pi (fun _ : J => mu)) :=
    measurePreserving_piCongrLeft (fun _ : J => mu) e
  have hφ (x : I → S) : φ x = fun j => x (e.symm j) := by
    funext j
    simp [φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  simpa only [hφ] using (hmp.integral_comp' F).symm

/-- The conditional integral of one actual degree-two component can be
put on the standard finite path coordinates supplied by its graph
isomorphism.  The integrand is still the literal component factor. -/
theorem integral_graphCoreComponentFactor_reindex
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    {I : Type*} [Fintype I] (e : I ≃ C) :
    (∫ y : C → S, graphCoreComponentFactor M t G s₀ C b y
        ∂Measure.pi (fun _ : C => M.mu)) =
      ∫ x : I → S,
        graphCoreComponentFactor M t G s₀ C b
          (fun c => x (e.symm c))
        ∂Measure.pi (fun _ : I => M.mu) := by
  exact integral_pi_reindex M.mu e
    (graphCoreComponentFactor M t G s₀ C b)

/-- Inclusion of a degree-two component's vertices into the ambient
finite graph. -/
def componentVertexEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) : C ↪ V where
  toFun x := x.val.val
  inj' := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)

/-- Inclusion of an internal component edge into the ambient graph. -/
def componentEdgeEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) : Sym2 C ↪ Sym2 V where
  toFun := Sym2.map (componentVertexEmbedding G C)
  inj' := Sym2.map.injective (componentVertexEmbedding G C).injective

/-- Ambient edges whose two endpoints are consecutive vertices of the
actual degree-two component. -/
def componentInternalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) : Finset (Sym2 V) :=
  C.toSimpleGraph.edgeFinset.map (componentEdgeEmbedding G C)

/-- A boundary stub determines an ambient edge injectively: its first
endpoint has degree two and its second endpoint does not. -/
def componentBoundaryEdgeEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) :
    {q // q ∈ componentBoundaryStubs G C} ↪ Sym2 V where
  toFun q := s(q.val.1.val.val, q.val.2)
  inj' := by
    rintro ⟨⟨x, b⟩, hxb⟩ ⟨⟨y, c⟩, hyc⟩ h
    have hxb' := hxb
    have hyc' := hyc
    simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
      true_and, Finset.mem_filter, G.mem_neighborFinset] at hxb' hyc'
    rcases Sym2.eq_iff.mp h with hdir | hswap
    · apply Subtype.ext
      apply Sigma.ext (Subtype.ext (Subtype.ext hdir.1))
      simpa [hdir.1] using hdir.2
    · exfalso
      have hcdeg : G.degree c ≠ 2 := hyc'.2
      apply hcdeg
      have hc : x.val.val = c := hswap.1
      subst c
      exact x.val.property

/-- Ambient boundary edges of one actual degree-two component. -/
def componentBoundaryEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) : Finset (Sym2 V) :=
  Finset.univ.map (componentBoundaryEdgeEmbedding G C)

theorem componentInternalEdges_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) (e : Sym2 C) :
    componentEdgeEmbedding G C e ∈ componentInternalEdges G C ↔
      e ∈ C.toSimpleGraph.edgeFinset := by
  simp [componentInternalEdges]

theorem componentBoundaryEdges_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent)
    (q : {q // q ∈ componentBoundaryStubs G C}) :
    componentBoundaryEdgeEmbedding G C q ∈ componentBoundaryEdges G C := by
  simp [componentBoundaryEdges]

/-- The ambient edges owned by one component split literally into its
internal path edges and its two actual boundary edges. -/
theorem component_incident_edges_eq_internal_union_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) :
    G.edgeFinset.filter (fun e => ∃ x : C, x.val.val ∈ e) =
      componentInternalEdges G C ∪ componentBoundaryEdges G C := by
  ext e
  constructor
  · intro he
    obtain ⟨hedge, x, hxe⟩ := Finset.mem_filter.mp he
    let y : V := Sym2.Mem.other hxe
    have hpair : s(x.val.val, y) = e := Sym2.other_spec hxe
    have hadj : G.Adj x.val.val y := by
      rw [← hpair] at hedge
      exact G.mem_edgeSet.mp (G.mem_edgeFinset.mp hedge)
    by_cases hy : G.degree y = 2
    · have hyC : (twoGraph G).connectedComponentMk ⟨y, hy⟩ = C := by
        calc
          (twoGraph G).connectedComponentMk ⟨y, hy⟩ =
              (twoGraph G).connectedComponentMk x.val :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              (show (twoGraph G).Adj x.val ⟨y, hy⟩ from hadj)).symm
          _ = C := x.property
      let yc : C := ⟨⟨y, hy⟩, hyC⟩
      have hxy : C.toSimpleGraph.Adj x yc := hadj
      apply Finset.mem_union_left
      rw [← hpair]
      exact Finset.mem_map.mpr ⟨s(x,yc), by simpa using hxy, rfl⟩
    · let q : Σ _x : C, V := ⟨x, y⟩
      have hq : q ∈ componentBoundaryStubs G C := by
        simp [q, componentBoundaryStubs, G.mem_neighborFinset, hadj, hy]
      apply Finset.mem_union_right
      rw [← hpair]
      exact componentBoundaryEdges_mem G C ⟨q, hq⟩
  · intro he
    rcases Finset.mem_union.mp he with hi | hb
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
      induction q using Sym2.inductionOn with
      | _ x y =>
          have hxy : C.toSimpleGraph.Adj x y := by simpa using hq
          apply Finset.mem_filter.mpr
          refine ⟨?_, x, Sym2.mem_mk_left _ _⟩
          apply G.mem_edgeFinset.mpr
          apply G.mem_edgeSet.mpr
          change G.Adj x.val.val y.val.val
          exact hxy
    · obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hb
      rcases q with ⟨⟨x, b⟩, hxb⟩
      have hxb' := hxb
      simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
        true_and, Finset.mem_filter, G.mem_neighborFinset] at hxb'
      apply Finset.mem_filter.mpr
      refine ⟨?_, x, Sym2.mem_mk_left _ _⟩
      apply G.mem_edgeFinset.mpr
      apply G.mem_edgeSet.mpr
      change G.Adj x.val.val b
      exact hxb'.1

/-- Internal and boundary edge sets of a component are disjoint. -/
theorem componentInternalEdges_disjoint_componentBoundaryEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) :
    Disjoint (componentInternalEdges G C) (componentBoundaryEdges G C) := by
  rw [Finset.disjoint_left]
  intro e hi hb
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hb
  rcases r with ⟨⟨x, b⟩, hxb⟩
  have hxb' := hxb
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_filter, G.mem_neighborFinset] at hxb'
  induction q using Sym2.inductionOn with
  | _ y z =>
      change s(x.val.val, b) = s(y.val.val, z.val.val) at hr
      rcases Sym2.eq_iff.mp hr with hdir | hswap
      · apply hxb'.2
        have hbz : b = z.val.val := hdir.2
        subst b
        exact z.val.property
      · apply hxb'.2
        have hby : b = y.val.val := hswap.2
        subst b
        exact y.val.property

/-- Product of the two actual external edge factors of a degree-two
component, before choosing an orientation of the path. -/
def graphCoreComponentBoundaryFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) : ℝ :=
  ∏ q : {q // q ∈ componentBoundaryStubs G C},
    (t * M.kernel (y q.val.1)
      (coreComponentAssemble G s₀ C b y q.val.2))

/-- The actual branch coordinate carried by a boundary stub. -/
def componentBoundaryStubBranchIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent)
    (q : {q // q ∈ componentBoundaryStubs G C}) : coreBranchIndex G := by
  refine ⟨q.val.2, ?_⟩
  have hq := q.property
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_filter, G.mem_neighborFinset] at hq
  exact hq.2

theorem coreComponentAssemble_boundaryStub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S)
    (q : {q // q ∈ componentBoundaryStubs G C}) :
    coreComponentAssemble G s₀ C b y q.val.2 =
      b (componentBoundaryStubBranchIndex G C q) := by
  exact coreComponentAssemble_branch G s₀ C b y q.val.2
    (componentBoundaryStubBranchIndex G C q).property

/-- The literal factor owned by one actual degree-two component is its
internal induced-graph weight times precisely its two boundary edge
factors. -/
theorem graphCoreComponentFactor_eq_internal_mul_boundary
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) :
    graphCoreComponentFactor M t G s₀ C b y =
      finiteGraphWeightIntegrand M t C.toSimpleGraph y *
        graphCoreComponentBoundaryFactor M t G s₀ C b y := by
  let A := coreComponentAssemble G s₀ C b y
  have hv :
      (∏ v ∈ (Finset.univ : Finset (Fin k)).filter
          (fun v => coreVertexOwner G v = some C),
          Real.exp (-t * M.degreeFunction (A v))) =
        ∏ c : C, Real.exp (-t * M.degreeFunction (y c)) := by
    rw [coreComponentVertices_eq G C]
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro c _
      have hc : A c.val.val = y c := by
        exact coreComponentAssemble_component G s₀ C b y c
      rw [hc]
    · intro x _ z _ h
      exact Subtype.ext (Subtype.ext h)
  have hi :
      (∏ e ∈ componentInternalEdges G C, M.edgeFactor t A e) =
        ∏ e ∈ C.toSimpleGraph.edgeFinset,
          Sym2.lift ⟨fun i j => t * M.kernel (y i) (y j), by
            intro i j
            change t * M.kernel (y i) (y j) = t * M.kernel (y j) (y i)
            rw [M.kernel.symmetric (y i) (y j)]⟩ e := by
    unfold componentInternalEdges
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e he
    induction e using Sym2.inductionOn with
    | _ x z =>
        change
          t * M.kernel
              (coreComponentAssemble G s₀ C b y x.val.val)
              (coreComponentAssemble G s₀ C b y z.val.val) =
            t * M.kernel (y x) (y z)
        rw [coreComponentAssemble_component G s₀ C b y x,
          coreComponentAssemble_component G s₀ C b y z]
  have hbdy :
      (∏ e ∈ componentBoundaryEdges G C, M.edgeFactor t A e) =
        graphCoreComponentBoundaryFactor M t G s₀ C b y := by
    unfold componentBoundaryEdges graphCoreComponentBoundaryFactor
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro q _
    rcases q with ⟨⟨x, d⟩, hxd⟩
    change
      t * M.kernel
          (coreComponentAssemble G s₀ C b y x.val.val)
          (coreComponentAssemble G s₀ C b y d) =
        t * M.kernel (y x) (coreComponentAssemble G s₀ C b y d)
    rw [coreComponentAssemble_component G s₀ C b y x]
  unfold graphCoreComponentFactor coreComponentBlock
  rw [coreComponentEdges_eq_incident G C,
    component_incident_edges_eq_internal_union_boundary G C,
    Finset.prod_union (componentInternalEdges_disjoint_componentBoundaryEdges G C),
    hv, hi, hbdy]
  unfold finiteGraphWeightIntegrand
  ring

theorem pathGraph_degree_zero_lt_two (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).degree 0 < 2 := by
  cases n with
  | zero =>
      have hempty : (SimpleGraph.pathGraph 1).neighborFinset 0 = ∅ := by
        ext i
        simp
      rw [← (SimpleGraph.pathGraph 1).card_neighborFinset_eq_degree 0,
        hempty]
      simp
  | succ m =>
      have hz : (SimpleGraph.pathGraph (m + 1 + 1)).degree 0 = 1 := by
        simpa [Nat.add_assoc] using pathGraph_degree_zero m
      rw [hz]
      omega

/-- The final vertex of a nonempty standard path also has degree below
two, by reversal symmetry. -/
theorem pathGraph_degree_last_lt_two (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).degree (Fin.last n) < 2 := by
  let r : SimpleGraph.pathGraph (n + 1) ≃g
      SimpleGraph.pathGraph (n + 1) :=
    { Fin.revPerm with
      map_rel_iff' := by
        intro i j
        exact pathGraph_adj_rev (n + 1) i j }
  have hr := r.degree_eq (0 : Fin (n + 1))
  have hrev : r (0 : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    change n - 0 = n
    omega
  rw [hrev] at hr
  rw [hr]
  exact pathGraph_degree_zero_lt_two n

/-- A component vertex whose internal degree is below two has an
actual outside neighbor, hence an actual boundary stub. -/
theorem exists_componentBoundaryStub_at
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) (x : C)
    (hx : C.toSimpleGraph.degree x < 2) :
    ∃ b : V, (⟨x, b⟩ : Σ _x : C, V) ∈ componentBoundaryStubs G C := by
  let E := (G.neighborFinset x.val.val).filter (fun b => G.degree b ≠ 2)
  have hcard : E.card = 2 - C.toSimpleGraph.degree x := by
    calc
      E.card = 2 - (twoGraph G).degree x.val :=
        degreeTwo_external_neighbors_eq_deficit G x.val
      _ = 2 - C.toSimpleGraph.degree x := by
        rw [connectedComponent_degree_eq (twoGraph G) C x]
  have hpos : 0 < E.card := by rw [hcard]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  refine ⟨b, ?_⟩
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  exact hb

/-- An actual degree-two path component admits a standard path order
whose first and last vertices carry two distinct actual boundary
stubs.  For a singleton component both stubs share the sole internal
vertex but remain distinct through their outside endpoints. -/
theorem exists_componentPathOrder_with_boundaryStubs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (C : (twoGraph G).ConnectedComponent) :
    ∃ n : ℕ, Fintype.card C = n + 1 ∧
      ∃ e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph,
      ∃ qL qR : {q // q ∈ componentBoundaryStubs G C},
        qL ≠ qR ∧ e 0 = qL.val.1 ∧ e (Fin.last n) = qR.val.1 := by
  have hCpos : 0 < Fintype.card C :=
    Fintype.card_pos_iff.mpr
      ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hCpos)
  refine ⟨n, hn, ?_⟩
  obtain ⟨e₀⟩ := degreeTwo_component_pathGraphIso G hacyc C
  rw [hn] at e₀
  let e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph := e₀
  have hdL : C.toSimpleGraph.degree (e 0) < 2 := by
    rw [e.degree_eq]
    exact pathGraph_degree_zero_lt_two n
  obtain ⟨bL, hbL⟩ := exists_componentBoundaryStub_at G C (e 0) hdL
  let qL : {q // q ∈ componentBoundaryStubs G C} := ⟨⟨e 0, bL⟩, hbL⟩
  cases n with
  | zero =>
      have hcard : Fintype.card {q // q ∈ componentBoundaryStubs G C} = 2 := by
        rw [Fintype.card_coe]
        exact componentBoundaryStubs_card_eq_two G hacyc C
      obtain ⟨qR, hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega) qL
      refine ⟨e, qL, qR, hne.symm, rfl, ?_⟩
      have huniq : ∀ x y : C, x = y :=
        (Fintype.card_le_one_iff.mp (by omega : Fintype.card C ≤ 1))
      exact huniq _ _
  | succ m =>
      have hdR : C.toSimpleGraph.degree (e (Fin.last (m + 1))) < 2 := by
        rw [e.degree_eq]
        exact pathGraph_degree_last_lt_two (m + 1)
      obtain ⟨bR, hbR⟩ :=
        exists_componentBoundaryStub_at G C (e (Fin.last (m + 1))) hdR
      let qR : {q // q ∈ componentBoundaryStubs G C} :=
        ⟨⟨e (Fin.last (m + 1)), bR⟩, hbR⟩
      have hne : qL ≠ qR := by
        intro h
        have hx : e (0 : Fin (m + 2)) = e (Fin.last (m + 1)) := by
          exact congrArg (fun q => q.val.1) h
        have hi : (0 : Fin (m + 2)) = Fin.last (m + 1) := e.injective hx
        have : (0 : ℕ) = m + 1 := congrArg Fin.val hi
        omega
      exact ⟨e, qL, qR, hne, rfl, rfl⟩

/-- Once the actual path order and its two actual boundary stubs are
fixed, the reindexed literal component factor is exactly the finite
path observable used to define `interiorPathGraphWeight`. -/
theorem graphCoreComponentFactor_reindexed_eq_interiorPathObservable
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k n : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1)
    (x : Fin (n + 1) → S) :
    graphCoreComponentFactor M t G s₀ C b
        (fun c => x (e.symm c)) =
      interiorPathObservable M t n
        (b (componentBoundaryStubBranchIndex G C qL))
        (b (componentBoundaryStubBranchIndex G C qR)) x := by
  let y : C → S := fun c => x (e.symm c)
  let A := coreComponentAssemble G s₀ C b y
  have hcard : Fintype.card {q // q ∈ componentBoundaryStubs G C} = 2 := by
    rw [Fintype.card_coe]
    exact componentBoundaryStubs_card_eq_two G hacyc C
  have hpair : (Finset.univ : Finset
      {q // q ∈ componentBoundaryStubs G C}) = {qL, qR} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.subset_univ _
    · rw [Finset.card_pair hne, Finset.card_univ, hcard]
  have hint : finiteGraphWeightIntegrand M t C.toSimpleGraph y =
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1)) x := by
    rw [← finiteGraphWeightIntegrand_fin_eq M t
      (SimpleGraph.pathGraph (n + 1)) x]
    have hiso := finiteGraphWeightIntegrand_iso M t
      (SimpleGraph.pathGraph (n + 1)) C.toSimpleGraph e y
    have hfun : y ∘ e = x := by
      funext i
      simp [y]
    rw [hfun] at hiso
    exact hiso.symm
  rw [graphCoreComponentFactor_eq_internal_mul_boundary M t G s₀ C b y]
  rw [hint]
  have hbdy : graphCoreComponentBoundaryFactor M t G s₀ C b y =
      (t * M.kernel (x 0) (A qL.val.2)) *
        (t * M.kernel (x (Fin.last n)) (A qR.val.2)) := by
    unfold graphCoreComponentBoundaryFactor
    change (∏ q : {q // q ∈ componentBoundaryStubs G C},
      t * M.kernel (y q.val.1) (A q.val.2)) = _
    rw [hpair]
    simp only [Finset.prod_pair hne]
    have hyL : y qL.val.1 = x 0 := by simp [y, ← hL]
    have hyR : y qR.val.1 = x (Fin.last n) := by simp [y, ← hR]
    rw [hyL, hyR]
  rw [hbdy]
  have hAL : A qL.val.2 =
      b (componentBoundaryStubBranchIndex G C qL) := by
    exact coreComponentAssemble_boundaryStub G s₀ C b y qL
  have hAR : A qR.val.2 =
      b (componentBoundaryStubBranchIndex G C qR) := by
    exact coreComponentAssemble_boundaryStub G s₀ C b y qR
  rw [hAL, hAR]
  change _ =
    (t * M.kernel
      (b (componentBoundaryStubBranchIndex G C qL)) (x 0)) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1)) x *
      (t * M.kernel (x (Fin.last n))
        (b (componentBoundaryStubBranchIndex G C qR)))
  rw [M.kernel.symmetric
    (b (componentBoundaryStubBranchIndex G C qL)) (x 0)]
  ring

/-- The conditional integral of one actual degree-two component is
exactly the corresponding path kernel between its two actual branch
endpoints. -/
theorem integral_graphCoreComponentFactor_eq_pathKernel_of_order
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k n : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1) :
    (∫ y : C → S, graphCoreComponentFactor M t G s₀ C b y
        ∂Measure.pi (fun _ : C => M.mu)) =
      pathKernel M t (n + 1)
        (b (componentBoundaryStubBranchIndex G C qL),
          b (componentBoundaryStubBranchIndex G C qR)) := by
  rw [integral_graphCoreComponentFactor_reindex M t G s₀ C b e.toEquiv]
  calc
    (∫ x : Fin (n + 1) → S,
        graphCoreComponentFactor M t G s₀ C b
          (fun c => x (e.symm c))
        ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
      ∫ x : Fin (n + 1) → S,
        interiorPathObservable M t n
          (b (componentBoundaryStubBranchIndex G C qL))
          (b (componentBoundaryStubBranchIndex G C qR)) x
        ∂Measure.pi (fun _ : Fin (n + 1) => M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact graphCoreComponentFactor_reindexed_eq_interiorPathObservable
        M t G hacyc s₀ C b e qL qR hne hL hR x
    _ = interiorPathGraphWeight M t (n + 1)
        (b (componentBoundaryStubBranchIndex G C qL))
        (b (componentBoundaryStubBranchIndex G C qR)) := by
      rfl
    _ = _ := interiorPathGraphWeight_eq_pathKernel M t (n + 1)
      (b (componentBoundaryStubBranchIndex G C qL))
      (b (componentBoundaryStubBranchIndex G C qR))

/-- Every actual degree-two component therefore supplies an honest
path-kernel factor for two actual boundary stubs; no endpoint map or
path ordering is assumed as an external interface. -/
theorem exists_graphCoreComponentFactor_integral_eq_pathKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) :
    ∃ n : ℕ, Fintype.card C = n + 1 ∧
      ∃ qL qR : {q // q ∈ componentBoundaryStubs G C},
        qL ≠ qR ∧
        (∫ y : C → S, graphCoreComponentFactor M t G s₀ C b y
            ∂Measure.pi (fun _ : C => M.mu)) =
          pathKernel M t (n + 1)
            (b (componentBoundaryStubBranchIndex G C qL),
              b (componentBoundaryStubBranchIndex G C qR)) := by
  obtain ⟨n, hn, e, qL, qR, hne, hL, hR⟩ :=
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  refine ⟨n, hn, qL, qR, hne, ?_⟩
  exact integral_graphCoreComponentFactor_eq_pathKernel_of_order
    M t G hacyc s₀ C b e qL qR hne hL hR

#print axioms PerronWright.GraphCore.finiteGraphWeightIntegrand_iso
#print axioms PerronWright.GraphCore.integral_pi_reindex
#print axioms PerronWright.GraphCore.integral_graphCoreComponentFactor_reindex
#print axioms PerronWright.GraphCore.component_incident_edges_eq_internal_union_boundary
#print axioms PerronWright.GraphCore.componentInternalEdges_disjoint_componentBoundaryEdges
#print axioms PerronWright.GraphCore.graphCoreComponentFactor_eq_internal_mul_boundary
#print axioms PerronWright.GraphCore.exists_componentPathOrder_with_boundaryStubs
#print axioms PerronWright.GraphCore.graphCoreComponentFactor_reindexed_eq_interiorPathObservable
#print axioms PerronWright.GraphCore.integral_graphCoreComponentFactor_eq_pathKernel_of_order
#print axioms PerronWright.GraphCore.exists_graphCoreComponentFactor_integral_eq_pathKernel

end PerronWright.GraphCore
