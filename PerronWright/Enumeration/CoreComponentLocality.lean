import PerronWright.Enumeration.CoreCoordinates
import PerronWright.Enumeration.FieldWeight

/-!
An actual degree-two component's compact-BJR block depends only on its own
vertex types and on the branch endpoint types, not on any other
degree-two component's type coordinates.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

theorem coreCoordinate_branch_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} [MeasurableSpace S]
    (x : V → S) (b : coreBranchIndex G) :
    (coreCoordinateMeasurableEquiv G x).1 b = x b.val := by
  rfl

theorem coreCoordinate_component_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} [MeasurableSpace S]
    (x : V → S)
    (C : (twoGraph G).ConnectedComponent) (c : C) :
    (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩ = x c.val.val := by
  rfl

/-- Fill one component's vertices from `y` and all non-degree-two
vertices from `b`; other components receive an arbitrary harmless
type, which the local factor never reads. -/
def coreComponentAssemble
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) : V → S :=
  fun v =>
    if hb : G.degree v ≠ 2 then b ⟨v, hb⟩
    else
      let h2 : G.degree v = 2 := not_not.mp hb
      if hc : (twoGraph G).connectedComponentMk ⟨v, h2⟩ = C then
        y ⟨⟨v, h2⟩, hc⟩
      else s₀

/-- A branch-only filling used to define the fixed-branch factor. -/
def coreBranchAssemble
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (b : coreBranchIndex G → S) : V → S :=
  fun v => if hb : G.degree v ≠ 2 then b ⟨v, hb⟩ else s₀

theorem coreBranchAssemble_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (b : coreBranchIndex G → S)
    (v : V) (hv : G.degree v ≠ 2) :
    coreBranchAssemble G s₀ b v = b ⟨v, hv⟩ := by
  simp [coreBranchAssemble, hv]

theorem coreComponentAssemble_branch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S)
    (v : V) (hv : G.degree v ≠ 2) :
    coreComponentAssemble G s₀ C b y v = b ⟨v, hv⟩ := by
  simp [coreComponentAssemble, hv]

theorem coreComponentAssemble_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} (s₀ : S)
    (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S)
    (c : C) :
    coreComponentAssemble G s₀ C b y c.val.val = y c := by
  have h2 : G.degree c.val.val = 2 := c.val.property
  have hc : (twoGraph G).connectedComponentMk c.val = C := c.property
  simp [coreComponentAssemble, h2, hc]

/-- The literal factor for one degree-two component of a finite core
is unchanged when all other degree-two components' types vary. -/
theorem graphComponentBlock_eq_of_agree
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent)
    (x x' : Fin k → S)
    (hbranch : ∀ v : Fin k, G.degree v ≠ 2 → x v = x' v)
    (hcomponent : ∀ c : C, x c.val.val = x' c.val.val) :
    coreComponentBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x v)))
        (fun e => M.edgeFactor t x e) C =
      coreComponentBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x' v)))
        (fun e => M.edgeFactor t x' e) C := by
  unfold coreComponentBlock
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    have ho : coreVertexOwner G v = some C := (Finset.mem_filter.mp hv).2
    unfold coreVertexOwner at ho
    split_ifs at ho with hd
    · have hc := Option.some_inj.mp ho
      have hval := hcomponent (⟨⟨v, hd⟩, hc⟩ : C)
      change x v = x' v at hval
      change Real.exp (-t * M.degreeFunction (x v)) =
        Real.exp (-t * M.degreeFunction (x' v))
      rw [hval]
  · apply Finset.prod_congr rfl
    intro e he
    have hedge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have howner : coreEdgeOwner G e = some C := (Finset.mem_filter.mp he).2
    have hval (v : Fin k) (hv : v ∈ e) : x v = x' v := by
      by_cases hd : G.degree v = 2
      · have ho := coreEdgeOwner_eq_component_of_mem G hedge hv hd
        have hc : (twoGraph G).connectedComponentMk ⟨v, hd⟩ = C :=
          Option.some_inj.mp (ho.symm.trans howner)
        exact hcomponent (⟨⟨v, hd⟩, hc⟩ : C)
      · exact hbranch v hd
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ha := hval a (Sym2.mem_mk_left a b)
      have hb := hval b (Sym2.mem_mk_right a b)
      simp only [CompactBJRModel.edgeFactor_mk, ha, hb]

/-- The direct branch block depends only on non-degree-two vertex
types, hence only on branch coordinates in a genuine 2-core. -/
theorem graphBranchBlock_eq_of_agree
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (x x' : Fin k → S)
    (hbranch : ∀ v : Fin k, G.degree v ≠ 2 → x v = x' v) :
    coreBranchBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x v)))
        (fun e => M.edgeFactor t x e) =
      coreBranchBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x' v)))
        (fun e => M.edgeFactor t x' e) := by
  unfold coreBranchBlock
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    have ho : coreVertexOwner G v = none := (Finset.mem_filter.mp hv).2
    have hd : G.degree v ≠ 2 := by
      intro h2
      simp [coreVertexOwner, h2] at ho
    change Real.exp (-t * M.degreeFunction (x v)) =
      Real.exp (-t * M.degreeFunction (x' v))
    rw [hbranch v hd]
  · apply Finset.prod_congr rfl
    intro e he
    have hedge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have howner : coreEdgeOwner G e = none := (Finset.mem_filter.mp he).2
    have hval (v : Fin k) (hv : v ∈ e) : x v = x' v := by
      apply hbranch v
      intro h2
      have ho := coreEdgeOwner_eq_component_of_mem G hedge hv h2
      rw [howner] at ho
      contradiction
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ha := hval a (Sym2.mem_mk_left a b)
      have hb := hval b (Sym2.mem_mk_right a b)
      simp only [CompactBJRModel.edgeFactor_mk, ha, hb]

/-- The branch block can be computed from the branch type vector
alone, with arbitrary filler on all path vertices. -/
theorem graphBranchBlock_eq_assemble
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (x : Fin k → S)
    (b : coreBranchIndex G → S)
    (hb : ∀ c : coreBranchIndex G, b c = x c.val) :
    coreBranchBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x v)))
        (fun e => M.edgeFactor t x e) =
      coreBranchBlock G
        (fun v => Real.exp (-t * M.degreeFunction
          (coreBranchAssemble G s₀ b v)))
        (fun e => M.edgeFactor t (coreBranchAssemble G s₀ b) e) := by
  apply graphBranchBlock_eq_of_agree M t G x (coreBranchAssemble G s₀ b)
  intro v hv
  calc
    x v = b ⟨v, hv⟩ := (hb ⟨v, hv⟩).symm
    _ = coreBranchAssemble G s₀ b v :=
      (coreBranchAssemble_branch G s₀ b v hv).symm

/-- A component block can be computed from its own type vector and
the branch vector alone, with arbitrary filler on other components. -/
theorem graphComponentBlock_eq_assemble
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (x : Fin k → S)
    (b : coreBranchIndex G → S) (y : C → S)
    (hb : ∀ c : coreBranchIndex G, b c = x c.val)
    (hy : ∀ c : C, y c = x c.val.val) :
    coreComponentBlock G
        (fun v => Real.exp (-t * M.degreeFunction (x v)))
        (fun e => M.edgeFactor t x e) C =
      coreComponentBlock G
        (fun v => Real.exp (-t * M.degreeFunction
          (coreComponentAssemble G s₀ C b y v)))
        (fun e => M.edgeFactor t
          (coreComponentAssemble G s₀ C b y) e) C := by
  apply graphComponentBlock_eq_of_agree M t G C x
    (coreComponentAssemble G s₀ C b y)
  · intro v hv
    calc
      x v = b ⟨v, hv⟩ := (hb ⟨v, hv⟩).symm
      _ = coreComponentAssemble G s₀ C b y v :=
        (coreComponentAssemble_branch G s₀ C b y v hv).symm
  · intro c
    calc
      x c.val.val = y c := (hy c).symm
      _ = coreComponentAssemble G s₀ C b y c.val.val :=
        (coreComponentAssemble_component G s₀ C b y c).symm

/-- The literal branch factor as a function only of branch types. -/
def graphCoreBranchFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (b : coreBranchIndex G → S) : ℝ :=
  coreBranchBlock G
    (fun v => Real.exp (-t * M.degreeFunction
      (coreBranchAssemble G s₀ b v)))
    (fun e => M.edgeFactor t (coreBranchAssemble G s₀ b) e)

/-- The literal factor of one actual degree-two component, expressed
only in its own types and the branch types. -/
def graphCoreComponentFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) : ℝ :=
  coreComponentBlock G
    (fun v => Real.exp (-t * M.degreeFunction
      (coreComponentAssemble G s₀ C b y v)))
    (fun e => M.edgeFactor t (coreComponentAssemble G s₀ C b y) e) C

/-- Exact graph-integrand factorization in the coordinate system used
by the simultaneous integral. -/
theorem graphWeightIntegrand_eq_coreFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    [∀ C : (twoGraph G).ConnectedComponent, Fintype C]
    (s₀ : S) (x : Fin k → S) :
    M.graphWeightIntegrand t G x =
      graphCoreBranchFactor M t G s₀
        (coreCoordinateMeasurableEquiv G x).1 *
      ∏ C : (twoGraph G).ConnectedComponent,
        graphCoreComponentFactor M t G s₀ C
          (coreCoordinateMeasurableEquiv G x).1
          (fun c => (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩) := by
  unfold graphCoreBranchFactor graphCoreComponentFactor
  rw [graphWeightIntegrand_coreFactor]
  congr 1
  · exact graphBranchBlock_eq_assemble M t G s₀ x _
      (fun c => coreCoordinate_branch_apply G x c)
  · apply Finset.prod_congr rfl
    intro C _
    exact graphComponentBlock_eq_assemble M t G s₀ C x _ _
      (fun c => coreCoordinate_branch_apply G x c)
      (fun c => coreCoordinate_component_apply G x C c)

/-- After the canonical coordinate regrouping, conditional Fubini
integrates every actual degree-two component in its own type block.
This is an identity for the literal compact-BJR graph weight. -/
theorem graphWeight_eq_integral_coreComponentFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    [∀ C : (twoGraph G).ConnectedComponent, Fintype C]
    (s₀ : S) :
    M.graphWeight t G =
      ∫ b : coreBranchIndex G → S,
        graphCoreBranchFactor M t G s₀ b *
          ∏ C : (twoGraph G).ConnectedComponent,
            (∫ y : C → S,
              graphCoreComponentFactor M t G s₀ C b y
              ∂Measure.pi (fun _ : C => M.mu))
        ∂Measure.pi (fun _ : coreBranchIndex G => M.mu) := by
  let e := coreCoordinateMeasurableEquiv G (S := S)
  let μB := Measure.pi (fun _ : coreBranchIndex G => M.mu)
  let μC := Measure.pi
    (fun _ : Σ C : (twoGraph G).ConnectedComponent, C => M.mu)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin k => M.mu)) (μB.prod μC) :=
    coreCoordinate_measurePreserving G M.mu
  have hbase : Integrable (M.graphWeightIntegrand t G)
      (Measure.pi (fun _ : Fin k => M.mu)) :=
    M.graphWeightIntegrand_integrable t G
  have hcoord : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S) =>
        M.graphWeightIntegrand t G (e.symm p))
      (μB.prod μC) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hbase
  have hfactor (p : (coreBranchIndex G → S) ×
      ((Σ C : (twoGraph G).ConnectedComponent, C) → S)) :
      M.graphWeightIntegrand t G (e.symm p) =
        graphCoreBranchFactor M t G s₀ p.1 *
          ∏ C : (twoGraph G).ConnectedComponent,
            graphCoreComponentFactor M t G s₀ C p.1
              (fun c => p.2 ⟨C, c⟩) := by
    simpa only [e, MeasurableEquiv.apply_symm_apply] using
      graphWeightIntegrand_eq_coreFactors M t G s₀ (e.symm p)
  have hInt : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S) =>
        graphCoreBranchFactor M t G s₀ p.1 *
          ∏ C : (twoGraph G).ConnectedComponent,
            graphCoreComponentFactor M t G s₀ C p.1
              (fun c => p.2 ⟨C, c⟩))
      (μB.prod μC) := by
    refine hcoord.congr ?_
    filter_upwards [] with p
    exact hfactor p
  unfold CompactBJRModel.graphWeight
  calc
    (∫ x : Fin k → S, M.graphWeightIntegrand t G x
        ∂Measure.pi (fun _ : Fin k => M.mu)) =
        ∫ x : Fin k → S,
          graphCoreBranchFactor M t G s₀
              (coreCoordinateMeasurableEquiv G x).1 *
            ∏ C : (twoGraph G).ConnectedComponent,
              graphCoreComponentFactor M t G s₀ C
                (coreCoordinateMeasurableEquiv G x).1
                (fun c => (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩)
          ∂Measure.pi (fun _ : Fin k => M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact graphWeightIntegrand_eq_coreFactors M t G s₀ x
    _ = _ := integral_core_component_blocks G M.mu
      (graphCoreBranchFactor M t G s₀)
      (fun C => graphCoreComponentFactor M t G s₀ C) hInt

#print axioms PerronWright.GraphCore.graphComponentBlock_eq_of_agree
#print axioms PerronWright.GraphCore.graphBranchBlock_eq_of_agree
#print axioms PerronWright.GraphCore.graphWeightIntegrand_eq_coreFactors
#print axioms PerronWright.GraphCore.graphWeight_eq_integral_coreComponentFactors

end PerronWright.GraphCore
