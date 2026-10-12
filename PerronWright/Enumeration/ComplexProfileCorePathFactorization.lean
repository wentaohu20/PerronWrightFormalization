import PerronWright.Enumeration.ComplexProfilePathCoefficient
import PerronWright.Enumeration.MarkedCoreFactorization
import PerronWright.Enumeration.UnicyclicFixedCoreAnalytic

/-!
# Complex-profile factorization of a fixed two-core

For an actual finite minimum-degree-two core, this file separates the
branch coordinates from the degree-two components at the level of the
genuine complex-profile graph integral.  Once a path order and its two
boundary stubs are fixed for each component, the conditional component
integral is exactly `profilePathEdgeCoefficient` at the actual path length.

The statements here are for one fixed core and explicit path orders.  They
do not assume a global subdivision classification or a regrouping of the
outer graph sum.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Complex kernel factor on an unordered edge. -/
def complexKernelEdgeFactor (M : CompactBJRModel S)
    {V : Type*} (x : V → S) (e : Sym2 V) : ℂ :=
  Sym2.lift ⟨fun i j ↦ (M.kernel (x i) (x j) : ℂ), by
    intro i j
    exact congrArg (fun r : ℝ ↦ (r : ℂ))
      (M.kernel.symmetric (x i) (x j))⟩ e

@[simp] theorem complexKernelEdgeFactor_mk
    (M : CompactBJRModel S) {V : Type*}
    (x : V → S) (i j : V) :
    complexKernelEdgeFactor M x s(i,j) =
      (M.kernel (x i) (x j) : ℂ) := rfl

/-- The complex vertex and direct-edge block. -/
def complexCoreBranchBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vf : V → ℂ) (ef : Sym2 V → ℂ) : ℂ :=
  (∏ v ∈ (Finset.univ : Finset V).filter
      (fun v ↦ coreVertexOwner G v = none), vf v) *
    ∏ e ∈ G.edgeFinset.filter
      (fun e ↦ coreEdgeOwner G e = none), ef e

/-- The complex block owned by one degree-two component. -/
def complexCoreComponentBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vf : V → ℂ) (ef : Sym2 V → ℂ)
    (C : (twoGraph G).ConnectedComponent) : ℂ :=
  (∏ v ∈ (Finset.univ : Finset V).filter
      (fun v ↦ coreVertexOwner G v = some C), vf v) *
    ∏ e ∈ G.edgeFinset.filter
      (fun e ↦ coreEdgeOwner G e = some C), ef e

/-- Every complex vertex and edge factor occurs exactly once in the branch
block or in one degree-two component block. -/
theorem complexCoreWeight_factor_pointwise
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    (vf : V → ℂ) (ef : Sym2 V → ℂ) :
    (∏ v : V, vf v) * (∏ e ∈ G.edgeFinset, ef e) =
      complexCoreBranchBlock G vf ef *
        ∏ C : (twoGraph G).ConnectedComponent,
          complexCoreComponentBlock G vf ef C := by
  have hv : (∏ v : V, vf v) =
      (∏ v ∈ (Finset.univ : Finset V).filter
        (fun v ↦ coreVertexOwner G v = none), vf v) *
      ∏ C : (twoGraph G).ConnectedComponent,
        ∏ v ∈ (Finset.univ : Finset V).filter
          (fun v ↦ coreVertexOwner G v = some C), vf v := by
    calc
      _ = ∏ o : Option (twoGraph G).ConnectedComponent,
            ∏ v ∈ (Finset.univ : Finset V).filter
              (fun v ↦ coreVertexOwner G v = o), vf v :=
        (Finset.prod_fiberwise (Finset.univ : Finset V)
          (coreVertexOwner G) vf).symm
      _ = _ := by rw [Fintype.prod_option]
  have he : (∏ e ∈ G.edgeFinset, ef e) =
      (∏ e ∈ G.edgeFinset.filter
        (fun e ↦ coreEdgeOwner G e = none), ef e) *
      ∏ C : (twoGraph G).ConnectedComponent,
        ∏ e ∈ G.edgeFinset.filter
          (fun e ↦ coreEdgeOwner G e = some C), ef e := by
    calc
      _ = ∏ o : Option (twoGraph G).ConnectedComponent,
            ∏ e ∈ G.edgeFinset.filter
              (fun e ↦ coreEdgeOwner G e = o), ef e :=
        (Finset.prod_fiberwise G.edgeFinset
          (coreEdgeOwner G) ef).symm
      _ = _ := by rw [Fintype.prod_option]
  rw [hv, he]
  unfold complexCoreBranchBlock complexCoreComponentBlock
  rw [Finset.prod_mul_distrib]
  ring

/-- The genuine complex-profile graph integrand has the preceding exact
branch/component factorization. -/
theorem finiteComplexGraphIntegrand_coreFactor
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    (x : V → S) :
    finiteComplexGraphIntegrand M tau G x =
      complexCoreBranchBlock G
          (fun v ↦ tau (x v)) (complexKernelEdgeFactor M x) *
        ∏ C : (twoGraph G).ConnectedComponent,
          complexCoreComponentBlock G
            (fun v ↦ tau (x v)) (complexKernelEdgeFactor M x) C := by
  unfold finiteComplexGraphIntegrand
  exact complexCoreWeight_factor_pointwise G
    (fun v ↦ tau (x v)) (complexKernelEdgeFactor M x)

/-- The branch block as a function only of the branch coordinates. -/
def complexProfileCoreBranchFactor
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (b : coreBranchIndex G → S) : ℂ :=
  complexCoreBranchBlock G
    (fun v ↦ tau (coreBranchAssemble G s₀ b v))
    (complexKernelEdgeFactor M (coreBranchAssemble G s₀ b))

/-- The block of one degree-two component as a function of its own and the
branch coordinates. -/
def complexProfileCoreComponentFactor
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) : ℂ :=
  complexCoreComponentBlock G
    (fun v ↦ tau (coreComponentAssemble G s₀ C b y v))
    (complexKernelEdgeFactor M (coreComponentAssemble G s₀ C b y)) C

private theorem complexCoreBranchBlock_eq_of_agree
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (x x' : Fin k → S)
    (hbranch : ∀ v, G.degree v ≠ 2 → x v = x' v) :
    complexCoreBranchBlock G
        (fun v ↦ tau (x v)) (complexKernelEdgeFactor M x) =
      complexCoreBranchBlock G
        (fun v ↦ tau (x' v)) (complexKernelEdgeFactor M x') := by
  unfold complexCoreBranchBlock
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    have ho : coreVertexOwner G v = none := (Finset.mem_filter.mp hv).2
    have hd : G.degree v ≠ 2 := by
      intro h2
      simp [coreVertexOwner, h2] at ho
    change tau (x v) = tau (x' v)
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
        simp only [complexKernelEdgeFactor_mk, hval a (Sym2.mem_mk_left a b),
          hval b (Sym2.mem_mk_right a b)]

private theorem complexCoreComponentBlock_eq_of_agree
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (C : (twoGraph G).ConnectedComponent) (x x' : Fin k → S)
    (hbranch : ∀ v, G.degree v ≠ 2 → x v = x' v)
    (hcomponent : ∀ c : C, x c.val.val = x' c.val.val) :
    complexCoreComponentBlock G
        (fun v ↦ tau (x v)) (complexKernelEdgeFactor M x) C =
      complexCoreComponentBlock G
        (fun v ↦ tau (x' v)) (complexKernelEdgeFactor M x') C := by
  unfold complexCoreComponentBlock
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    have ho : coreVertexOwner G v = some C := (Finset.mem_filter.mp hv).2
    unfold coreVertexOwner at ho
    split_ifs at ho with hd
    · have hc := Option.some_inj.mp ho
      change tau (x v) = tau (x' v)
      rw [hcomponent (⟨⟨v, hd⟩, hc⟩ : C)]
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
        simp only [complexKernelEdgeFactor_mk, hval a (Sym2.mem_mk_left a b),
          hval b (Sym2.mem_mk_right a b)]

/-- Exact pointwise factorization in the canonical core coordinate system. -/
theorem finiteComplexGraphIntegrand_eq_complexProfileCoreFactors
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (s₀ : S) (x : Fin k → S) :
    finiteComplexGraphIntegrand M tau G x =
      complexProfileCoreBranchFactor M tau G s₀
          (coreCoordinateMeasurableEquiv G x).1 *
        ∏ C : (twoGraph G).ConnectedComponent,
          complexProfileCoreComponentFactor M tau G s₀ C
            (coreCoordinateMeasurableEquiv G x).1
            (fun c ↦ (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩) := by
  rw [finiteComplexGraphIntegrand_coreFactor M tau G x]
  congr 1
  · unfold complexProfileCoreBranchFactor
    apply complexCoreBranchBlock_eq_of_agree M tau G
    intro v hv
    exact (coreCoordinate_branch_apply G x ⟨v, hv⟩).symm.trans
      (coreBranchAssemble_branch G s₀ _ v hv).symm
  · apply Finset.prod_congr rfl
    intro C hC
    unfold complexProfileCoreComponentFactor
    apply complexCoreComponentBlock_eq_of_agree M tau G C
    · intro v hv
      exact (coreCoordinate_branch_apply G x ⟨v, hv⟩).symm.trans
        (coreComponentAssemble_branch G s₀ C _ _ v hv).symm
    · intro c
      exact (coreCoordinate_component_apply G x C c).symm.trans
        (coreComponentAssemble_component G s₀ C
          (coreCoordinateMeasurableEquiv G x).1
          (fun c ↦ (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩) c).symm

/-- Reindex a complex-valued integral against an iid finite product law. -/
private theorem integral_pi_reindex_complex_local
    {X I J : Type*} [MeasurableSpace X]
    [Fintype I] [Fintype J]
    (mu : Measure X) [SigmaFinite mu]
    (e : I ≃ J) (F : (J → X) → ℂ) :
    (∫ y : J → X, F y ∂Measure.pi (fun _ : J ↦ mu)) =
      ∫ x : I → X, F (fun j ↦ x (e.symm j))
        ∂Measure.pi (fun _ : I ↦ mu) := by
  let φ := MeasurableEquiv.piCongrLeft (fun _ : J ↦ X) e
  have hmp : MeasurePreserving φ
      (Measure.pi (fun _ : I ↦ mu))
      (Measure.pi (fun _ : J ↦ mu)) :=
    measurePreserving_piCongrLeft (fun _ : J ↦ mu) e
  have hφ (x : I → X) : φ x = fun j ↦ x (e.symm j) := by
    funext j
    simp [φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  simpa only [hφ] using (hmp.integral_comp' F).symm

/-- Complex-valued simultaneous Fubini over a finite family of coordinate
blocks. -/
private theorem integral_piSigma_prod_blocks_complex
    {K : Type*} [Fintype K]
    {J : K → Type*} [∀ k, Fintype (J k)]
    {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ]
    (f : (k : K) → (J k → T) → ℂ) :
    (∫ x : (Σ k, J k) → T,
        ∏ k : K, f k (fun j ↦ x ⟨k, j⟩)
        ∂Measure.pi (fun _ : Σ k, J k ↦ μ)) =
      ∏ k : K,
        ∫ y : J k → T, f k y
          ∂Measure.pi (fun _ : J k ↦ μ) := by
  let e : (((Σ k, J k) → T) ≃ᵐ ((k : K) → J k → T)) :=
    MeasurableEquiv.piCurry (fun _ _ ↦ T)
  have hmap :
      (Measure.pi (fun _ : Σ k, J k ↦ μ)).map e =
        Measure.pi (fun k : K ↦ Measure.pi (fun _ : J k ↦ μ)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry
        (μ := fun (k : K) (_j : J k) ↦ μ))
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Σ k, J k ↦ μ))
      (Measure.pi (fun k : K ↦ Measure.pi (fun _ : J k ↦ μ))) :=
    ⟨e.measurable, hmap⟩
  calc
    _ = ∫ y : (k : K) → J k → T,
        ∏ k : K, f k (y k)
        ∂Measure.pi (fun k : K ↦ Measure.pi (fun _ : J k ↦ μ)) := by
      exact hmp.integral_comp' (fun y ↦ ∏ k : K, f k (y k))
    _ = _ := integral_fintype_prod_eq_prod f

/-- Complex-valued version of simultaneous branch/component Fubini. -/
private theorem integral_core_component_blocks_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    [∀ C : (twoGraph G).ConnectedComponent, Fintype C]
    {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ]
    (B : (coreBranchIndex G → T) → ℂ)
    (F : (C : (twoGraph G).ConnectedComponent) →
      (coreBranchIndex G → T) → (C → T) → ℂ)
    (hInt : Integrable
      (fun p : (coreBranchIndex G → T) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → T) ↦
        B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
          F C p.1 (fun j ↦ p.2 ⟨C, j⟩))
      ((Measure.pi (fun _ : coreBranchIndex G ↦ μ)).prod
        (Measure.pi
          (fun _ : Σ C : (twoGraph G).ConnectedComponent, C ↦ μ)))) :
    (∫ x : V → T,
      B (coreCoordinateMeasurableEquiv G x).1 *
        ∏ C : (twoGraph G).ConnectedComponent,
          F C (coreCoordinateMeasurableEquiv G x).1
            (fun j ↦ (coreCoordinateMeasurableEquiv G x).2 ⟨C, j⟩)
      ∂Measure.pi (fun _ : V ↦ μ)) =
      ∫ b : coreBranchIndex G → T,
        B b * ∏ C : (twoGraph G).ConnectedComponent,
          (∫ y : C → T, F C b y
            ∂Measure.pi (fun _ : C ↦ μ))
        ∂Measure.pi (fun _ : coreBranchIndex G ↦ μ) := by
  have hmp := coreCoordinate_measurePreserving G μ
  calc
    _ = ∫ p : (coreBranchIndex G → T) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → T),
        B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
          F C p.1 (fun j ↦ p.2 ⟨C, j⟩)
        ∂((Measure.pi (fun _ : coreBranchIndex G ↦ μ)).prod
          (Measure.pi
            (fun _ : Σ C : (twoGraph G).ConnectedComponent, C ↦ μ))) := by
      exact hmp.integral_comp'
        (fun p : (coreBranchIndex G → T) ×
            ((Σ C : (twoGraph G).ConnectedComponent, C) → T) ↦
          B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
            F C p.1 (fun j ↦ p.2 ⟨C, j⟩))
    _ = ∫ b : coreBranchIndex G → T,
          ∫ p : (Σ C : (twoGraph G).ConnectedComponent, C) → T,
            B b * ∏ C : (twoGraph G).ConnectedComponent,
              F C b (fun j ↦ p ⟨C, j⟩)
            ∂Measure.pi
              (fun _ : Σ C : (twoGraph G).ConnectedComponent, C ↦ μ)
          ∂Measure.pi (fun _ : coreBranchIndex G ↦ μ) := by
      exact integral_prod _ hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [integral_const_mul,
        integral_piSigma_prod_blocks_complex μ (fun C ↦ F C b)]

/-- Exact conditional decomposition of one fixed complex-profile core
weight into its branch block and the independently integrated degree-two
components. -/
theorem finiteComplexGraphWeight_eq_integral_complexProfileCoreFactors
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (s₀ : S) :
    finiteComplexGraphWeight M tau G =
      ∫ b : coreBranchIndex G → S,
        complexProfileCoreBranchFactor M tau G s₀ b *
          ∏ C : (twoGraph G).ConnectedComponent,
            (∫ y : C → S,
              complexProfileCoreComponentFactor M tau G s₀ C b y
              ∂Measure.pi (fun _ : C ↦ M.mu))
        ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu) := by
  let e := coreCoordinateMeasurableEquiv G (S := S)
  let μB := Measure.pi (fun _ : coreBranchIndex G ↦ M.mu)
  let μC := Measure.pi
    (fun _ : Σ C : (twoGraph G).ConnectedComponent, C ↦ M.mu)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin k ↦ M.mu)) (μB.prod μC) :=
    coreCoordinate_measurePreserving G M.mu
  have hbase : Integrable (finiteComplexGraphIntegrand M tau G)
      (Measure.pi (fun _ : Fin k ↦ M.mu)) :=
    (continuous_finiteComplexGraphIntegrand M tau G).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hcoord : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S) ↦
        finiteComplexGraphIntegrand M tau G (e.symm p))
      (μB.prod μC) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hbase
  have hfactor (p : (coreBranchIndex G → S) ×
      ((Σ C : (twoGraph G).ConnectedComponent, C) → S)) :
      finiteComplexGraphIntegrand M tau G (e.symm p) =
        complexProfileCoreBranchFactor M tau G s₀ p.1 *
          ∏ C : (twoGraph G).ConnectedComponent,
            complexProfileCoreComponentFactor M tau G s₀ C p.1
              (fun c ↦ p.2 ⟨C, c⟩) := by
    simpa only [e, MeasurableEquiv.apply_symm_apply] using
      finiteComplexGraphIntegrand_eq_complexProfileCoreFactors
        M tau G s₀ (e.symm p)
  have hInt : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S) ↦
        complexProfileCoreBranchFactor M tau G s₀ p.1 *
          ∏ C : (twoGraph G).ConnectedComponent,
            complexProfileCoreComponentFactor M tau G s₀ C p.1
              (fun c ↦ p.2 ⟨C, c⟩))
      (μB.prod μC) := by
    refine hcoord.congr ?_
    filter_upwards [] with p
    exact hfactor p
  unfold finiteComplexGraphWeight
  rw [show (∫ x : Fin k → S, finiteComplexGraphIntegrand M tau G x
      ∂Measure.pi (fun _ : Fin k ↦ M.mu)) =
      ∫ x : Fin k → S,
        complexProfileCoreBranchFactor M tau G s₀
            (coreCoordinateMeasurableEquiv G x).1 *
          ∏ C : (twoGraph G).ConnectedComponent,
            complexProfileCoreComponentFactor M tau G s₀ C
              (coreCoordinateMeasurableEquiv G x).1
              (fun c ↦ (coreCoordinateMeasurableEquiv G x).2 ⟨C, c⟩)
        ∂Measure.pi (fun _ : Fin k ↦ M.mu) by
    apply integral_congr_ae
    filter_upwards [] with x
    exact finiteComplexGraphIntegrand_eq_complexProfileCoreFactors
      M tau G s₀ x]
  exact integral_core_component_blocks_complex G M.mu
    (complexProfileCoreBranchFactor M tau G s₀)
    (complexProfileCoreComponentFactor M tau G s₀) hInt

/-- At length zero, using the canonical order of an unordered endpoint pair
recovers its symmetric complex kernel factor. -/
theorem profilePathEdgeCoefficient_zero_eq_complexKernelEdgeFactor
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {n : ℕ} (x : Fin n → S) (z : Sym2 (Fin n)) :
    profilePathEdgeCoefficient M tau
        (x (Sym2.sortEquiv z).1.1)
        (x (Sym2.sortEquiv z).1.2) 0 =
      complexKernelEdgeFactor M x z := by
  induction z using Sym2.inductionOn with
  | _ i j =>
      rcases le_total i j with hij | hji
      · change (M.kernel (x (i ⊓ j)) (x (i ⊔ j)) : ℂ) =
          (M.kernel (x i) (x j) : ℂ)
        rw [inf_eq_left.mpr hij, sup_eq_right.mpr hij]
      · change (M.kernel (x (i ⊓ j)) (x (i ⊔ j)) : ℂ) =
          (M.kernel (x i) (x j) : ℂ)
        rw [inf_eq_right.mpr hji, sup_eq_left.mpr hji]
        exact congrArg (fun r : ℝ ↦ (r : ℂ))
          (M.kernel.symmetric (x j) (x i))

/-- A direct branch edge is the length-zero generic path coefficient on
the corresponding suppressed-kernel endpoint pair. -/
theorem profilePathEdgeCoefficient_kernelBranchEndpoints_inr
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (d : {e // e ∈ directBranchEdges G}) {nv : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin nv)
    (b : coreBranchIndex G → S) :
    profilePathEdgeCoefficient M tau
        ((fun i ↦ b ((coreBranchEquivBranching G hmin).symm
          (eB.symm i)))
          (Sym2.sortEquiv
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G)))).1.1)
        ((fun i ↦ b ((coreBranchEquivBranching G hmin).symm
          (eB.symm i)))
          (Sym2.sortEquiv
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G)))).1.2) 0 =
      complexKernelEdgeFactor M (coreBranchAssemble G s₀ b) d.val := by
  let eD : KernelEdgeLabel G := Sum.inr d
  let z := kernelBranchEndpoints G hmin hacyc eD
  have hmap : Sym2.map Subtype.val z = d.val := by
    calc
      Sym2.map Subtype.val z = kernelEdgeEndpoints G hacyc eD :=
        kernelBranchEndpoints_map_val G hmin hacyc eD
      _ = d.val := rfl
  change profilePathEdgeCoefficient M tau
      ((fun i ↦ b ((coreBranchEquivBranching G hmin).symm
        (eB.symm i)))
        (Sym2.sortEquiv (Sym2.map eB z)).1.1)
      ((fun i ↦ b ((coreBranchEquivBranching G hmin).symm
        (eB.symm i)))
        (Sym2.sortEquiv (Sym2.map eB z)).1.2) 0 = _
  calc
    _ = complexKernelEdgeFactor M
          (fun i ↦ b ((coreBranchEquivBranching G hmin).symm
            (eB.symm i)))
          (Sym2.map eB z) :=
      profilePathEdgeCoefficient_zero_eq_complexKernelEdgeFactor M tau _ _
    _ = complexKernelEdgeFactor M (coreBranchAssemble G s₀ b) d.val := by
      revert hmap
      induction z using Sym2.inductionOn with
      | _ i j =>
          intro hmap
          have hd : d.val = s(i.val, j.val) := by
            change Sym2.map Subtype.val s(i, j) = d.val at hmap
            rw [Sym2.map_mk] at hmap
            exact hmap.symm
          rw [hd]
          simp only [Sym2.map_mk, complexKernelEdgeFactor_mk,
            Equiv.symm_apply_apply]
          have hi : coreBranchAssemble G s₀ b i.val =
              b ((coreBranchEquivBranching G hmin).symm i) := by
            rw [coreBranchAssemble_branch G s₀ b i.val
              ((coreBranchEquivBranching G hmin).symm i).property]
            congr 1
          have hj : coreBranchAssemble G s₀ b j.val =
              b ((coreBranchEquivBranching G hmin).symm j) := by
            rw [coreBranchAssemble_branch G s₀ b j.val
              ((coreBranchEquivBranching G hmin).symm j).property]
            congr 1
          rw [hi, hj]

/-- After relabelling the actual branch vertices, the branch factor is the
product of the branch profile and the length-zero generic coefficients of
all direct suppressed-kernel edges. -/
theorem complexProfileCoreBranchFactor_relabel_eq_kernelFactors
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) {nv : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin nv)
    (x : Fin nv → S) :
    complexProfileCoreBranchFactor M tau G s₀
        (fun b ↦ x (eB (coreBranchEquivBranching G hmin b))) =
      (∏ i : Fin nv, tau (x i)) *
        ∏ d : {e // e ∈ directBranchEdges G},
          profilePathEdgeCoefficient M tau
            (x (Sym2.sortEquiv
              (Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.1)
            (x (Sym2.sortEquiv
              (Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.2) 0 := by
  classical
  let b : coreBranchIndex G → S :=
    fun c ↦ x (eB (coreBranchEquivBranching G hmin c))
  have hvfilter :
      (Finset.univ : Finset (Fin k)).filter
          (fun v ↦ coreVertexOwner G v = none) =
        branchingVertices G := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact coreVertexOwner_none_iff_branch G hmin v
  have hefilter :
      G.edgeFinset.filter (fun e ↦ coreEdgeOwner G e = none) =
        directBranchEdges G := by
    apply Finset.Subset.antisymm
    · intro e he
      have heG := (Finset.mem_filter.mp he).1
      exact (coreEdgeOwner_none_iff_direct G hmin heG).mp
        (Finset.mem_filter.mp he).2
    · intro e hd
      have heG := directBranchEdges_subset_edgeFinset G hd
      exact Finset.mem_filter.mpr
        ⟨heG, (coreEdgeOwner_none_iff_direct G hmin heG).mpr hd⟩
  have hv :
      (∏ v ∈ branchingVertices G,
          tau (coreBranchAssemble G s₀ b v)) =
        ∏ i : Fin nv, tau (x i) := by
    calc
      _ = ∏ z : (branchingVertices G : Set (Fin k)),
          tau (coreBranchAssemble G s₀ b z.val) := by
        exact Finset.prod_subtype (branchingVertices G)
          (fun _ ↦ Iff.rfl)
          (fun v ↦ tau (coreBranchAssemble G s₀ b v))
      _ = ∏ z : (branchingVertices G : Set (Fin k)),
          tau (x (eB z)) := by
        apply Finset.prod_congr rfl
        intro z hz
        rw [coreBranchAssemble_branch G s₀ b z.val
          ((coreBranchEquivBranching G hmin).symm z).property]
        change tau (x (eB (coreBranchEquivBranching G hmin
          ((coreBranchEquivBranching G hmin).symm z)))) = tau (x (eB z))
        rw [Equiv.apply_symm_apply]
      _ = _ := by
        exact Fintype.prod_equiv eB
          (fun z : (branchingVertices G : Set (Fin k)) ↦ tau (x (eB z)))
          (fun i : Fin nv ↦ tau (x i))
          (fun _ ↦ rfl)
  have he :
      (∏ e ∈ directBranchEdges G,
          complexKernelEdgeFactor M (coreBranchAssemble G s₀ b) e) =
        ∏ d : {e // e ∈ directBranchEdges G},
          profilePathEdgeCoefficient M tau
            (x (Sym2.sortEquiv
              (Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.1)
            (x (Sym2.sortEquiv
              (Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc
                  (Sum.inr d : KernelEdgeLabel G)))).1.2) 0 := by
    calc
      _ = ∏ d : {e // e ∈ directBranchEdges G},
          complexKernelEdgeFactor M (coreBranchAssemble G s₀ b) d.val := by
        exact Finset.prod_subtype (directBranchEdges G)
          (fun _ ↦ Iff.rfl)
          (fun e ↦ complexKernelEdgeFactor M
            (coreBranchAssemble G s₀ b) e)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro d hd
        simpa [b] using
          (profilePathEdgeCoefficient_kernelBranchEndpoints_inr
            M tau G hmin hacyc s₀ d eB b).symm
  change complexProfileCoreBranchFactor M tau G s₀ b = _
  unfold complexProfileCoreBranchFactor complexCoreBranchBlock
  rw [hvfilter, hefilter, hv, he]

/-- Product of the two complex kernel factors at the actual boundary stubs
of one degree-two component. -/
def complexProfileCoreComponentBoundaryFactor
    (M : CompactBJRModel S) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) : ℂ :=
  ∏ q : {q // q ∈ componentBoundaryStubs G C},
    (M.kernel (y q.val.1)
      (coreComponentAssemble G s₀ C b y q.val.2) : ℂ)

/-- One complex-profile component block is its internal induced-graph
integrand times its two actual boundary kernel factors. -/
theorem complexProfileCoreComponentFactor_eq_internal_mul_boundary
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C → S) :
    complexProfileCoreComponentFactor M tau G s₀ C b y =
      finiteComplexGraphIntegrand M tau C.toSimpleGraph y *
        complexProfileCoreComponentBoundaryFactor M G s₀ C b y := by
  let A := coreComponentAssemble G s₀ C b y
  have hv :
      (∏ v ∈ (Finset.univ : Finset (Fin k)).filter
          (fun v ↦ coreVertexOwner G v = some C), tau (A v)) =
        ∏ c : C, tau (y c) := by
    rw [coreComponentVertices_eq G C]
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro c hc
      exact congrArg tau (coreComponentAssemble_component G s₀ C b y c)
    · intro x hx z hz h
      exact Subtype.ext (Subtype.ext h)
  have hi :
      (∏ e ∈ componentInternalEdges G C,
          complexKernelEdgeFactor M A e) =
        ∏ e ∈ C.toSimpleGraph.edgeFinset,
          complexKernelEdgeFactor M y e := by
    unfold componentInternalEdges
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e he
    induction e using Sym2.inductionOn with
    | _ x z =>
        change complexKernelEdgeFactor M A s(x.val.val, z.val.val) =
          (M.kernel (y x) (y z) : ℂ)
        rw [complexKernelEdgeFactor_mk]
        have hx : A x.val.val = y x :=
          coreComponentAssemble_component G s₀ C b y x
        have hz : A z.val.val = y z :=
          coreComponentAssemble_component G s₀ C b y z
        rw [hx, hz]
  have hbdy :
      (∏ e ∈ componentBoundaryEdges G C,
          complexKernelEdgeFactor M A e) =
        complexProfileCoreComponentBoundaryFactor M G s₀ C b y := by
    unfold componentBoundaryEdges complexProfileCoreComponentBoundaryFactor
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro q hq
    rcases q with ⟨⟨x, d⟩, hxd⟩
    change complexKernelEdgeFactor M A s(x.val.val, d) =
      (M.kernel (y x) (coreComponentAssemble G s₀ C b y d) : ℂ)
    rw [complexKernelEdgeFactor_mk]
    have hx : A x.val.val = y x :=
      coreComponentAssemble_component G s₀ C b y x
    rw [hx]
  unfold complexProfileCoreComponentFactor complexCoreComponentBlock
  rw [coreComponentEdges_eq_incident G C,
    component_incident_edges_eq_internal_union_boundary G C,
    Finset.prod_union
      (componentInternalEdges_disjoint_componentBoundaryEdges G C),
    hv, hi, hbdy]
  unfold finiteComplexGraphIntegrand complexKernelEdgeFactor
  ring

/-- With a fixed Hamilton order and fixed boundary stubs, the literal
component block is exactly the standard complex-profile path observable. -/
theorem complexProfileCoreComponentFactor_reindexed_eq_pathObservable
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k n : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1)
    (x : Fin (n + 1) → S) :
    complexProfileCoreComponentFactor M tau G s₀ C b
        (fun c ↦ x (e.symm c)) =
      complexProfilePathObservable M tau n
        (b (componentBoundaryStubBranchIndex G C qL))
        (b (componentBoundaryStubBranchIndex G C qR)) x := by
  let y : C → S := fun c ↦ x (e.symm c)
  let A := coreComponentAssemble G s₀ C b y
  have hcard : Fintype.card
      {q // q ∈ componentBoundaryStubs G C} = 2 := by
    rw [Fintype.card_coe]
    exact componentBoundaryStubs_card_eq_two G hacyc C
  have hpair : (Finset.univ : Finset
      {q // q ∈ componentBoundaryStubs G C}) = {qL, qR} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.subset_univ _
    · rw [Finset.card_pair hne, Finset.card_univ, hcard]
  have hint : finiteComplexGraphIntegrand M tau C.toSimpleGraph y =
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) x := by
    have hiso := finiteComplexGraphIntegrand_iso M tau
      (SimpleGraph.pathGraph (n + 1)) C.toSimpleGraph e y
    have hfun : y ∘ e = x := by
      funext i
      simp [y]
    rw [hfun] at hiso
    exact hiso.symm
  rw [complexProfileCoreComponentFactor_eq_internal_mul_boundary
    M tau G s₀ C b y, hint]
  have hbdy :
      complexProfileCoreComponentBoundaryFactor M G s₀ C b y =
        (M.kernel (x 0) (A qL.val.2) : ℂ) *
          (M.kernel (x (Fin.last n)) (A qR.val.2) : ℂ) := by
    unfold complexProfileCoreComponentBoundaryFactor
    change (∏ q : {q // q ∈ componentBoundaryStubs G C},
      (M.kernel (y q.val.1) (A q.val.2) : ℂ)) = _
    rw [hpair]
    simp only [Finset.prod_pair hne]
    have hyL : y qL.val.1 = x 0 := by simp [y, ← hL]
    have hyR : y qR.val.1 = x (Fin.last n) := by simp [y, ← hR]
    rw [hyL, hyR]
  have hAL : A qL.val.2 =
      b (componentBoundaryStubBranchIndex G C qL) :=
    coreComponentAssemble_boundaryStub G s₀ C b y qL
  have hAR : A qR.val.2 =
      b (componentBoundaryStubBranchIndex G C qR) :=
    coreComponentAssemble_boundaryStub G s₀ C b y qR
  rw [hbdy, hAL, hAR]
  change _ =
    (M.kernel
      (b (componentBoundaryStubBranchIndex G C qL)) (x 0) : ℂ) *
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) x *
      (M.kernel (x (Fin.last n))
        (b (componentBoundaryStubBranchIndex G C qR)) : ℂ)
  rw [M.kernel.symmetric
    (b (componentBoundaryStubBranchIndex G C qL)) (x 0)]
  ring

/-- The conditional integral of one actual degree-two component is the
generic path-edge coefficient at its actual number of vertices. -/
theorem integral_complexProfileCoreComponentFactor_eq_pathEdgeCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k n : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1) :
    (∫ y : C → S,
        complexProfileCoreComponentFactor M tau G s₀ C b y
        ∂Measure.pi (fun _ : C ↦ M.mu)) =
      profilePathEdgeCoefficient M tau
        (b (componentBoundaryStubBranchIndex G C qL))
        (b (componentBoundaryStubBranchIndex G C qR)) (n + 1) := by
  rw [integral_pi_reindex_complex_local M.mu e.toEquiv
    (complexProfileCoreComponentFactor M tau G s₀ C b)]
  change
    (∫ x : Fin (n + 1) → S,
      complexProfileCoreComponentFactor M tau G s₀ C b
        (fun c ↦ x (e.symm c))
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) = _
  rw [show (∫ x : Fin (n + 1) → S,
      complexProfileCoreComponentFactor M tau G s₀ C b
        (fun c ↦ x (e.symm c))
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) =
      ∫ x : Fin (n + 1) → S,
        complexProfilePathObservable M tau n
          (b (componentBoundaryStubBranchIndex G C qL))
          (b (componentBoundaryStubBranchIndex G C qR)) x
        ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu) by
    apply integral_congr_ae
    filter_upwards [] with x
    exact complexProfileCoreComponentFactor_reindexed_eq_pathObservable
      M tau G hacyc s₀ C b e qL qR hne hL hR x]
  change complexProfilePathWeight M tau (n + 1)
      (b (componentBoundaryStubBranchIndex G C qL))
      (b (componentBoundaryStubBranchIndex G C qR)) = _
  exact complexProfilePathWeight_eq_profilePathEdgeCoefficient M tau _ _ _

/-- Fixed branch coordinates: integrating all actual degree-two components
gives exactly the product of their generic path-edge coefficients. -/
theorem prod_integral_complexProfileCoreComponentFactors_eq_pathEdges
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (hacyc : (twoGraph G).IsAcyclic) (s₀ : S)
    (b : coreBranchIndex G → S)
    (n : (twoGraph G).ConnectedComponent → ℕ)
    (e : (C : (twoGraph G).ConnectedComponent) →
      SimpleGraph.pathGraph (n C + 1) ≃g C.toSimpleGraph)
    (qL qR : ∀ C : (twoGraph G).ConnectedComponent,
      {q // q ∈ componentBoundaryStubs G C})
    (hne : ∀ C, qL C ≠ qR C)
    (hL : ∀ C, e C 0 = (qL C).val.1)
    (hR : ∀ C, e C (Fin.last (n C)) = (qR C).val.1) :
    (∏ C : (twoGraph G).ConnectedComponent,
        ∫ y : C → S,
          complexProfileCoreComponentFactor M tau G s₀ C b y
          ∂Measure.pi (fun _ : C ↦ M.mu)) =
      ∏ C : (twoGraph G).ConnectedComponent,
        profilePathEdgeCoefficient M tau
          (b (componentBoundaryStubBranchIndex G C (qL C)))
          (b (componentBoundaryStubBranchIndex G C (qR C)))
          (n C + 1) := by
  apply Finset.prod_congr rfl
  intro C hC
  exact integral_complexProfileCoreComponentFactor_eq_pathEdgeCoefficient
    M tau G hacyc s₀ C b (e C) (qL C) (qR C)
      (hne C) (hL C) (hR C)

/-- Exact fixed-core/profile composition after explicit path orders and
boundary stubs have been selected.  This is the desired branch-profile
factor times generic path-edge coefficients, before any outer regrouping by
kernel isomorphism class. -/
theorem finiteComplexGraphWeight_eq_integral_branch_mul_pathEdgeCoefficients
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (hacyc : (twoGraph G).IsAcyclic) (s₀ : S)
    (n : (twoGraph G).ConnectedComponent → ℕ)
    (e : (C : (twoGraph G).ConnectedComponent) →
      SimpleGraph.pathGraph (n C + 1) ≃g C.toSimpleGraph)
    (qL qR : ∀ C : (twoGraph G).ConnectedComponent,
      {q // q ∈ componentBoundaryStubs G C})
    (hne : ∀ C, qL C ≠ qR C)
    (hL : ∀ C, e C 0 = (qL C).val.1)
    (hR : ∀ C, e C (Fin.last (n C)) = (qR C).val.1) :
    finiteComplexGraphWeight M tau G =
      ∫ b : coreBranchIndex G → S,
        complexProfileCoreBranchFactor M tau G s₀ b *
          ∏ C : (twoGraph G).ConnectedComponent,
            profilePathEdgeCoefficient M tau
              (b (componentBoundaryStubBranchIndex G C (qL C)))
              (b (componentBoundaryStubBranchIndex G C (qR C)))
              (n C + 1)
        ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu) := by
  rw [finiteComplexGraphWeight_eq_integral_complexProfileCoreFactors
    M tau G s₀]
  apply integral_congr_ae
  filter_upwards [] with b
  congr 1
  apply Finset.prod_congr rfl
  intro C hC
  exact integral_complexProfileCoreComponentFactor_eq_pathEdgeCoefficient
    M tau G hacyc s₀ C b (e C) (qL C) (qR C)
      (hne C) (hL C) (hR C)

/-- Coefficient-level form for the existing fixed-core profile composition:
on the monomial profile `X * C tau`, its unique degree-`k` core term is the
same explicit branch/path-coefficient integral. -/
theorem fixedCoreProfileCompositionSeries_X_mul_C_coeff_eq_branch_paths
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (hacyc : (twoGraph G).IsAcyclic) (s₀ : S)
    (n : (twoGraph G).ConnectedComponent → ℕ)
    (e : (C : (twoGraph G).ConnectedComponent) →
      SimpleGraph.pathGraph (n C + 1) ≃g C.toSimpleGraph)
    (qL qR : ∀ C : (twoGraph G).ConnectedComponent,
      {q // q ∈ componentBoundaryStubs G C})
    (hne : ∀ C, qL C ≠ qR C)
    (hL : ∀ C, e C 0 = (qL C).val.1)
    (hR : ∀ C, e C (Fin.last (n C)) = (qR C).val.1) :
    PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M
          (PowerSeries.X * PowerSeries.C tau) G) =
      ∫ b : coreBranchIndex G → S,
        complexProfileCoreBranchFactor M tau G s₀ b *
          ∏ C : (twoGraph G).ConnectedComponent,
            profilePathEdgeCoefficient M tau
              (b (componentBoundaryStubBranchIndex G C (qL C)))
              (b (componentBoundaryStubBranchIndex G C (qR C)))
              (n C + 1)
        ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu) := by
  rw [fixedCoreProfileCompositionSeries_X_mul_C_coeff]
  exact finiteComplexGraphWeight_eq_integral_branch_mul_pathEdgeCoefficients
    M tau G hacyc s₀ n e qL qR hne hL hR

/-- Full analytic form of the bridge.  If `tau(z)` has Taylor series `p`,
then the actual branch-profile/path-coefficient expression for the fixed
core has exactly `fixedCoreProfileCompositionSeries` as its Taylor series.
Thus all coefficients, not only the monomial specialization above, are
identified without introducing heterogeneous path weights as an assumption. -/
theorem integral_branch_mul_pathEdgeCoefficients_hasFPowerSeriesAt
    (M : CompactBJRModel S)
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (hacyc : (twoGraph G).IsAcyclic) (s₀ : S)
    (n : (twoGraph G).ConnectedComponent → ℕ)
    (e : (C : (twoGraph G).ConnectedComponent) →
      SimpleGraph.pathGraph (n C + 1) ≃g C.toSimpleGraph)
    (qL qR : ∀ C : (twoGraph G).ConnectedComponent,
      {q // q ∈ componentBoundaryStubs G C})
    (hne : ∀ C, qL C ≠ qR C)
    (hL : ∀ C, e C 0 = (qL C).val.1)
    (hR : ∀ C, e C (Fin.last (n C)) = (qR C).val.1)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun z ↦
        ∫ b : coreBranchIndex G → S,
          complexProfileCoreBranchFactor M (tau z) G s₀ b *
            ∏ C : (twoGraph G).ConnectedComponent,
              profilePathEdgeCoefficient M (tau z)
                (b (componentBoundaryStubBranchIndex G C (qL C)))
                (b (componentBoundaryStubBranchIndex G C (qR C)))
                (n C + 1)
          ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu))
      (oneDimensionalFormalMultilinearSeries
        (fixedCoreProfileCompositionSeries M
          (oneDimensionalPowerSeries p) G)) 0 := by
  have hseries :=
    finiteComplexGraphWeight_hasFPowerSeriesAt_profileComposition
      M G hp hp0
  have hfun :
      (fun z ↦ finiteComplexGraphWeight M (tau z) G) =
        (fun z ↦
          ∫ b : coreBranchIndex G → S,
            complexProfileCoreBranchFactor M (tau z) G s₀ b *
              ∏ C : (twoGraph G).ConnectedComponent,
                profilePathEdgeCoefficient M (tau z)
                  (b (componentBoundaryStubBranchIndex G C (qL C)))
                  (b (componentBoundaryStubBranchIndex G C (qR C)))
                  (n C + 1)
            ∂Measure.pi (fun _ : coreBranchIndex G ↦ M.mu)) := by
    funext z
    exact finiteComplexGraphWeight_eq_integral_branch_mul_pathEdgeCoefficients
      M (tau z) G hacyc s₀ n e qL qR hne hL hR
  rw [hfun] at hseries
  exact hseries

end PerronWright.GraphCore
