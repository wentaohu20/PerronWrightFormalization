import PerronWright.Enumeration.FieldAnalytic
import PerronWright.Enumeration.RootedTreeFormalIdentity
import PerronWright.Enumeration.RootedTreeAnalyticBridge
import PerronWright.Analysis.TreeFoldJointChart

/-!
# The actual field-weighted rooted-tree series

This module constructs the type-resolved rooted-tree coefficients
directly from the genuine finite labelled graph integrals, for an arbitrary
complex continuous field.  The coefficient recurrence is not a definition:
the next layer proves it from root deletion and the labelled-tree/branch
decomposition already available in the project.

No assertion is made that the complex-field series converges at its critical
point.  What is needed later is the honest local enumerative germ at `z = 0`
and its analytic continuation to the fold chart.
-/

open MeasureTheory
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

namespace FieldRootedTree

theorem continuousMap_finset_sum_apply
    {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → C(X, ℂ)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ContinuousMap.add_apply, ih]

theorem continuousMap_finset_prod_apply
    {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → C(X, ℂ)) (x : X) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, ContinuousMap.mul_apply, ih]

theorem sum_dite_eq_sum_subtype
    {α R : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid R]
    (p : α → Prop) [DecidablePred p] (f : ∀ a, p a → R) :
    (∑ a : α, if h : p a then f a h else 0) =
      ∑ a : {a // p a}, f a.1 a.2 := by
  classical
  let F : α → R := fun a ↦ if h : p a then f a h else 0
  calc
    _ = ∑ a : α, F a := rfl
    _ = ∑ a ∈ (Finset.univ.filter p), F a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p a <;> simp [F, ha]
    _ = ∑ a : {a // p a}, F a.1 := by
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) F
    _ = _ := by
      apply Fintype.sum_congr
      intro a
      simp [F, a.2]

/-- Reindex a complex-valued integral against an iid finite product law. -/
theorem integral_pi_reindex_complex
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

/-- A finite-graph integrand with an arbitrary complex vertex factor.  This
is the convenient generic form of the field integrand for root deletion. -/
def finiteIntegrand (M : CompactBJRModel S) (q : C(S, ℂ))
    {k : ℕ} (G : SimpleGraph (Fin k)) (x : Fin k → S) : ℂ :=
  (∏ v : Fin k, q (x v)) *
    ∏ e ∈ G.edgeFinset, (M.edgeFactor 1 x e : ℂ)

/-- Generic finite-graph weights are invariant under simultaneous graph and
type-coordinate relabelling. -/
theorem finiteIntegrand_iso (M : CompactBJRModel S) (q : C(S, ℂ))
    {k : ℕ} (G H : SimpleGraph (Fin k))
    (e : G ≃g H) (x : Fin k → S) :
    finiteIntegrand M q G (x ∘ e) = finiteIntegrand M q H x := by
  unfold finiteIntegrand
  congr 1
  · exact Equiv.prod_comp e.toEquiv (fun i : Fin k ↦ q (x i))
  · apply Finset.prod_bijective (GraphCore.sym2Congr e.toEquiv)
    · exact (GraphCore.sym2Congr e.toEquiv).bijective
    · intro a
      induction a using Sym2.inductionOn with
      | _ i j =>
          simp only [GraphCore.sym2Congr_mk, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet]
          exact e.map_adj_iff.symm
    · intro a _
      induction a using Sym2.inductionOn with
      | _ i j => rfl

/-- Insert a fixed root type and regard the remaining-coordinate integral as
a bounded linear map between spaces of continuous functions. -/
def rootSliceCLM (M : CompactBJRModel S) (n : ℕ) (v : Fin (n + 1)) :
    C(Fin (n + 1) → S, ℂ) →L[ℂ] C(S, ℂ) := by
  let μn : Measure (Fin n → S) := Measure.pi (fun _ : Fin n ↦ M.mu)
  let slice : C(Fin (n + 1) → S, ℂ) → C(S, ℂ) := fun f ↦
    ⟨fun x ↦ ∫ z : Fin n → S, f (Fin.insertNth v x z) ∂μn, by
      have hins : Continuous
          (fun p : S × (Fin n → S) ↦
            (Fin.insertNth (α := fun _ ↦ S) v p.1 p.2 : Fin (n + 1) → S)) := by
        apply continuous_pi
        intro j
        by_cases hj : j = v
        · subst j
          simpa only [Fin.insertNth_apply_same] using
            (continuous_fst : Continuous (fun p : S × (Fin n → S) ↦ p.1))
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
          simpa only [Fin.insertNth_apply_succAbove] using
            (show Continuous (fun p : S × (Fin n → S) ↦ p.2 k) by fun_prop)
      have hjoint : Continuous
          (fun p : S × (Fin n → S) ↦ f (Fin.insertNth v p.1 p.2)) :=
        f.continuous.comp hins
      have hc := continuous_parametric_integral_of_continuous
        (μ := μn)
        (f := fun x : S ↦ fun z : Fin n → S ↦ f (Fin.insertNth v x z))
        hjoint isCompact_univ
      simpa only [setIntegral_univ] using hc⟩
  refine LinearMap.mkContinuous
    { toFun := slice
      map_add' := ?_
      map_smul' := ?_ }
    (M.mu.real Set.univ) ?_
  · intro f h
    apply ContinuousMap.ext
    intro x
    change (∫ z : Fin n → S,
      (f + h) (Fin.insertNth v x z) ∂μn) = _
    rw [show (fun z : Fin n → S ↦
        (f + h) (Fin.insertNth v x z)) =
        (fun z ↦ f (Fin.insertNth v x z) + h (Fin.insertNth v x z)) by
          funext z; rfl]
    rw [integral_add]
    · rfl
    · exact (f.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
    · exact (h.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
  · intro c f
    apply ContinuousMap.ext
    intro x
    change (∫ z : Fin n → S,
      (c • f) (Fin.insertNth v x z) ∂μn) =
        c • ∫ z : Fin n → S, f (Fin.insertNth v x z) ∂μn
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
      (integral_smul c (fun z : Fin n → S ↦ f (Fin.insertNth v x z)))
  · intro f
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro x
    calc
      ‖slice f x‖ ≤ ‖f‖ * μn.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards [] with z
        exact f.norm_coe_le_norm (Fin.insertNth v x z)
      _ = M.mu.real Set.univ * ‖f‖ := by simp [μn]

@[simp] theorem rootSliceCLM_apply (M : CompactBJRModel S)
    (n : ℕ) (v : Fin (n + 1)) (f : C(Fin (n + 1) → S, ℂ)) (x : S) :
    rootSliceCLM M n v f x =
      ∫ z : Fin n → S, f (Fin.insertNth v x z)
        ∂Measure.pi (fun _ : Fin n ↦ M.mu) := rfl

/-- The genuine complex-field type profile of one finite labelled graph with
one distinguished vertex. -/
def fixedRootedGraphProfileMap (M : CompactBJRModel S)
    (g : C(S, ℂ)) {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) : C(S, ℂ) :=
  rootSliceCLM M n v (M.complexFieldGraphIntegrand g H)

@[simp] theorem fixedRootedGraphProfileMap_apply
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (x : S) :
    fixedRootedGraphProfileMap M g H v x =
      ∫ z : Fin n → S,
        M.complexFieldGraphIntegrand g H (Fin.insertNth v x z)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu) := rfl

/-- For every fixed rooted finite graph, its genuine profile is entire in
the ambient complex field. -/
theorem analyticAt_fixedRootedGraphProfileMap
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    AnalyticAt ℂ (fun h ↦ fixedRootedGraphProfileMap M h H v) g := by
  exact AnalyticAt.comp ((rootSliceCLM M n v).analyticAt _)
    (M.analyticAt_complexFieldGraphIntegrand H g)

/-- The unnormalised genuine field-weighted labelled-tree profile, with
label `0` as the distinguished root. -/
def numerator (M : CompactBJRModel S) (g : C(S, ℂ))
    (n : ℕ) : C(S, ℂ) :=
  ∑ H : SimpleGraph (Fin (n + 1)),
    if H.IsTree then fixedRootedGraphProfileMap M g H 0 else 0

/-- Factorial-normalised type-resolved coefficient of degree `n+1`. -/
def coefficient (M : CompactBJRModel S) (g : C(S, ℂ))
    (n : ℕ) : C(S, ℂ) :=
  (n.factorial : ℂ)⁻¹ • numerator M g n

theorem analyticAt_numerator (M : CompactBJRModel S)
    (n : ℕ) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h ↦ numerator M h n) g := by
  classical
  unfold numerator
  let F : SimpleGraph (Fin (n + 1)) → C(S, ℂ) → C(S, ℂ) := fun H h ↦
    if H.IsTree then fixedRootedGraphProfileMap M h H 0 else 0
  change AnalyticAt ℂ (fun h : C(S, ℂ) ↦ ∑ H, F H h) g
  have hsum : AnalyticAt ℂ (∑ H, F H) g := by
    apply Finset.analyticAt_sum Finset.univ
    intro H _
    dsimp [F]
    split
    · exact analyticAt_fixedRootedGraphProfileMap M g H 0
    · exact analyticAt_const
  have hfun : (∑ H, F H) = (fun h : C(S, ℂ) ↦ ∑ H, F H h) := by
    funext h
    exact Fintype.sum_apply h F
  rw [← hfun]
  exact hsum

theorem analyticAt_coefficient (M : CompactBJRModel S)
    (n : ℕ) (g : C(S, ℂ)) :
    AnalyticAt ℂ (fun h ↦ coefficient M h n) g := by
  exact (analyticAt_const : AnalyticAt ℂ
    (fun _ : C(S, ℂ) ↦ ((n.factorial : ℂ)⁻¹)) g).smul
      (analyticAt_numerator M n g)

/-- The actual field-weighted rooted-tree formal series.  Its coefficient of
degree `n+1` is the genuine finite graph sum above. -/
def series (M : CompactBJRModel S) (g : C(S, ℂ)) :
    PowerSeries C(S, ℂ) :=
  PowerSeries.X * PowerSeries.mk (coefficient M g)

@[simp] theorem series_coeff_zero (M : CompactBJRModel S)
    (g : C(S, ℂ)) :
    PowerSeries.coeff 0 (series M g) = 0 := by
  simp [series, PowerSeries.coeff_zero_X_mul]

@[simp] theorem series_coeff_succ (M : CompactBJRModel S)
    (g : C(S, ℂ)) (n : ℕ) :
    PowerSeries.coeff (n + 1) (series M g) = coefficient M g n := by
  simp [series, PowerSeries.coeff_succ_X_mul]

/-- The actual one-vertex factor in a complex external field. -/
def vertexFactor (M : CompactBJRModel S) (g : C(S, ℂ)) : C(S, ℂ) :=
  NormedSpace.exp (g - TreeCritical.degree M)

@[simp] theorem vertexFactor_apply (M : CompactBJRModel S)
    (g : C(S, ℂ)) (x : S) :
    vertexFactor M g x =
      Complex.exp (g x - (M.degreeFunction x : ℂ)) := by
  rw [vertexFactor]
  rw [show M.degreeFunction x = M.kernel.degree M.mu x from
    M.kernel.degreeMap_apply M.mu x]
  simpa only [TreeCritical.degree_apply, ContinuousMap.sub_apply,
    ContinuousMap.evalAlgHom_apply,
    ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
      (ContinuousMap.evalCLM ℂ x).continuous
      (g - TreeCritical.degree M)

/-- The formal field-dependent rooted-tree right hand side
`z exp(g-d) exp(KT)`. -/
def formalRHS (M : CompactBJRModel S) (g : C(S, ℂ))
    (F : PowerSeries C(S, ℂ)) : PowerSeries C(S, ℂ) :=
  PowerSeries.X *
    (PowerSeries.C (vertexFactor M g) *
      PowerSeries.subst (M.complexKernelActionPowerSeries F)
        (PowerSeries.exp C(S, ℂ)))

@[simp] theorem formalRHS_coeff_zero (M : CompactBJRModel S)
    (g : C(S, ℂ)) (F : PowerSeries C(S, ℂ)) :
    PowerSeries.coeff 0 (formalRHS M g F) = 0 := by
  simp [formalRHS, PowerSeries.coeff_zero_X_mul]

/-- The generic integrand at the actual field vertex factor is definitionally
the project's complexified graph integrand. -/
theorem complexFieldGraphIntegrand_eq_finiteIntegrand
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) (x : Fin k → S) :
    M.complexFieldGraphIntegrand g H x =
      finiteIntegrand M (vertexFactor M g) H x := by
  classical
  unfold CompactBJRModel.complexFieldGraphIntegrand finiteIntegrand
  simp only [ContinuousMap.coe_mul, Pi.mul_apply, ContinuousMap.prod_apply]
  apply congrArg₂ (fun a b : ℂ ↦ a * b)
  · apply Finset.prod_congr rfl
    intro i _
    rw [vertexFactor_apply]
    let f : C(Fin k → S, ℂ) :=
      ⟨fun y ↦ g (y i) - (M.degreeFunction (y i) : ℂ),
        (g.continuous.comp (continuous_apply i)).sub
          (Complex.continuous_ofReal.comp
            (M.degreeFunction.continuous.comp (continuous_apply i)))⟩
    change NormedSpace.exp f x = _
    calc
      NormedSpace.exp f x = Complex.exp (f x) := by
        simpa only [ContinuousMap.evalAlgHom_apply,
          ← Complex.exp_eq_exp_ℂ] using
          NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
            (ContinuousMap.evalCLM ℂ x).continuous f
      _ = Complex.exp (g (x i) - (M.degreeFunction (x i) : ℂ)) := by
        rfl
  · change (∏ e ∈ H.edgeFinset, (M.edgeFactor 1 x e : ℂ)) = _
    rfl

/-- The field-rooted graph profile can equivalently be written using the
generic finite integrand. -/
theorem fixedRootedGraphProfileMap_eq_finiteIntegrand
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (x : S) :
    fixedRootedGraphProfileMap M g H v x =
      ∫ z : Fin n → S,
        finiteIntegrand M (vertexFactor M g) H (Fin.insertNth v x z)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu) := by
  rw [fixedRootedGraphProfileMap_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  exact complexFieldGraphIntegrand_eq_finiteIntegrand M g H _

/-- The same profile for a graph on an arbitrary nonempty `Fin k`. -/
def fixedRootedFinGraphProfileMap (M : CompactBJRModel S)
    (g : C(S, ℂ)) {k : ℕ} (H : SimpleGraph (Fin k))
    (v : Fin k) : C(S, ℂ) := by
  cases k with
  | zero => exact Fin.elim0 v
  | succ n => exact fixedRootedGraphProfileMap M g H v

/-- Fubini separates a parent-kernel factor from a genuine complex-field
rooted graph profile. -/
theorem parentKernelWeightedGraphIntegral_eq_action
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (root : S) :
    (∫ x : Fin (n + 1) → S,
        (M.kernel root (x v) : ℂ) *
          M.complexFieldGraphIntegrand g H x
        ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) =
      M.kernel.complexAction M.mu
        (fixedRootedGraphProfileMap M g H v) root := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ M.mu) v
  have hcont : Continuous
      (fun x : Fin (n + 1) → S ↦
        (M.kernel root (x v) : ℂ) *
          M.complexFieldGraphIntegrand g H x) := by
    exact (Complex.continuous_ofReal.comp
      (M.kernel.toContinuousMap.continuous.comp
        (continuous_const.prodMk (continuous_apply v)))).mul
          (M.complexFieldGraphIntegrand g H).continuous
  have hf : Integrable
      (fun x : Fin (n + 1) → S ↦
        (M.kernel root (x v) : ℂ) *
          M.complexFieldGraphIntegrand g H x)
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) :=
    hcont.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) ↦
        (M.kernel root ((e.symm p) v) : ℂ) *
          M.complexFieldGraphIntegrand g H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  rw [M.kernel.complexAction_apply]
  calc
    _ = ∫ p : S × (Fin n → S),
          (M.kernel root ((e.symm p) v) : ℂ) *
            M.complexFieldGraphIntegrand g H (e.symm p)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu)) := by
      exact (hmp.symm.integral_comp' _).symm
    _ = ∫ y : S, ∫ z : Fin n → S,
          (M.kernel root y : ℂ) *
            M.complexFieldGraphIntegrand g H (Fin.insertNth v y z)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu) ∂M.mu := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
    _ = ∫ y : S, (M.kernel root y : ℂ) *
          fixedRootedGraphProfileMap M g H v y ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fixedRootedGraphProfileMap_apply, integral_const_mul]

theorem parentKernelWeightedFinGraphIntegral_eq_action
    (M : CompactBJRModel S) (g : C(S, ℂ)) {k : ℕ}
    (H : SimpleGraph (Fin k)) (v : Fin k) (root : S) :
    (∫ x : Fin k → S,
        (M.kernel root (x v) : ℂ) *
          M.complexFieldGraphIntegrand g H x
        ∂Measure.pi (fun _ : Fin k ↦ M.mu)) =
      M.kernel.complexAction M.mu
        (fixedRootedFinGraphProfileMap M g H v) root := by
  cases k with
  | zero => exact Fin.elim0 v
  | succ n =>
      simpa only [fixedRootedFinGraphProfileMap] using
        parentKernelWeightedGraphIntegral_eq_action M g H v root

private theorem finpartition_prod_univ_complex {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (f : Fin n → ℂ) :
    (∏ i : Fin n, f i) = ∏ B ∈ P.parts, ∏ i ∈ B, f i := by
  classical
  calc
    (∏ i : Fin n, f i) = ∏ i ∈ P.parts.biUnion id, f i := by
      rw [P.biUnion_parts]
    _ = ∏ B ∈ P.parts, ∏ i ∈ B, f i :=
      Finset.prod_biUnion P.supIndep.pairwiseDisjoint

/-- The part of a generic field-weighted graph integrand belonging to one
root-deleted connected block, before adjoining the parent edge. -/
def rootlessBlockIntegrand (M : CompactBJRModel S) (q : C(S, ℂ))
    {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x : Fin (n + 1) → S) : ℂ :=
  (∏ i ∈ B, q (x i.succ)) *
    ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
        with e.out.1 ∈ B ∧ e.out.2 ∈ B,
      (M.edgeFactor 1 (fun i ↦ x i.succ) e : ℂ)

/-- Adjoin to a rootless block all edges from the parent root. -/
def rootBlockIntegrand (M : CompactBJRModel S) (q : C(S, ℂ))
    {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x : Fin (n + 1) → S) : ℂ :=
  (∏ i ∈ B, if H.Adj 0 i.succ then
      (M.kernel (x 0) (x i.succ) : ℂ) else 1) *
    rootlessBlockIntegrand M q H B x

private theorem edge_factors_root_block_partition
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (x : Fin (n + 1) → S) :
    (∏ e ∈ H.edgeFinset, (M.edgeFactor 1 x e : ℂ)) =
      ∏ B ∈ (finRootlessPartition n H).parts,
        ((∏ i ∈ B, if H.Adj 0 i.succ then
            (M.kernel (x 0) (x i.succ) : ℂ) else 1) *
          ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
              with e.out.1 ∈ B ∧ e.out.2 ∈ B,
            (M.edgeFactor 1 (fun i ↦ x i.succ) e : ℂ)) := by
  have hEdge := M.zeroTree_edge_factors_root_kernel_partition H x
  have hRoot := M.zeroTree_root_kernel_factors_partition H x
  have hEdgeC := congrArg (fun r : ℝ ↦ (r : ℂ)) hEdge
  have hRootC := congrArg (fun r : ℝ ↦ (r : ℂ)) hRoot
  push_cast at hEdgeC hRootC
  have hcast :
      (∏ B ∈ (finRootlessPartition n H).parts,
          ∏ i ∈ B, (if H.Adj 0 i.succ then
            M.kernel (x 0) (x i.succ) else 1 : ℝ) : ℂ) =
        ∏ B ∈ (finRootlessPartition n H).parts,
          ∏ i ∈ B, if H.Adj 0 i.succ then
            (M.kernel (x 0) (x i.succ) : ℂ) else 1 := by
    apply Finset.prod_congr rfl
    intro B hB
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : H.Adj 0 i.succ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact Complex.ofReal_one
  rw [hEdgeC, hRootC]
  rw [hcast]
  rw [Finset.prod_mul_distrib]

/-- Exact root-block factorisation with an arbitrary complex vertex factor. -/
theorem finiteIntegrand_root_block_partition
    (M : CompactBJRModel S) (q : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (x : Fin (n + 1) → S) :
    finiteIntegrand M q H x = q (x 0) *
      ∏ B ∈ (finRootlessPartition n H).parts,
        rootBlockIntegrand M q H B x := by
  classical
  unfold finiteIntegrand rootBlockIntegrand rootlessBlockIntegrand
  rw [Fin.prod_univ_succ]
  rw [finpartition_prod_univ_complex (finRootlessPartition n H)
    (fun i ↦ q (x i.succ))]
  have hedge := edge_factors_root_block_partition M H x
  change
    (q (x 0) * ∏ B ∈ (finRootlessPartition n H).parts,
        ∏ i ∈ B, q (x i.succ)) *
        (∏ e ∈ H.edgeFinset, (M.edgeFactor 1 x e : ℂ)) = _
  rw [hedge]
  simp_rw [Finset.prod_mul_distrib]
  ring

theorem rootlessBlockIntegrand_congr_on
    (M : CompactBJRModel S) (q : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (B : Finset (Fin n))
    (x y : Fin (n + 1) → S)
    (hxy : ∀ i ∈ B, x i.succ = y i.succ) :
    rootlessBlockIntegrand M q H B x =
      rootlessBlockIntegrand M q H B y := by
  unfold rootlessBlockIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hxy i hi]
  · apply Finset.prod_congr rfl
    intro e he
    have h1 : e.out.1 ∈ B := (Finset.mem_filter.mp he).2.1
    have h2 : e.out.2 ∈ B := (Finset.mem_filter.mp he).2.2
    have hval (v : Fin n) (hv : v ∈ e) : x v.succ = y v.succ := by
      have heq : s(e.out.1, e.out.2) = e := by
        simpa only [Sym2.mk] using e.out_eq
      have hv' : v ∈ s(e.out.1, e.out.2) := by
        exact heq.symm ▸ hv
      rcases Sym2.mem_iff.mp hv' with hv1 | hv2
      · exact hv1.symm ▸ hxy e.out.1 h1
      · exact hv2.symm ▸ hxy e.out.2 h2
    induction e using Sym2.inductionOn with
    | _ a b =>
        have ha := hval a (Sym2.mem_mk_left a b)
        have hb := hval b (Sym2.mem_mk_right a b)
        simp only [CompactBJRModel.edgeFactor_mk, one_mul, ha, hb]

theorem rootBlockIntegrand_congr_on
    (M : CompactBJRModel S) (q : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (B : Finset (Fin n))
    (x y : Fin (n + 1) → S) (hroot : x 0 = y 0)
    (hxy : ∀ i ∈ B, x i.succ = y i.succ) :
    rootBlockIntegrand M q H B x = rootBlockIntegrand M q H B y := by
  unfold rootBlockIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hroot, hxy i hi]
  · exact rootlessBlockIntegrand_congr_on M q H B x y hxy

theorem rootBlockIntegrand_eq_local
    (M : CompactBJRModel S) (q : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (B : Finset (Fin n))
    (root : S) (z : Fin n → S) :
    rootBlockIntegrand M q H B (Fin.cons root z) =
      rootBlockIntegrand M q H B
        (Fin.cons root (extendBlock B root (fun i ↦ z i.1))) := by
  classical
  apply rootBlockIntegrand_congr_on M q H B
  · simp only [Fin.cons_zero]
  · intro i hi
    simp only [Fin.cons_succ, extendBlock, dif_pos hi]

private theorem integral_finpartition_prod_eq_prod_complex
    {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (P : Finpartition (Finset.univ : Finset ι))
    (μ : Measure X) [SigmaFinite μ]
    (F : (B : P.parts) → (B.1 → X) → ℂ) :
    (∫ z : ι → X, ∏ B : P.parts, F B (fun i ↦ z i.1)
      ∂Measure.pi (fun _ : ι ↦ μ)) =
      ∏ B : P.parts, ∫ y : B.1 → X, F B y
        ∂Measure.pi (fun _ : B.1 ↦ μ) := by
  calc
    _ = ∫ u : (B : P.parts) → B.1 → X, ∏ B : P.parts, F B (u B)
        ∂Measure.pi (fun B : P.parts ↦ Measure.pi (fun _ : B.1 ↦ μ)) := by
      rw [← (measurePreserving_finpartitionPi P μ).integral_comp']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z ↦ by
        apply Finset.prod_congr rfl
        intro B _
        congr 1
        funext i
        exact (finpartitionPiMeasurableEquiv_apply P z B i).symm)
    _ = _ := integral_fintype_prod_eq_prod F

/-- Product-measure factorisation of the generic complex field integrand
after fixing the root type. -/
theorem integral_root_block_partition
    (M : CompactBJRModel S) (q : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (root : S) :
    (∫ z : Fin n → S,
        finiteIntegrand M q H (Fin.cons root z)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu)) =
      q root *
        ∏ B : (finRootlessPartition n H).parts,
          ∫ y : B.1 → S,
            rootBlockIntegrand M q H B.1
              (Fin.cons root (extendBlock B.1 root y))
              ∂Measure.pi (fun _ : B.1 ↦ M.mu) := by
  classical
  let P := finRootlessPartition n H
  let F : (B : P.parts) → (B.1 → S) → ℂ := fun B y ↦
    rootBlockIntegrand M q H B.1
      (Fin.cons root (extendBlock B.1 root y))
  have hpoint (z : Fin n → S) :
      finiteIntegrand M q H (Fin.cons root z) =
        q root * ∏ B : P.parts, F B (fun i ↦ z i.1) := by
    rw [finiteIntegrand_root_block_partition M q H (Fin.cons root z)]
    simp only [Fin.cons_zero]
    congr 1
    rw [Finset.prod_subtype P.parts (fun B ↦ Iff.rfl)
      (fun B ↦ rootBlockIntegrand M q H B (Fin.cons root z))]
    apply Finset.prod_congr rfl
    intro B _
    exact rootBlockIntegrand_eq_local M q H B.1 root z
  calc
    _ = ∫ z : Fin n → S,
        q root * ∏ B : P.parts, F B (fun i ↦ z i.1)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = q root * ∫ z : Fin n → S,
        ∏ B : P.parts, F B (fun i ↦ z i.1)
          ∂Measure.pi (fun _ : Fin n ↦ M.mu) := by
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      exact integral_finpartition_prod_eq_prod_complex P M.mu F

/-- The genuine field profile of the relabelled tree in one root-deleted
block, rooted at its unique vertex adjacent to the parent. -/
def relabelledRootBlockProfileMap (M : CompactBJRModel S)
    (g : C(S, ℂ)) {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (i : Fin n) : C(S, ℂ) :=
  fixedRootedFinGraphProfileMap M g
    (finRootlessBlockTreeGraph n H i)
    (((finRootlessPartition n H).part i).equivFin
      ⟨i, (finRootlessPartition n H).mem_part_self.mpr
        (Finset.mem_univ i)⟩)

set_option linter.style.haveILetI false in
theorem tree_rootBlockIntegrand_relabel
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ) (root : S)
    (y : ((finRootlessPartition n H).part i) → S) :
    rootBlockIntegrand M (vertexFactor M g) H
        ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y)) =
      (M.kernel root
          (y ⟨i, (finRootlessPartition n H).mem_part_self.mpr
            (Finset.mem_univ i)⟩) : ℂ) *
        M.complexFieldGraphIntegrand g
          (finRootlessBlockTreeGraph n H i)
          (fun a ↦ y (((finRootlessPartition n H).part i).equivFin.symm a)) := by
  classical
  let P := finRootlessPartition n H
  let B := P.part i
  letI : Fintype B :=
    Subtype.fintype (fun x : Fin n ↦ x ∈ (B : Set (Fin n)))
  have hiB : i ∈ B := P.mem_part_self.mpr (Finset.mem_univ i)
  have hB : B ∈ P.parts := P.part_mem.mpr (Finset.mem_univ i)
  obtain ⟨j, hjB, hjroot, hjprod⟩ :=
    M.tree_root_block_kernel_product_eq_single H hT B hB
  have hji : j = i := by
    obtain ⟨_, _, huniq⟩ :=
      finRootlessPartition_part_existsUnique_root_neighbor H hT B hB
    exact huniq j ⟨hjB, hjroot⟩ |>.trans (huniq i ⟨hiB, hi⟩).symm
  subst j
  have hrootprod := hjprod root (extendBlock B root y)
  have hrootprod' :
      (∏ j ∈ B, if H.Adj 0 j.succ then
          (M.kernel root ((extendBlock B root y) j) : ℂ) else 1) =
        (M.kernel root (y ⟨i, hiB⟩) : ℂ) := by
    have hreal :
        (∏ j ∈ B, if H.Adj 0 j.succ then
            M.kernel root ((extendBlock B root y) j) else 1) =
          M.kernel root (y ⟨i, hiB⟩) := by
      simpa only [extendBlock, dif_pos hiB] using hrootprod
    have hc := congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
    push_cast at hc
    rw [← hc]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases h : H.Adj 0 j.succ
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact Complex.ofReal_one
  have hvert :
      (∏ j ∈ B, vertexFactor M g ((extendBlock B root y) j)) =
        ∏ a : Fin B.card,
          vertexFactor M g (y (B.equivFin.symm a)) := by
    calc
      _ = ∏ b : B, vertexFactor M g ((extendBlock B root y) b.1) := by
        exact Finset.prod_subtype B (fun _ ↦ Iff.rfl) _
      _ = ∏ b : B, vertexFactor M g (y b) := by
        apply Finset.prod_congr rfl
        intro b _
        simp only [extendBlock, dif_pos b.property]
      _ = _ := by
        exact Fintype.prod_equiv B.equivFin
          (fun b : B ↦ vertexFactor M g (y b))
          (fun a : Fin B.card ↦ vertexFactor M g (y (B.equivFin.symm a)))
          (fun b ↦ by simp only [Equiv.symm_apply_apply])
  have hedge :
      (∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
          with e.out.1 ∈ B ∧ e.out.2 ∈ B,
        (M.edgeFactor 1 (extendBlock B root y) e : ℂ)) =
      ∏ e ∈ (finRootlessBlockTreeGraph n H i).edgeFinset,
        (M.edgeFactor 1 (fun a ↦ y (B.equivFin.symm a)) e : ℂ) := by
    let G := H.comap (Fin.succ : Fin n → Fin (n + 1))
    change (∏ e ∈ G.edgeFinset
        with e.out.1 ∈ (B : Set (Fin n)) ∧ e.out.2 ∈ (B : Set (Fin n)),
          _) = _
    rw [← finRootless_block_edgeFinset_eq H (B : Set (Fin n))]
    rw [Finset.prod_map]
    let eSym : Sym2 B ≃ Sym2 (Fin B.card) :=
      { toFun := Sym2.map B.equivFin
        invFun := Sym2.map B.equivFin.symm
        left_inv := by
          intro e
          induction e using Sym2.inductionOn with
          | _ a b => simp only [Sym2.map_mk, Equiv.symm_apply_apply]
        right_inv := by
          intro e
          induction e using Sym2.inductionOn with
          | _ a b => simp only [Sym2.map_mk, Equiv.apply_symm_apply] }
    apply Finset.prod_equiv eSym
    · intro e
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [show eSym s(a, b) = s(B.equivFin a, B.equivFin b) from rfl]
          constructor
          · intro hab
            have hab' : (G.induce (B : Set (Fin n))).Adj a b :=
              (SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hab)
            apply SimpleGraph.mem_edgeFinset.mpr
            apply (SimpleGraph.mem_edgeSet _).mpr
            simpa only [finRootlessBlockTreeGraph, B, P, G,
              SimpleGraph.comap_adj, Equiv.symm_apply_apply,
              Function.Embedding.subtype_apply] using hab'
          · intro hab
            have hab' : (finRootlessBlockTreeGraph n H i).Adj
                (B.equivFin a) (B.equivFin b) :=
              (SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hab)
            apply SimpleGraph.mem_edgeFinset.mpr
            apply (SimpleGraph.mem_edgeSet _).mpr
            simpa only [finRootlessBlockTreeGraph, B, P, G,
              SimpleGraph.comap_adj, Equiv.symm_apply_apply,
              Function.Embedding.subtype_apply] using hab'
    · intro e _
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [show eSym s(a, b) = s(B.equivFin a, B.equivFin b) from rfl]
          change
            (M.edgeFactor 1 (extendBlock B root y) s(a.1, b.1) : ℂ) =
              (M.edgeFactor 1 (fun c ↦ y (B.equivFin.symm c))
                s(B.equivFin a, B.equivFin b) : ℂ)
          simp only [extendBlock, dif_pos a.property, dif_pos b.property,
            Equiv.symm_apply_apply, CompactBJRModel.edgeFactor_mk, one_mul]
  rw [complexFieldGraphIntegrand_eq_finiteIntegrand]
  unfold rootBlockIntegrand rootlessBlockIntegrand finiteIntegrand
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hrootprod']
  change (M.kernel root (y ⟨i, hiB⟩) : ℂ) *
      ((∏ j ∈ B, vertexFactor M g ((extendBlock B root y) j)) * _) =
    (M.kernel root (y ⟨i, hiB⟩) : ℂ) *
      ((∏ a : Fin B.card, vertexFactor M g (y (B.equivFin.symm a))) * _)
  rw [hvert, hedge]

/-- The preceding pointwise relabelling also preserves the product measure. -/
theorem tree_rootBlock_integral_relabel
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ) (root : S) :
    (∫ y : ((finRootlessPartition n H).part i) → S,
      rootBlockIntegrand M (vertexFactor M g) H
        ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y))
        ∂Measure.pi
          (fun _ : ((finRootlessPartition n H).part i) ↦ M.mu)) =
      ∫ z : Fin ((finRootlessPartition n H).part i).card → S,
        (M.kernel root
            (z (((finRootlessPartition n H).part i).equivFin
              ⟨i, (finRootlessPartition n H).mem_part_self.mpr
                (Finset.mem_univ i)⟩)) : ℂ) *
          M.complexFieldGraphIntegrand g
            (finRootlessBlockTreeGraph n H i) z
        ∂Measure.pi
          (fun _ : Fin ((finRootlessPartition n H).part i).card ↦ M.mu) := by
  classical
  let P := finRootlessPartition n H
  let B := P.part i
  have hiB : i ∈ B := P.mem_part_self.mpr (Finset.mem_univ i)
  let e : (Fin B.card → S) ≃ᵐ (B → S) :=
    MeasurableEquiv.piCongrLeft (fun _ : B ↦ S) B.equivFin.symm
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin B.card ↦ M.mu))
      (Measure.pi (fun _ : B ↦ M.mu)) :=
    measurePreserving_piCongrLeft (fun _ : B ↦ M.mu) B.equivFin.symm
  calc
    _ = ∫ z : Fin B.card → S,
        rootBlockIntegrand M (vertexFactor M g) H B
          (Fin.cons root (extendBlock B root (e z)))
          ∂Measure.pi (fun _ : Fin B.card ↦ M.mu) := by
      exact (hmp.integral_comp' _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [tree_rootBlockIntegrand_relabel M g H hT i hi root (e z)]
      have hroot : e z ⟨i, hiB⟩ = z (B.equivFin ⟨i, hiB⟩) := by
        simpa only [Equiv.symm_apply_apply] using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : B ↦ S) B.equivFin.symm z
            (B.equivFin ⟨i, hiB⟩))
      have hcoords : (fun a ↦ e z (B.equivFin.symm a)) = z := by
        funext a
        exact MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : B ↦ S) B.equivFin.symm z a
      rw [hroot, hcoords]

theorem tree_rootBlock_integral_eq_action
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ) (root : S) :
    (∫ y : ((finRootlessPartition n H).part i) → S,
      rootBlockIntegrand M (vertexFactor M g) H
        ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y))
        ∂Measure.pi
          (fun _ : ((finRootlessPartition n H).part i) ↦ M.mu)) =
      M.kernel.complexAction M.mu
        (relabelledRootBlockProfileMap M g H i) root := by
  rw [tree_rootBlock_integral_relabel M g H hT i hi root]
  simpa only [relabelledRootBlockProfileMap] using
    parentKernelWeightedFinGraphIntegral_eq_action M g
      (finRootlessBlockTreeGraph n H i)
      (((finRootlessPartition n H).part i).equivFin
        ⟨i, (finRootlessPartition n H).mem_part_self.mpr
          (Finset.mem_univ i)⟩) root

/-- Relabelling a finite graph and its distinguished root leaves its genuine
complex-field profile unchanged. -/
theorem fixedRootedGraphProfileMap_comap_equiv
    (M : CompactBJRModel S) (g : C(S, ℂ)) {m : ℕ}
    (G : SimpleGraph (Fin (m + 1)))
    (e : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1)) :
    fixedRootedGraphProfileMap M g (G.comap e) v =
      fixedRootedGraphProfileMap M g G (e v) := by
  ext root
  rw [fixedRootedGraphProfileMap_eq_finiteIntegrand,
    fixedRootedGraphProfileMap_eq_finiteIntegrand]
  let q : Fin m ≃ Fin m := rootComplementEquiv e v
  have hcomp (z : Fin m → S) :
      (Fin.insertNth (e v) root (fun j ↦ z (q.symm j))) ∘ e =
        Fin.insertNth v root z := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove v j with rfl | ⟨i, rfl⟩
    · simp only [Function.comp_apply, Fin.insertNth_apply_same]
    · rw [Function.comp_apply, rootComplementEquiv_succAbove]
      simp only [Fin.insertNth_apply_succAbove, q, Equiv.symm_apply_apply]
  have hpoint (z : Fin m → S) :
      finiteIntegrand M (vertexFactor M g) (G.comap e)
          (Fin.insertNth v root z) =
        finiteIntegrand M (vertexFactor M g) G
          (Fin.insertNth (e v) root (fun j ↦ z (q.symm j))) := by
    have hiso := finiteIntegrand_iso M (vertexFactor M g)
      (G.comap e) G (SimpleGraph.Iso.comap e G)
      (Fin.insertNth (e v) root (fun j ↦ z (q.symm j)))
    change finiteIntegrand M (vertexFactor M g) (G.comap e)
        ((Fin.insertNth (e v) root (fun j ↦ z (q.symm j))) ∘ e) =
      finiteIntegrand M (vertexFactor M g) G
        (Fin.insertNth (e v) root (fun j ↦ z (q.symm j))) at hiso
    rw [hcomp] at hiso
    exact hiso
  calc
    _ = ∫ z : Fin m → S,
        finiteIntegrand M (vertexFactor M g) G
          (Fin.insertNth (e v) root (fun j ↦ z (q.symm j)))
        ∂Measure.pi (fun _ : Fin m ↦ M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ y : Fin m → S,
        finiteIntegrand M (vertexFactor M g) G
          (Fin.insertNth (e v) root y)
        ∂Measure.pi (fun _ : Fin m ↦ M.mu) := by
      exact (integral_pi_reindex_complex M.mu q
        (fun y : Fin m → S ↦ finiteIntegrand M (vertexFactor M g) G
          (Fin.insertNth (e v) root y))).symm

theorem sum_tree_fixedRootedGraphProfileMap_eq_root_zero
    (M : CompactBJRModel S) (g : C(S, ℂ)) {m : ℕ}
    (v : Fin (m + 1)) :
    (∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        fixedRootedGraphProfileMap M g H.1 v) =
      ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        fixedRootedGraphProfileMap M g H.1 0 := by
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 v
  let E := treeGraphPermEquiv e
  calc
    _ = ∑ H : {G : SimpleGraph (Fin (m + 1)) // G.IsTree},
        fixedRootedGraphProfileMap M g (E H).1 v := by
      exact (E.sum_comp (fun H ↦ fixedRootedGraphProfileMap M g H.1 v)).symm
    _ = _ := by
      apply Fintype.sum_congr
      intro H
      change fixedRootedGraphProfileMap M g (H.1.comap e.symm) v = _
      rw [fixedRootedGraphProfileMap_comap_equiv M g H.1 e.symm v]
      rw [Equiv.symm_swap, Equiv.swap_apply_right]

/-- The field-weighted profile of one independently labelled root branch. -/
def branchProfileMap (M : CompactBJRModel S) (g : C(S, ℂ))
    {n : ℕ} {B : Finset (Fin n)} (T : LabelledRootBranch B) : C(S, ℂ) :=
  fixedRootedFinGraphProfileMap M g
    (T.graph.comap (B.equivFin.symm : Fin B.card → B))
    (B.equivFin T.root)

theorem treeRootBranch_profileMap_eq_of_root
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) (i : Fin n)
    (hi : ((treeRootBranchDecomposition H hT).2 B).root.1 = i)
    (hpart : (finRootlessPartition n H).part i = B.1) :
    branchProfileMap M g ((treeRootBranchDecomposition H hT).2 B) =
      relabelledRootBlockProfileMap M g H i := by
  let C : (finRootlessPartition n H).parts :=
    ⟨(finRootlessPartition n H).part i,
      (finRootlessPartition n H).part_mem.mpr (Finset.mem_univ i)⟩
  have hCB : C = B := Subtype.ext hpart
  subst B
  have hroot : ((treeRootBranchDecomposition H hT).2 C).root =
      ⟨i, (finRootlessPartition n H).mem_part_self.mpr
        (Finset.mem_univ i)⟩ := by
    apply Subtype.ext
    exact hi
  unfold branchProfileMap relabelledRootBlockProfileMap
  rw [treeRootBranchDecomposition_graph, hroot]
  unfold finRootlessBlockTreeGraph
  rfl

theorem treeRootBranch_profileMap_eq
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (B : (finRootlessPartition n H).parts) :
    branchProfileMap M g ((treeRootBranchDecomposition H hT).2 B) =
      relabelledRootBlockProfileMap M g H
        (finRootlessBranchRoot H hT B) := by
  apply treeRootBranch_profileMap_eq_of_root M g H hT B
  · exact treeRootBranchDecomposition_root_val H hT B
  · exact finRootlessPartition_part_branchRoot H hT B

/-- Exact root decomposition for one genuine field-weighted labelled tree. -/
theorem fixedTreeProfile_eq_rootBranchActions
    (M : CompactBJRModel S) (g : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree) (root : S) :
    fixedRootedGraphProfileMap M g H 0 root =
      vertexFactor M g root *
        ∏ B : (finRootlessPartition n H).parts,
          M.kernel.complexAction M.mu
            (relabelledRootBlockProfileMap M g H
              (finRootlessBranchRoot H hT B)) root := by
  rw [fixedRootedGraphProfileMap_eq_finiteIntegrand]
  simpa only [Fin.insertNth_zero'] using
    (integral_root_block_partition M (vertexFactor M g) H root).trans (by
      congr 1
      apply Fintype.prod_congr
      intro B
      have hpart := finRootlessPartition_part_branchRoot H hT B
      have hadj := finRootlessBranchRoot_adj H hT B
      have hblock := tree_rootBlock_integral_eq_action M g H hT
        (finRootlessBranchRoot H hT B) hadj root
      rw [hpart] at hblock
      exact hblock)

end FieldRootedTree

end PerronWright
