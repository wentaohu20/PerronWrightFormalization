import PerronWright.Enumeration.CoreBranching
import PerronWright.Enumeration.LeafFactor

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- At a degree-two vertex of a simple graph, the two displayed
neighbors account for exactly its two incident edges. -/
theorem degreeTwo_incidenceFinset_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a b : V} (hv : G.degree v = 2)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    G.incidenceFinset v = ({s(v,a), s(v,b)} : Finset (Sym2 V)) := by
  have hne : s(v,a) ≠ s(v,b) := by
    intro h
    exact hab (Sym2.congr_right.mp h)
  have hsub : ({s(v,a), s(v,b)} : Finset (Sym2 V)) ⊆
      G.incidenceFinset v := by
    intro e he
    have hcases : e = s(v,a) ∨ e = s(v,b) := by simpa using he
    rcases hcases with rfl | rfl
    · rw [G.mem_incidenceFinset]
      exact G.mk'_mem_incidenceSet_left_iff.mpr hva
    · rw [G.mem_incidenceFinset]
      exact G.mk'_mem_incidenceSet_left_iff.mpr hvb
  have hcard : (G.incidenceFinset v).card = 2 := by
    simpa only [G.card_incidenceFinset_eq_degree] using hv
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard, hne])).symm

open scoped Classical in
/-- Exact two-edge deletion identity before the degree-two vertex is
suppressed into one multigraph edge. -/
theorem degreeTwo_deleteIncidence_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a b : V} (hv : G.degree v = 2)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    (G.deleteIncidenceSet v).edgeFinset =
      G.edgeFinset \ ({s(v,a), s(v,b)} : Finset (Sym2 V)) := by
  rw [G.edgeFinset_deleteIncidenceSet_eq_sdiff,
    degreeTwo_incidenceFinset_eq_pair G hv hva hvb hab]

open scoped Classical in
/-- A degree-two vertex contributes exactly its vertex factor and two
edge factors, with all other vertices and edges retained literally. -/
theorem degreeTwo_weight_product_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a b : V} (hv : G.degree v = 2)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    {R : Type*} [CommMonoid R] (A : V → R) (B : Sym2 V → R) :
    (∏ x : V, A x) * (∏ e ∈ G.edgeFinset, B e) =
      (A v * B s(v,a) * B s(v,b)) *
        ((∏ x ∈ (Finset.univ.erase v), A x) *
          (∏ e ∈ (G.deleteIncidenceSet v).edgeFinset, B e)) := by
  let P : Finset (Sym2 V) := {s(v,a), s(v,b)}
  have hne : s(v,a) ≠ s(v,b) := by
    intro h
    exact hab (Sym2.congr_right.mp h)
  have hsub : P ⊆ G.edgeFinset := by
    intro e he
    have hcases : e = s(v,a) ∨ e = s(v,b) := by simpa [P] using he
    rcases hcases with rfl | rfl
    · simpa using hva
    · simpa using hvb
  have hE := Finset.prod_sdiff hsub (f := B)
  have hV := Finset.mul_prod_erase (Finset.univ : Finset V) A (Finset.mem_univ v)
  have hdel := degreeTwo_deleteIncidence_edgeFinset G hv hva hvb hab
  have hpair : (∏ e ∈ P, B e) = B s(v,a) * B s(v,b) := by
    simp [P, hne]
  rw [hdel]
  change (∏ x : V, A x) * (∏ e ∈ G.edgeFinset, B e) =
    (A v * B s(v,a) * B s(v,b)) *
      ((∏ x ∈ (Finset.univ.erase v), A x) *
        (∏ e ∈ G.edgeFinset \ P, B e))
  rw [← hV, ← hE, hpair]
  ac_rfl

open scoped Classical in
/-- Specialization to the paper's actual compact-type graph-weight
integrand.  Integration over the degree-two type will turn the product
of the two displayed kernel factors into a path convolution. -/
theorem degreeTwo_graphWeightIntegrand_split
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (H : SimpleGraph (Fin k)) (x : Fin k → S)
    {v a b : Fin k} (hv : H.degree v = 2)
    (hva : H.Adj v a) (hvb : H.Adj v b) (hab : a ≠ b) :
    M.graphWeightIntegrand t H x =
      (Real.exp (-t * M.degreeFunction (x v)) *
        (t * M.kernel (x v) (x a)) * (t * M.kernel (x v) (x b))) *
        ((∏ i ∈ (Finset.univ.erase v),
            Real.exp (-t * M.degreeFunction (x i))) *
          (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
            M.edgeFactor t x e)) := by
  simpa only [CompactBJRModel.graphWeightIntegrand,
    CompactBJRModel.edgeFactor_mk] using
    (degreeTwo_weight_product_split H hv hva hvb hab
      (fun i => Real.exp (-t * M.degreeFunction (x i)))
      (M.edgeFactor t x))

open MeasureTheory

/-- The genuine two-edge path response obtained by integrating its
degree-two internal type.  It is defined from the model's actual kernel,
type law, and vertex isolation factor. -/
def path2Convolution
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a b : S) : ℝ :=
  ∫ y : S, Real.exp (-t * M.degreeFunction y) *
    (t * M.kernel y a) * (t * M.kernel y b) ∂M.mu

/-- The first edge of a two-step path, carrying the internal
vertex's exponential weight on its endpoint. -/
def pathFirstKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : C(S × S, ℝ) :=
  ⟨fun p => (t * M.kernel p.1 p.2) *
    Real.exp (-t * M.degreeFunction p.2), by fun_prop⟩

/-- The second, unweighted edge of a two-step path. -/
def pathSecondKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : C(S × S, ℝ) :=
  ⟨fun p => t * M.kernel p.1 p.2, by fun_prop⟩

/-- The two-step path response is a genuine continuous kernel, given
by the already established composition operation on compact kernels. -/
def path2ContinuousKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : C(S × S, ℝ) :=
  KernelMap.comp M.mu (pathFirstKernel M t) (pathSecondKernel M t)

theorem path2ContinuousKernel_apply
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a b : S) :
    path2ContinuousKernel M t (a, b) = path2Convolution M t a b := by
  rw [path2ContinuousKernel, KernelMap.comp_apply]
  unfold path2Convolution
  apply integral_congr_ae
  filter_upwards [] with y
  change ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
      (t * M.kernel y b) =
    Real.exp (-t * M.degreeFunction y) *
      (t * M.kernel y a) * (t * M.kernel y b)
  rw [M.kernel.symmetric a y]
  ring

theorem path2Convolution_symmetric
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a b : S) :
    path2Convolution M t a b = path2Convolution M t b a := by
  unfold path2Convolution
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem path2ContinuousKernel_symmetric
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a b : S) :
    path2ContinuousKernel M t (a, b) =
      path2ContinuousKernel M t (b, a) := by
  rw [path2ContinuousKernel_apply, path2ContinuousKernel_apply]
  exact path2Convolution_symmetric M t a b

/-- The integrated length-two path may be attached to an unordered
multigraph edge, including loops and parallel edges. -/
def path2EdgeFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {v : ℕ}
    (x : Fin v → S) (e : Sym2 (Fin v)) : ℝ :=
  Sym2.lift ⟨fun i j => path2ContinuousKernel M t (x i, x j), by
    intro i j
    exact path2ContinuousKernel_symmetric M t (x i) (x j)⟩ e

@[simp] theorem path2EdgeFactor_mk
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {v : ℕ}
    (x : Fin v → S) (i j : Fin v) :
    path2EdgeFactor M t x s(i,j) =
      path2Convolution M t (x i) (x j) := by
  simp [path2EdgeFactor, path2ContinuousKernel_apply]

open scoped Classical in
/-- An exact one-vertex degree-two suppression identity for the
original annealed graph weight.  A two-edge path is replaced by the
integrated path kernel between its surviving endpoints; existing
endpoint edges are retained in the residual graph, so this identity
already respects the parallel-edge case relevant to multigraph kernels. -/
theorem graphWeight_degreeTwo_transfer_induced
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1))
    (ja jb : Fin n) (hv : H.degree v = 2)
    (hva : H.Adj v (v.succAbove ja))
    (hvb : H.Adj v (v.succAbove jb)) (hab : ja ≠ jb) :
    M.graphWeight t H =
      ∫ z : Fin n → S,
        path2Convolution M t (z ja) (z jb) *
          M.graphWeightIntegrand t (H.comap v.succAbove) z
          ∂Measure.pi (fun _ : Fin n => M.mu) := by
  rw [graphWeight_fubini_survivors_first M t H v]
  congr 1
  funext z
  have hneq : v.succAbove ja ≠ v.succAbove jb :=
    fun h => hab (Fin.succAbove_right_injective h)
  have hpoint (y : S) :
      M.graphWeightIntegrand t H (Fin.insertNth v y z) =
        (Real.exp (-t * M.degreeFunction y) *
          (t * M.kernel y (z ja)) * (t * M.kernel y (z jb))) *
        M.graphWeightIntegrand t (H.comap v.succAbove) z := by
    rw [degreeTwo_graphWeightIntegrand_split M t H
      (Fin.insertNth v y z) hv hva hvb hneq]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    congr 1
    exact leaf_residual_eq_smaller_graph_integrand M t H v y z
  calc
    (∫ y : S, M.graphWeightIntegrand t H (Fin.insertNth v y z) ∂M.mu) =
        ∫ y : S,
          (Real.exp (-t * M.degreeFunction y) *
            (t * M.kernel y (z ja)) * (t * M.kernel y (z jb))) *
          M.graphWeightIntegrand t (H.comap v.succAbove) z ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = path2Convolution M t (z ja) (z jb) *
          M.graphWeightIntegrand t (H.comap v.succAbove) z := by
      rw [integral_mul_const]
      rfl

/-- The same exact suppression with any continuous observable depending
only on the surviving types.  The observable may be a product of factors
carried by additional labelled multigraph edges, including parallel
edges already created by previous suppressions. -/
theorem graphWeight_degreeTwo_transfer_marked
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1))
    (ja jb : Fin n) (hv : H.degree v = 2)
    (hva : H.Adj v (v.succAbove ja))
    (hvb : H.Adj v (v.succAbove jb)) (hab : ja ≠ jb)
    (F : C((Fin n → S), ℝ)) :
    (∫ x : Fin (n + 1) → S,
       M.graphWeightIntegrand t H x * F (fun j => x (v.succAbove j))
         ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
      ∫ z : Fin n → S,
        path2Convolution M t (z ja) (z jb) *
          M.graphWeightIntegrand t (H.comap v.succAbove) z * F z
          ∂Measure.pi (fun _ : Fin n => M.mu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hcont : Continuous
      (fun x : Fin (n + 1) → S =>
        M.graphWeightIntegrand t H x * F (fun j => x (v.succAbove j))) := by
    exact (M.graphWeightIntegrand_continuous t H).mul
      (F.continuous.comp (by fun_prop))
  have hf : Integrable
      (fun x : Fin (n + 1) → S =>
        M.graphWeightIntegrand t H x * F (fun j => x (v.succAbove j)))
      (Measure.pi (fun _ : Fin (n + 1) => M.mu)) :=
    hcont.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) =>
        M.graphWeightIntegrand t H (e.symm p) * F (e.symm p ∘ v.succAbove))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    _ = ∫ p : S × (Fin n → S),
          M.graphWeightIntegrand t H (e.symm p) * F (e.symm p ∘ v.succAbove)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
      exact (hmp.symm.integral_comp'
        (fun x : Fin (n + 1) → S =>
          M.graphWeightIntegrand t H x * F (fun j => x (v.succAbove j)))).symm
    _ = ∫ y : S, ∫ z : Fin n → S,
          M.graphWeightIntegrand t H (Fin.insertNth v y z) * F z
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk,
        Fin.insertNth_comp_succAbove]
    _ = ∫ z : Fin n → S, ∫ y : S,
          M.graphWeightIntegrand t H (Fin.insertNth v y z) * F z
          ∂M.mu ∂Measure.pi (fun _ : Fin n => M.mu) := by
      have hprod' : Integrable
          (fun p : S × (Fin n → S) =>
            M.graphWeightIntegrand t H (Fin.insertNth v p.1 p.2) * F p.2)
          (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) := by
        simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Equiv.coe_fn_mk,
          Fin.insertNth_comp_succAbove] using hprod
      exact integral_integral_swap hprod'
    _ = _ := by
      congr 1
      funext z
      have hneq : v.succAbove ja ≠ v.succAbove jb :=
        fun h => hab (Fin.succAbove_right_injective h)
      have hpoint (y : S) :
          M.graphWeightIntegrand t H (Fin.insertNth v y z) =
            (Real.exp (-t * M.degreeFunction y) *
              (t * M.kernel y (z ja)) * (t * M.kernel y (z jb))) *
            M.graphWeightIntegrand t (H.comap v.succAbove) z := by
        rw [degreeTwo_graphWeightIntegrand_split M t H
          (Fin.insertNth v y z) hv hva hvb hneq]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        congr 1
        exact leaf_residual_eq_smaller_graph_integrand M t H v y z
      calc
        (∫ y : S, M.graphWeightIntegrand t H (Fin.insertNth v y z) * F z ∂M.mu) =
            ∫ y : S,
              (Real.exp (-t * M.degreeFunction y) *
                (t * M.kernel y (z ja)) * (t * M.kernel y (z jb))) *
                (M.graphWeightIntegrand t (H.comap v.succAbove) z * F z) ∂M.mu := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hpoint]
          ring
        _ = path2Convolution M t (z ja) (z jb) *
              M.graphWeightIntegrand t (H.comap v.succAbove) z * F z := by
          rw [integral_mul_const]
          rw [mul_assoc]
          rfl

#print axioms PerronWright.GraphCore.degreeTwo_deleteIncidence_edgeFinset
#print axioms PerronWright.GraphCore.degreeTwo_weight_product_split
#print axioms PerronWright.GraphCore.degreeTwo_graphWeightIntegrand_split
#print axioms PerronWright.GraphCore.graphWeight_degreeTwo_transfer_induced
#print axioms PerronWright.GraphCore.path2ContinuousKernel_apply
#print axioms PerronWright.GraphCore.path2EdgeFactor_mk
#print axioms PerronWright.GraphCore.graphWeight_degreeTwo_transfer_marked

end PerronWright.GraphCore

