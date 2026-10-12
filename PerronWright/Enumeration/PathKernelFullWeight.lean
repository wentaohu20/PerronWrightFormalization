import PerronWright.Enumeration.PathKernelActualGraph

/-!
# Exact finite-dimensional weight of an entire path

The conditional weight integrates the literal `graphWeightIntegrand`
of the path on all internal vertices, with the two external endpoint
edge factors attached.  For every internal-vertex count it agrees
exactly with `pathKernel`, without an asymptotic or formal-series
assumption.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Removing the left endpoint from a nontrivial path preserves the
standard path-graph labelling of the remaining vertices. -/
theorem pathGraph_comap_succAbove_zero (m : ℕ) :
    (SimpleGraph.pathGraph (m + 2)).comap
        (fun i : Fin (m + 1) => (0 : Fin (m + 2)).succAbove i) =
      SimpleGraph.pathGraph (m + 1) := by
  ext i j
  simp only [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  simp only [Fin.zero_succAbove, Fin.val_succ]
  omega

/-- The first vertex of a path of at least two vertices has exactly
one neighbor. -/
theorem pathGraph_degree_zero (m : ℕ) :
    (SimpleGraph.pathGraph (m + 2)).degree 0 = 1 := by
  have hneigh : (SimpleGraph.pathGraph (m + 2)).neighborFinset 0 =
      ({1} : Finset (Fin (m + 2))) := by
    ext i
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton,
      SimpleGraph.pathGraph_adj, Fin.val_zero]
    constructor
    · intro h
      apply Fin.ext
      have hval : (1 : Fin (m + 2)).val = 1 := by simp
      rw [hval]
      omega
    · intro h
      subst i
      simp
  have hcard := (SimpleGraph.pathGraph (m + 2)).card_neighborFinset_eq_degree 0
  simpa [hneigh] using hcard.symm

/-- Literal path-graph integrand factorization when its first
internal vertex is peeled off.  The remainder is the actual induced
path graph, so every factor is stated concretely. -/
theorem pathGraph_integrand_first_split
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ)
    (y : S) (z : Fin (m + 1) → S) :
    M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 2))
        (Fin.insertNth 0 y z) =
      (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (z 0))) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 1)) z := by
  let G := SimpleGraph.pathGraph (m + 2)
  have hdeg : G.degree 0 = 1 := pathGraph_degree_zero m
  have hadj : G.Adj 0 ((0 : Fin (m + 2)).succAbove 0) := by
    simp [G, SimpleGraph.pathGraph_adj, Fin.zero_succAbove]
  rw [leaf_graphWeightIntegrand_split_at_neighbor M t G
    (Fin.insertNth 0 y z) hdeg hadj]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  congr 1
  rw [leaf_residual_eq_smaller_graph_integrand M t G 0 y z]
  exact congrArg (fun H => M.graphWeightIntegrand t H z)
    (pathGraph_comap_succAbove_zero m)

/-- Product-law Fubini at the first coordinate for any continuous
finite type-vector observable. -/
theorem integral_piFinSuccAbove_zero_continuous
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (n : ℕ)
    (F : C((Fin (n + 1) → S), ℝ)) :
    (∫ x : Fin (n + 1) → S, F x
      ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
      ∫ y : S, ∫ z : Fin n → S,
        F (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => S) 0
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) 0
  have hf : Integrable (fun x : Fin (n + 1) → S => F x)
      (Measure.pi (fun _ : Fin (n + 1) => M.mu)) :=
    F.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) => F (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    _ = ∫ p : S × (Fin n → S), F (e.symm p)
        ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
      exact (hmp.symm.integral_comp'
        (fun x : Fin (n + 1) → S => F x)).symm
    _ = _ := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk]

/-- A conditional type-vector observable built from the actual
graph-weight integrand of the path on all internal vertices, together
with the two external endpoint edges. -/
def interiorPathObservable
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (a b : S) :
    C((Fin (n + 1) → S), ℝ) := by
  refine ⟨fun x =>
    (t * M.kernel a (x 0)) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1)) x *
      (t * M.kernel (x (Fin.last n)) b), ?_⟩
  have hleft : Continuous
      (fun x : Fin (n + 1) → S => t * M.kernel a (x 0)) :=
    continuous_const.mul (M.kernel.toContinuousMap.continuous.comp
      (continuous_const.prodMk (continuous_apply 0)))
  have hright : Continuous
      (fun x : Fin (n + 1) → S => t * M.kernel (x (Fin.last n)) b) :=
    continuous_const.mul (M.kernel.toContinuousMap.continuous.comp
      ((continuous_apply (Fin.last n)).prodMk continuous_const))
  exact (hleft.mul
    (M.graphWeightIntegrand_continuous t (SimpleGraph.pathGraph (n + 1)))).mul hright

/-- The finite-dimensional conditional weight of an entire path:
every internal vertex and internal edge belongs to the *literal*
`graphWeightIntegrand` of `pathGraph`, and the two external edges are
model kernel factors. -/
def interiorPathGraphWeight
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : ℕ → S → S → ℝ
  | 0, a, b => t * M.kernel a b
  | n + 1, a, b =>
      ∫ x : Fin (n + 1) → S,
        interiorPathObservable M t n a b x
        ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)

theorem insertNth_zero_last
    {S : Type*} (m : ℕ) (y : S) (z : Fin (m + 1) → S) :
    (Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S)
        (Fin.last (m + 1)) =
      z (Fin.last m) := by
  have hlast : (0 : Fin (m + 2)).succAbove (Fin.last m) =
      Fin.last (m + 1) := by
    simp only [Fin.zero_succAbove, Fin.succ_last]
  rw [← hlast, Fin.insertNth_apply_succAbove]

/-- Exact first-vertex Fubini recurrence for the *whole* internal
path graph's finite-dimensional weight. -/
theorem interiorPathGraphWeight_succ_succ
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    interiorPathGraphWeight M t (m + 2) a b =
      ∫ y : S, (t * M.kernel a y) *
        Real.exp (-t * M.degreeFunction y) *
        interiorPathGraphWeight M t (m + 1) y b ∂M.mu := by
  change
    (∫ x : Fin (m + 2) → S,
      interiorPathObservable M t (m + 1) a b x
      ∂Measure.pi (fun _ : Fin (m + 2) => M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous M (m + 1)
    (interiorPathObservable M t (m + 1) a b)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hpoint (z : Fin (m + 1) → S) :
      interiorPathObservable M t (m + 1) a b
          (Fin.insertNth 0 y z) =
        ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
          interiorPathObservable M t m y b z := by
    change
      (t * M.kernel a
        ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S) 0)) *
        M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 2))
          (Fin.insertNth 0 y z) *
        (t * M.kernel
          ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S)
            (Fin.last (m + 1))) b) = _
    rw [pathGraph_integrand_first_split M t m y z]
    simp only [Fin.insertNth_apply_same, insertNth_zero_last]
    change _ =
      ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
        ((t * M.kernel y (z 0)) *
          M.graphWeightIntegrand t (SimpleGraph.pathGraph (m + 1)) z *
          (t * M.kernel (z (Fin.last m)) b))
    ring
  calc
    (∫ z : Fin (m + 1) → S,
        interiorPathObservable M t (m + 1) a b
          (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin (m + 1) => M.mu)) =
      ∫ z : Fin (m + 1) → S,
        ((t * M.kernel a y) * Real.exp (-t * M.degreeFunction y)) *
          interiorPathObservable M t m y b z
        ∂Measure.pi (fun _ : Fin (m + 1) => M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = _ := by
      rw [integral_const_mul]
      rfl

/-- Base case: integrating the sole internal vertex of the actual
one-vertex path graph gives the length-two path kernel. -/
theorem interiorPathGraphWeight_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a b : S) :
    interiorPathGraphWeight M t 1 a b = pathKernel M t 1 (a, b) := by
  change
    (∫ x : Fin 1 → S,
      interiorPathObservable M t 0 a b x
      ∂Measure.pi (fun _ : Fin 1 => M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous M 0
    (interiorPathObservable M t 0 a b)]
  rw [pathKernel_succ_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  have hpoint (z : Fin 0 → S) :
      interiorPathObservable M t 0 a b
          (Fin.insertNth 0 y z) =
        (t * M.kernel a y) * Real.exp (-t * M.degreeFunction y) *
          (t * M.kernel y b) := by
    have hx : (Fin.insertNth (0 : Fin 1) y z : Fin 1 → S) = ![y] := by
      funext i
      fin_cases i
      simp
    rw [hx]
    change (t * M.kernel a y) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph 1) ![y] *
      (t * M.kernel y b) = _
    rw [graphWeightIntegrand_pathGraph_one]
  simp_rw [hpoint]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

/-- Every length has an exact finite-dimensional representation:
the path kernel is the integral of the genuine `graphWeightIntegrand`
of the path on its internal vertices, multiplied by its two external
edge factors. -/
theorem interiorPathGraphWeight_eq_pathKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    interiorPathGraphWeight M t m a b = pathKernel M t m (a, b) := by
  induction m using Nat.twoStepInduction generalizing a b with
  | zero => rfl
  | one => exact interiorPathGraphWeight_one M t a b
  | more n _ ih =>
    rw [interiorPathGraphWeight_succ_succ M t n a b]
    rw [show n + 2 = (n + 1) + 1 by omega, pathKernel_succ_apply]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [ih y b]

#print axioms PerronWright.GraphCore.pathGraph_comap_succAbove_zero
#print axioms PerronWright.GraphCore.pathGraph_degree_zero
#print axioms PerronWright.GraphCore.pathGraph_integrand_first_split
#print axioms PerronWright.GraphCore.integral_piFinSuccAbove_zero_continuous
#print axioms PerronWright.GraphCore.interiorPathGraphWeight_succ_succ
#print axioms PerronWright.GraphCore.interiorPathGraphWeight_one
#print axioms PerronWright.GraphCore.interiorPathGraphWeight_eq_pathKernel

end PerronWright.GraphCore
