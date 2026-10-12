import PerronWright.Enumeration.PathKernel
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Actual graph-weight factors in arbitrary path convolutions

These identities connect the continuous path kernels to the literal
finite-graph integrand used in the compact BJR model.  They are local
splicing identities; a separate argument is still required to identify
the entire finite-dimensional weight of a long path graph at once.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- The one-vertex path graph supplies precisely one internal
isolation factor of the manuscript's graph-weight integrand. -/
theorem graphWeightIntegrand_pathGraph_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (y : S) :
    M.graphWeightIntegrand t (SimpleGraph.pathGraph 1) ![y] =
      Real.exp (-t * M.degreeFunction y) := by
  have hgraph : SimpleGraph.pathGraph 1 = ⊥ := by
    ext u v
    fin_cases u
    fin_cases v
    simp
  rw [hgraph]
  unfold CompactBJRModel.graphWeightIntegrand
  simp only [SimpleGraph.edgeFinset, SimpleGraph.edgeSet_bot,
    Set.toFinset_empty, Finset.prod_empty, mul_one]
  simp

/-- One internal vertex in an arbitrarily continued weighted path is
literally the isolated-vertex graph-weight integrand times its
neighboring edge and remaining path response. -/
theorem pathKernel_succ_graphWeightIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    pathKernel M t (m + 1) (a, b) =
      ∫ y : S, (t * M.kernel a y) *
        M.graphWeightIntegrand t (SimpleGraph.pathGraph 1) ![y] *
        pathKernel M t m (y, b) ∂M.mu := by
  rw [pathKernel_succ_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [graphWeightIntegrand_pathGraph_one]

/-- The actual graph-weight integrand of the two-vertex path is exactly
the pair of interior isolation factors and its genuine kernel edge. -/
theorem graphWeightIntegrand_pathGraph_two
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (y z : S) :
    M.graphWeightIntegrand t (SimpleGraph.pathGraph 2) ![y, z] =
      Real.exp (-t * M.degreeFunction y) *
      Real.exp (-t * M.degreeFunction z) *
      (t * M.kernel y z) := by
  have hset : (⊤ : SimpleGraph (Fin 2)).edgeSet =
      ({s(0,1)} : Set (Sym2 (Fin 2))) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ i j =>
      fin_cases i <;> fin_cases j <;>
        simp [SimpleGraph.edgeSet_top, Sym2.mk_isDiag_iff]
  rw [SimpleGraph.pathGraph_two_eq_top]
  unfold CompactBJRModel.graphWeightIntegrand
  simp only [SimpleGraph.edgeFinset, hset, Set.toFinset_singleton,
    Fin.prod_univ_two, Finset.prod_singleton,
    CompactBJRModel.edgeFactor_mk]
  rfl

/-- Two more internal vertices of an arbitrarily continued path are
represented by the literal graph-weight integrand of the two-vertex
path, integrated against the actual type law. -/
theorem pathKernel_add_two_graphWeightIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    pathKernel M t (m + 2) (a, b) =
      ∫ y : S, ∫ z : S,
        (t * M.kernel a y) *
        M.graphWeightIntegrand t (SimpleGraph.pathGraph 2) ![y, z] *
        pathKernel M t m (z, b) ∂M.mu ∂M.mu := by
  rw [show m + 2 = (m + 1) + 1 by omega,
      pathKernel_succ_apply]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [pathKernel_succ_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [graphWeightIntegrand_pathGraph_two]
  ring

#print axioms PerronWright.GraphCore.graphWeightIntegrand_pathGraph_one
#print axioms PerronWright.GraphCore.pathKernel_succ_graphWeightIntegrand
#print axioms PerronWright.GraphCore.graphWeightIntegrand_pathGraph_two
#print axioms PerronWright.GraphCore.pathKernel_add_two_graphWeightIntegrand

end PerronWright.GraphCore
