import PerronWright.Enumeration.PathKernelFullWeight
import Mathlib.Data.Fin.Rev

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Reversing the standard finite path preserves its adjacency. -/
theorem pathGraph_adj_rev (m : ℕ) (i j : Fin m) :
    (SimpleGraph.pathGraph m).Adj i.rev j.rev ↔
      (SimpleGraph.pathGraph m).Adj i j := by
  simp only [SimpleGraph.pathGraph_adj, Fin.val_rev]
  omega

/-- Reversal as a permutation of unordered vertex pairs. -/
def pathEdgeRevPerm (m : ℕ) : Equiv.Perm (Sym2 (Fin m)) where
  toFun := Sym2.map Fin.rev
  invFun := Sym2.map Fin.rev
  left_inv := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j => simp [Sym2.map_mk, Fin.rev_rev]
  right_inv := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j => simp [Sym2.map_mk, Fin.rev_rev]

@[simp] theorem pathEdgeRevPerm_mk (m : ℕ) (i j : Fin m) :
    pathEdgeRevPerm m s(i,j) = s(i.rev,j.rev) := rfl

/-- The unordered edge factor commutes with reversal of the type
vector and the corresponding unordered edge. -/
theorem edgeFactor_rev
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ)
    (x : Fin m → S) (e : Sym2 (Fin m)) :
    M.edgeFactor t (fun i => x i.rev) e =
      M.edgeFactor t x (pathEdgeRevPerm m e) := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- Reversal preserves exactly the edge set of the standard path. -/
theorem pathGraph_edgeFinset_rev_mem (m : ℕ) (e : Sym2 (Fin m)) :
    e ∈ (SimpleGraph.pathGraph m).edgeFinset ↔
      pathEdgeRevPerm m e ∈ (SimpleGraph.pathGraph m).edgeFinset := by
  induction e using Sym2.inductionOn with
  | _ i j =>
    simp only [pathEdgeRevPerm_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact (pathGraph_adj_rev m i j).symm

/-- The literal finite-path graph integrand is invariant under
reversal of all internal type labels. -/
theorem graphWeightIntegrand_pathGraph_rev
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ)
    (x : Fin m → S) :
    M.graphWeightIntegrand t (SimpleGraph.pathGraph m)
        (fun i => x i.rev) =
      M.graphWeightIntegrand t (SimpleGraph.pathGraph m) x := by
  unfold CompactBJRModel.graphWeightIntegrand
  congr 1
  · exact Equiv.prod_comp (Fin.revPerm (n := m))
      (fun i : Fin m => Real.exp (-t * M.degreeFunction (x i)))
  · apply Finset.prod_bijective (pathEdgeRevPerm m)
    · exact (pathEdgeRevPerm m).bijective
    · intro e
      exact pathGraph_edgeFinset_rev_mem m e
    · intro e _
      exact edgeFactor_rev M t m x e

/-- The full conditional path observable reverses its endpoint roles
when its entire internal type vector is reversed. -/
theorem interiorPathObservable_rev
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    (a b : S) (x : Fin (n + 1) → S) :
    interiorPathObservable M t n a b (fun i => x i.rev) =
      interiorPathObservable M t n b a x := by
  change
    (t * M.kernel a (x (Fin.rev 0))) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1))
        (fun i => x i.rev) *
      (t * M.kernel (x (Fin.rev (Fin.last n))) b) = _
  simp only [Fin.rev_zero, Fin.rev_last,
    graphWeightIntegrand_pathGraph_rev]
  change
    (t * M.kernel a (x (Fin.last n))) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1)) x *
      (t * M.kernel (x 0) b) =
    (t * M.kernel b (x 0)) *
      M.graphWeightIntegrand t (SimpleGraph.pathGraph (n + 1)) x *
      (t * M.kernel (x (Fin.last n)) a)
  rw [M.kernel.symmetric a (x (Fin.last n)),
    M.kernel.symmetric (x 0) b]
  ring

/-- Reversal of independent identically distributed internal types
preserves the actual product type law. -/
theorem integral_pathObservable_rev
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (n : ℕ)
    (F : C((Fin (n + 1) → S), ℝ)) :
    (∫ x : Fin (n + 1) → S, F (fun i => x i.rev)
      ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
      ∫ x : Fin (n + 1) → S, F x
      ∂Measure.pi (fun _ : Fin (n + 1) => M.mu) := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (n + 1) => S) (Fin.revPerm (n := n + 1))
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (Measure.pi (fun _ : Fin (n + 1) => M.mu)) :=
    measurePreserving_piCongrLeft
      (fun _ : Fin (n + 1) => M.mu) (Fin.revPerm (n := n + 1))
  have he (x : Fin (n + 1) → S) :
      e x = (fun i => x i.rev) := by
    funext i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Fin.revPerm]
  simpa only [he] using
    (hmp.integral_comp' (fun x : Fin (n + 1) → S => F x))

/-- The path kernel has no dependence on the orientation of its
endpoints, for every number of internal degree-two vertices. -/
theorem pathKernel_symmetric_all
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    pathKernel M t m (a, b) = pathKernel M t m (b, a) := by
  rw [← interiorPathGraphWeight_eq_pathKernel M t m a b,
    ← interiorPathGraphWeight_eq_pathKernel M t m b a]
  cases m with
  | zero =>
      change t * M.kernel a b = t * M.kernel b a
      rw [M.kernel.symmetric a b]
  | succ n =>
      change
        (∫ x : Fin (n + 1) → S,
          interiorPathObservable M t n a b x
          ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) =
        ∫ x : Fin (n + 1) → S,
          interiorPathObservable M t n b a x
          ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)
      calc
        _ = ∫ x : Fin (n + 1) → S,
            interiorPathObservable M t n b a (fun i => x i.rev)
            ∂Measure.pi (fun _ : Fin (n + 1) => M.mu) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (interiorPathObservable_rev M t n b a x).symm
        _ = _ := integral_pathObservable_rev M n
          (interiorPathObservable M t n b a)

/-- Any path length now defines an edge factor on unordered labelled
kernel edges, including loops and parallel edge labels. -/
def pathKernelEdgeFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ)
    {v : ℕ} (x : Fin v → S) (e : Sym2 (Fin v)) : ℝ :=
  Sym2.lift ⟨fun i j => pathKernel M t m (x i, x j), by
    intro i j
    exact pathKernel_symmetric_all M t m (x i) (x j)⟩ e

@[simp] theorem pathKernelEdgeFactor_mk
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ)
    {v : ℕ} (x : Fin v → S) (i j : Fin v) :
    pathKernelEdgeFactor M t m x s(i,j) =
      pathKernel M t m (x i, x j) := rfl

#print axioms PerronWright.GraphCore.pathGraph_adj_rev
#print axioms PerronWright.GraphCore.pathEdgeRevPerm_mk
#print axioms PerronWright.GraphCore.edgeFactor_rev
#print axioms PerronWright.GraphCore.pathGraph_edgeFinset_rev_mem
#print axioms PerronWright.GraphCore.graphWeightIntegrand_pathGraph_rev
#print axioms PerronWright.GraphCore.interiorPathObservable_rev
#print axioms PerronWright.GraphCore.integral_pathObservable_rev
#print axioms PerronWright.GraphCore.pathKernel_symmetric_all
#print axioms PerronWright.GraphCore.pathKernelEdgeFactor_mk

end PerronWright.GraphCore
