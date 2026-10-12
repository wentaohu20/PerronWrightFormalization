import PerronWright.Model.PerronQuantities
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact annealed connected-graph weight

This module begins the combinatorial branch with the literal finite-graph
definition of the paper's `C_t(k,r)`.  It sums over simple graphs on `Fin k`
and integrates their type weights against the product type law.  No
asymptotic enumeration theorem is assumed here.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The edge factor for an unordered pair of vertices.  Symmetry of the
kernel makes this independent of the choice of ordering. -/
def edgeFactor (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (x : Fin k → S) (e : Sym2 (Fin k)) : ℝ :=
  Sym2.lift ⟨fun i j => t * M.kernel (x i) (x j), by
    intro i j
    change t * M.kernel (x i) (x j) = t * M.kernel (x j) (x i)
    rw [M.kernel.symmetric (x i) (x j)]⟩ e

@[simp] theorem edgeFactor_mk (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (x : Fin k → S) (i j : Fin k) :
    M.edgeFactor t x s(i,j) = t * M.kernel (x i) (x j) := rfl

/-- The exact weight of one labelled simple graph and one type vector. -/
def graphWeightIntegrand (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (H : SimpleGraph (Fin k)) (x : Fin k → S) : ℝ := by
  classical
  exact (∏ i : Fin k, Real.exp (-t * M.degreeFunction (x i))) *
    ∏ e ∈ H.edgeFinset, M.edgeFactor t x e

/-- Annealed weight of a particular labelled graph. -/
def graphWeight (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (H : SimpleGraph (Fin k)) : ℝ :=
  ∫ x : Fin k → S, M.graphWeightIntegrand t H x
    ∂Measure.pi (fun _ : Fin k => M.mu)

/-- The connected fixed-size, fixed-surplus partition function from the
statement of the Perron--Wright theorem. -/
def connectedWeight (M : CompactBJRModel S) (t : ℝ)
    (k r : ℕ) : ℝ := by
  classical
  exact ∑ H : SimpleGraph (Fin k),
    if H.Connected ∧ H.edgeFinset.card = k + r - 1
    then M.graphWeight t H else 0

end CompactBJRModel
end PerronWright
