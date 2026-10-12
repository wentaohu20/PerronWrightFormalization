import PerronWright.Model.FiniteIrreducibleModel
import PerronWright.Probability.FixedTypeGraph
import PerronWright.Probability.IntegerTypeAssignment

/-!
# Literal deterministic finite irreducible graph laws

An arbitrary actual vertex type assignment is held fixed. Its edge law has
the paper's exact probability 1-exp(-t*kappa/n), and its ordered component
factorial expectation is the genuine independent-edge finite formula.
Arbitrary integer count realizations are supported; rounded counts are
only one proved instance, not a restriction on the identities.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.FiniteIrreducibleTypedGraphLaw

open AnnealedGraph SelectedConfiguration ComponentCounts ExactFactorialExpectation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The actual symmetric matrix entry on an unordered vertex pair. -/
def pairKernel (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ M.kernel (x i) (x j),
    fun i j ↦ M.symmetric (x i) (x j)⟩

@[simp] theorem pairKernel_mk (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (i j : Fin n) :
    pairKernel M x s(i,j) = M.kernel (x i) (x j) := rfl

theorem pairKernel_nonneg (M : FiniteIrreducibleModel S) {n : ℕ}
    (x : Fin n → S) (e : Sym2 (Fin n)) : 0 ≤ pairKernel M x e := by
  induction e using Sym2.inductionOn with
  | _ i j => exact M.kernel_nonneg (x i) (x j)

/-- Exact edge hazards for a fixed, not sampled, type assignment. -/
def hazard (M : FiniteIrreducibleModel S) (t : ℝ) {n : ℕ}
    (x : Fin n → S) (e : Edge n) : ℝ :=
  t * pairKernel M x e.val / (n : ℝ)

theorem hazard_nonneg (M : FiniteIrreducibleModel S) {t : ℝ} (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) (e : Edge n) : 0 ≤ hazard M t x e :=
  div_nonneg (mul_nonneg ht (pairKernel_nonneg M x e.val)) (Nat.cast_nonneg n)

/-- The actual graph probability law conditional on this deterministic
type assignment, without integrating over any type law. -/
def law (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) : Measure (SimpleGraph (Fin n)) :=
  FixedTypeGraph.law (hazard M t x) (hazard_nonneg M ht x)

instance law_isProbability (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) : IsProbabilityMeasure (law M t ht x) :=
  inferInstanceAs (IsProbabilityMeasure
    (FixedTypeGraph.law (hazard M t x) (hazard_nonneg M ht x)))

/-- The marginal of one actual graph edge, directly from the finite
independent-edge distribution. -/
theorem edge_indicator_expectation {n : ℕ} (z : Edge n → ℝ)
    (hz : ∀ e, 0 ≤ z e) (e : Edge n) :
    (∫ G, if e.val ∈ G.edgeSet then (1 : ℝ) else 0 ∂FixedTypeGraph.law z hz) =
      1 - Real.exp (-z e) := by
  rw [FixedTypeGraph.expectation_eq_sum]
  simp only [mem_toGraph_edgeSet, mul_ite, mul_one, mul_zero]
  simpa [IndependentEdges.AgreesOn] using
    IndependentEdges.sum_mass_agreesOn z {e} (fun _ ↦ true)

/-- The exact paper edge probability under the genuine graph measure. -/
theorem law_real_edge (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) (e : Edge n) :
    (law M t ht x).real {G | e.val ∈ G.edgeSet} =
      1 - Real.exp (-(t * pairKernel M x e.val / (n : ℝ))) := by
  have h := edge_indicator_expectation (hazard M t x) (hazard_nonneg M ht x) e
  have hm : MeasurableSet {G : SimpleGraph (Fin n) | e.val ∈ G.edgeSet} :=
    Set.toFinite _ |>.measurableSet
  rw [← integral_indicator_one hm]
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, law, hazard] using h

/-- Exact ordered distinct genuine-component factorial formula for every
actual deterministic finite type assignment. -/
theorem factorial_expectation_exact (M : FiniteIrreducibleModel S)
    (t : ℝ) (ht : 0 ≤ t) {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      ∑ B : Fin q ↪ Finset (Fin n),
        ∑ c : prescribedEdges (selectedUnion B) → Bool,
          Real.exp (-(∑ e ∈ prescribedEdges (selectedUnion B), hazard M t x e)) *
            (∏ e ∈ prescribedEdges (selectedUnion B),
              if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
              then Real.exp (hazard M t x e) - 1 else 1) *
            (if ∀ i, MatchesBlock
              (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))
              (B i) (k i) (r i) then (1 : ℝ) else 0) :=
  FixedTypeGraph.factorial_expectation_exact (hazard M t x) (hazard_nonneg M ht x) k r

/-- Any prescribed integer type counts summing to n have an actual
deterministic assignment; no rounding choice is imposed. -/
theorem exists_assignment_of_counts {n : ℕ} (c : S → ℕ) (hc : ∑ a, c a = n) :
      ∃ x : Fin n → S, ∀ a : S, Fintype.card {v : Fin n // x v = a} = c a := by
  classical
  refine ⟨IntegerTypeAssignment.typeVector c hc, ?_⟩
  intro a
  exact (Fintype.card_congr (IntegerTypeAssignment.fiberEquiv c hc a)).trans
    (Fintype.card_fin _)

/-- One concrete rounding realization of the fixed positive target law. -/
def roundedAssignment (M : FiniteIrreducibleModel S) (a0 : S) (n : ℕ) : Fin n → S :=
  IntegerTypeAssignment.roundedTypeVector a0 M.weight
    (fun a ↦ (M.weight_pos a).le) M.weight_sum n

@[simp] theorem roundedAssignment_fiber_card
    (M : FiniteIrreducibleModel S) (a0 : S) (n : ℕ) (a : S) :
    Fintype.card {v : Fin n // roundedAssignment M a0 n v = a} =
      FiniteTypeCounts.counts a0 M.weight n a := by
  classical
  exact (Fintype.card_congr (IntegerTypeAssignment.fiberEquiv
    (FiniteTypeCounts.counts a0 M.weight n)
    (FiniteTypeCounts.sum_counts a0 M.weight
      (fun a ↦ (M.weight_pos a).le) M.weight_sum n) a)).trans
    (Fintype.card_fin _)

/-- The constructed actual type counts have a uniform O(1) rounding error. -/
theorem roundedAssignment_fiber_error_le
    (M : FiniteIrreducibleModel S) (a0 : S) (n : ℕ) (a : S) :
    |(Fintype.card {v : Fin n // roundedAssignment M a0 n v = a} : ℝ) -
      (n : ℝ) * M.weight a| ≤ 2 * (Fintype.card S : ℝ) := by
  rw [roundedAssignment_fiber_card]
  exact (Finset.single_le_sum (fun b _ ↦ abs_nonneg
    ((FiniteTypeCounts.counts a0 M.weight n b : ℝ) - (n : ℝ) * M.weight b))
    (Finset.mem_univ a)).trans
    (FiniteTypeCounts.sum_counts_error_le a0 M.weight
      (fun b ↦ (M.weight_pos b).le) M.weight_sum n)

end PerronWright.FiniteIrreducibleTypedGraphLaw
