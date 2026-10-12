import PerronWright.Probability.IndependentEdges
import PerronWright.Enumeration.FieldWeight
import Mathlib.MeasureTheory.Constructions.SimpleGraph

/-!
# The annealed compact BJR random graph

The sample coordinates are unordered non-diagonal vertex pairs.  Thus each
simple edge occurs exactly once.  We average the conditional independent
edge masses over the literal product type law and construct a normalized
probability mass function.  All finite graph expectations are consequently
actual expectations under a probability measure.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.AnnealedGraph

/-- The possible simple edges on the labelled vertex set `Fin n`. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- One Boolean variable for each unordered simple edge. -/
abbrev Assignment (n : ℕ) := Edge n → Bool

/-- Convert an edge assignment to a labelled simple graph. -/
def toGraph {n : ℕ} (a : Assignment n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬e.IsDiag, a ⟨e, h⟩ = true}

@[simp] theorem mem_toGraph_edgeSet {n : ℕ} (a : Assignment n)
    (e : Edge n) : e.val ∈ (toGraph a).edgeSet ↔ a e = true := by
  simp [toGraph, SimpleGraph.edgeSet_fromEdgeSet, e.property, Sym2.mem_diagSet]

/-- Recover the Boolean edge assignment of a simple graph. -/
def assignmentOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Assignment n :=
  fun e ↦ decide (e.val ∈ G.edgeSet)

@[simp] theorem assignmentOfGraph_toGraph {n : ℕ} (a : Assignment n) :
    assignmentOfGraph (toGraph a) = a := by
  funext e
  cases h : a e <;> simp [assignmentOfGraph, h]

@[simp] theorem toGraph_assignmentOfGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) : toGraph (assignmentOfGraph G) = G := by
  apply SimpleGraph.edgeSet_injective
  ext e
  by_cases he : e.IsDiag
  · simp [toGraph, SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet, he,
      G.not_mem_edgeSet_of_isDiag he]
  · simpa [assignmentOfGraph] using
      (mem_toGraph_edgeSet (assignmentOfGraph G) ⟨e, he⟩)

/-- Boolean assignments and labelled simple graphs are in bijection. -/
def graphEquiv (n : ℕ) : Assignment n ≃ SimpleGraph (Fin n) where
  toFun := toGraph
  invFun := assignmentOfGraph
  left_inv := assignmentOfGraph_toGraph
  right_inv := toGraph_assignmentOfGraph

theorem measurable_toGraph (n : ℕ) :
    Measurable (toGraph : Assignment n → SimpleGraph (Fin n)) :=
  measurable_of_finite _

instance graph_measurableSingleton (n : ℕ) :
    MeasurableSingletonClass (SimpleGraph (Fin n)) where
  measurableSet_singleton G := by
    have hm := SimpleGraph.measurable_adj (measurableSet_singleton G.Adj)
    have hs : SimpleGraph.Adj ⁻¹' {G.Adj} = {G} := by
      ext H
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SimpleGraph.adj_inj]
    rw [hs] at hm
    exact hm

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The i.i.d. type law on all labelled vertices. -/
abbrev typeLaw (M : CompactBJRModel S) (n : ℕ) : Measure (Fin n → S) :=
  Measure.pi (fun _ : Fin n ↦ M.mu)

/-- The exact conditional edge hazard from the paper. -/
def hazard (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (x : Fin n → S) (e : Edge n) : ℝ :=
  M.edgeFactor t x e.val / (n : ℝ)

theorem hazard_nonneg (M : CompactBJRModel S) {t : ℝ} (ht : 0 ≤ t)
    {n : ℕ} (x : Fin n → S) (e : Edge n) : 0 ≤ hazard M t x e :=
  div_nonneg (M.edgeFactor_nonneg t ht x e.val) (Nat.cast_nonneg n)

/-- The graph mass with the types held fixed. -/
def conditionalMass (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (x : Fin n → S) (a : Assignment n) : ℝ :=
  IndependentEdges.mass (hazard M t x) a

theorem conditionalMass_nonneg (M : CompactBJRModel S)
    {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (x : Fin n → S) (a : Assignment n) :
    0 ≤ conditionalMass M t x a :=
  IndependentEdges.mass_nonneg (hazard_nonneg M ht x) a

@[simp] theorem sum_conditionalMass (M : CompactBJRModel S) (t : ℝ)
    {n : ℕ} (x : Fin n → S) :
    ∑ a : Assignment n, conditionalMass M t x a = 1 :=
  IndependentEdges.sum_mass (J := Edge n) (hazard M t x)

theorem conditionalMass_continuous (M : CompactBJRModel S) (t : ℝ)
    {n : ℕ} (a : Assignment n) :
    Continuous (fun x : Fin n → S ↦ conditionalMass M t x a) := by
  unfold conditionalMass IndependentEdges.mass
  apply continuous_finsetProd
  intro e _
  have he : Continuous (fun x : Fin n → S ↦ hazard M t x e) :=
    (M.edgeFactor_continuous t e.val).div_const _
  cases a e
  · exact he.neg.rexp
  · exact continuous_const.sub he.neg.rexp

theorem conditionalMass_integrable (M : CompactBJRModel S) (t : ℝ)
    {n : ℕ} (a : Assignment n) :
    Integrable (fun x : Fin n → S ↦ conditionalMass M t x a) (typeLaw M n) :=
  (conditionalMass_continuous M t a).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- The annealed graph mass, averaging over both types and edges. -/
def mass (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (a : Assignment n) : ℝ :=
  ∫ x : Fin n → S, conditionalMass M t x a ∂typeLaw M n

theorem mass_nonneg (M : CompactBJRModel S) {t : ℝ} (ht : 0 ≤ t)
    {n : ℕ} (a : Assignment n) : 0 ≤ mass M t a :=
  integral_nonneg (fun x ↦ conditionalMass_nonneg M ht x a)

@[simp] theorem sum_mass (M : CompactBJRModel S) (t : ℝ) (n : ℕ) :
    ∑ a : Assignment n, mass M t a = 1 := by
  unfold mass
  rw [← integral_finsetSum]
  · simp
  · intro a _
    exact conditionalMass_integrable M t a

/-- A normalized probability mass function for the annealed graph. -/
def pmf (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    PMF (Assignment n) :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (mass M t a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mass_nonneg M ht a)]
    simp)

@[simp] theorem pmf_apply (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) {n : ℕ} (a : Assignment n) :
    pmf M t ht n a = ENNReal.ofReal (mass M t a) := rfl

@[simp] theorem pmf_apply_toReal (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) {n : ℕ} (a : Assignment n) :
    (pmf M t ht n a).toReal = mass M t a := by
  rw [pmf_apply, ENNReal.toReal_ofReal (mass_nonneg M ht a)]

/-- The annealed graph law as a probability mass function on simple graphs. -/
def graphPMF (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    PMF (SimpleGraph (Fin n)) :=
  (pmf M t ht n).map toGraph

/-- The annealed graph law as a probability measure on simple graphs. -/
def law (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Measure (SimpleGraph (Fin n)) := (graphPMF M t ht n).toMeasure

instance law_isProbability (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) : IsProbabilityMeasure (law M t ht n) :=
  inferInstanceAs (IsProbabilityMeasure (graphPMF M t ht n).toMeasure)

/-- Expected graph observables equal the i.i.d. type average of their
conditional expectations.  This identity is exact at every finite size. -/
theorem expectation_eq_type_integral (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (f : SimpleGraph (Fin n) → ℝ) :
    (∫ a : Assignment n, f (toGraph a) ∂(pmf M t ht n).toMeasure) =
      ∫ x : Fin n → S,
        ∑ a : Assignment n, conditionalMass M t x a * f (toGraph a)
        ∂typeLaw M n := by
  rw [PMF.integral_eq_sum]
  simp only [pmf_apply_toReal, smul_eq_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    exact (integral_mul_const _ _).symm
  · intro a _
    exact (conditionalMass_integrable M t a).mul_const _

/-- The same identity on the paper's graph sample space. -/
theorem law_expectation_eq_type_integral (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (f : SimpleGraph (Fin n) → ℝ) :
    (∫ G, f G ∂law M t ht n) =
      ∫ x : Fin n → S,
        ∑ a : Assignment n, conditionalMass M t x a * f (toGraph a)
        ∂typeLaw M n := by
  unfold law graphPMF
  rw [← PMF.toMeasure_map toGraph (pmf M t ht n) (measurable_toGraph n)]
  rw [integral_map (measurable_toGraph n).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable]
  exact expectation_eq_type_integral M t ht n f

end PerronWright.AnnealedGraph
