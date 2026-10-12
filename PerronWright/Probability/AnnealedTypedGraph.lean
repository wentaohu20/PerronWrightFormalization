import PerronWright.Probability.AnnealedGraph
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Joint type-and-edge probability law

This keeps the sampled vertex types, rather than marginalizing them out,
so empirical type profiles are random variables on the same probability
space as the component graph.  Its density is the literal conditional
independent-edge mass, and normalization follows from the finite sum of
those masses being one at every type vector.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.AnnealedTypedGraph

open AnnealedGraph

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The joint sampled type vector and edge assignment. -/
abbrev State (S : Type*) (n : ℕ) := (Fin n → S) × Assignment n

theorem measurable_conditionalMass (M : CompactBJRModel S) (t : ℝ) (n : ℕ) :
    Measurable (fun p : State S n ↦ conditionalMass M t p.1 p.2) :=
  measurable_from_prod_countable_left
    (fun a ↦ (conditionalMass_continuous M t a).measurable)

/-- The joint type-and-edge probability law. -/
def law (M : CompactBJRModel S) (t : ℝ) (_ht : 0 ≤ t) (n : ℕ) :
    Measure (State S n) :=
  ((typeLaw M n).prod Measure.count).withDensity
    (fun p ↦ ENNReal.ofReal (conditionalMass M t p.1 p.2))

instance law_isProbability (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) : IsProbabilityMeasure (law M t ht n) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hm : Measurable (fun p : State S n ↦
      ENNReal.ofReal (conditionalMass M t p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_conditionalMass M t n)
  rw [lintegral_prod _ hm.aemeasurable]
  have hx (x : Fin n → S) :
      (∑ a : Assignment n, ENNReal.ofReal (conditionalMass M t x a)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ ↦ conditionalMass_nonneg M ht x a)]
    simp
  simp_rw [lintegral_count, tsum_fintype, hx]
  simp

/-- The labelled simple graph sampled on the joint space. -/
def graph {n : ℕ} (p : State S n) : SimpleGraph (Fin n) := toGraph p.2

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem measurable_graph (n : ℕ) :
    Measurable (graph : State S n → SimpleGraph (Fin n)) :=
  (measurable_toGraph n).comp measurable_snd

/-- Fubini for observables that are integrable on every fixed graph slice.
The finiteness of the edge sample space supplies the remaining integrability. -/
theorem expectation_eq_type_integral (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (F : State S n → ℝ)
    (hF : ∀ a, Measurable (fun x ↦ F (x, a)))
    (hI : ∀ a, Integrable
      (fun x ↦ conditionalMass M t x a * F (x, a)) (typeLaw M n)) :
    (∫ p, F p ∂law M t ht n) =
      ∫ x : Fin n → S,
        ∑ a : Assignment n, conditionalMass M t x a * F (x, a)
        ∂typeLaw M n := by
  have hd : Measurable (fun p : State S n ↦
      ENNReal.ofReal (conditionalMass M t p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_conditionalMass M t n)
  have hw : Measurable (fun p : State S n ↦
      conditionalMass M t p.1 p.2 * F p) :=
    measurable_from_prod_countable_left
      (fun a ↦ (conditionalMass_continuous M t a).measurable.mul (hF a))
  have hi : Integrable (fun p : State S n ↦
      conditionalMass M t p.1 p.2 * F p)
      ((typeLaw M n).prod Measure.count) := by
    apply (integrable_prod_iff' hw.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hI, ?_⟩
    exact Integrable.of_finite
  unfold law
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (conditionalMass_nonneg M ht _ _), smul_eq_mul]
  rw [integral_prod _ hi]
  simp only [integral_count]

/-- The joint law has exactly the previously constructed graph marginal. -/
theorem graph_expectation (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (f : SimpleGraph (Fin n) → ℝ) :
    (∫ p, f (graph p) ∂law M t ht n) =
      ∫ G, f G ∂AnnealedGraph.law M t ht n := by
  rw [expectation_eq_type_integral M t ht n (fun p ↦ f (graph p))]
  · exact (AnnealedGraph.law_expectation_eq_type_integral M t ht n f).symm
  · intro a
    change Measurable (fun _ : Fin n → S ↦ f (toGraph a))
    exact measurable_const
  · intro a
    change Integrable (fun x ↦ conditionalMass M t x a * f (toGraph a)) _
    exact (conditionalMass_integrable M t a).mul_const _

/-- Marginalizing out the sampled graph leaves the literal i.i.d. type law. -/
theorem type_expectation (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) (f : C((Fin n → S), ℝ)) :
    (∫ p, f p.1 ∂law M t ht n) = ∫ x, f x ∂typeLaw M n := by
  rw [expectation_eq_type_integral M t ht n (fun p ↦ f p.1)]
  · apply integral_congr_ae
    filter_upwards [] with x
    rw [← Finset.sum_mul, sum_conditionalMass, one_mul]
  · intro a
    exact f.continuous.measurable
  · intro a
    exact ((conditionalMass_continuous M t a).mul f.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact

end PerronWright.AnnealedTypedGraph
