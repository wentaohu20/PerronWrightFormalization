import PerronWright.Probability.FiniteIrreducibleMarkedWindowMoments
import PerronWright.Probability.EmpiricalWeakNeighborhood

/-! # Actual deterministic graph window marks collapse to the Perron law

The bad event ranges over the actual connected components of the graph
with its literal deterministic assignment. Expected total deviation and
Markov's inequality are proved from the finite-model marked factorial
terminal; no graph-profile concentration interface is assumed.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleWindowMarkConcentration

open FiniteIrreducibleMarkedWindowMoments FiniteIrreducibleComponentProcess
  ComponentWindowPointMeasures EmpiricalTypeMarks EmpiricalWeakNeighborhood
open FiniteIrreducibleConnectedTypeLaw (perronLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def badTestEvent (ν : ProbabilityMeasure S) {n : ℕ} (x : Fin n → S)
    (a b : ℝ) (R : ℕ) (F : ProbabilityMeasure S → ℝ) (ε : ℝ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ C : WindowComponent a b R 1 G, ε ≤ |F (componentMark x C.val)-F ν|}

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem badTestEvent_probability_le (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    (F : ProbabilityMeasure S → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (graphLaw M lambda n x).real (badTestEvent (perronLaw M hM) x a b R F ε) ≤
      (∫ G, windowMarkDeviation M hM x G a b R F ∂graphLaw M lambda n x)/ε := by
  let μ := graphLaw M lambda n x
  let D : SimpleGraph (Fin n) → ℝ := fun G ↦ windowMarkDeviation M hM x G a b R F
  have hI : Integrable D μ := Integrable.of_finite
  have hp (G) : 0 ≤ D G := windowMarkDeviation_nonneg M hM x G a b R F
  have hh : μ (badTestEvent (perronLaw M hM) x a b R F ε) ≤
      ENNReal.ofReal (∫ G, D G/ε ∂μ) :=
    (hI.div_const ε).measure_le_integral
      (Eventually.of_forall (fun G ↦ div_nonneg (hp G) hε.le)) (fun G hG ↦ by
        obtain ⟨C,hC⟩ := hG
        apply (le_div_iff₀ hε).mpr
        simp only [one_mul]
        apply hC.trans
        exact Finset.single_le_sum (f := fun C : WindowComponent a b R 1 G ↦
          |F (componentMark x C.val)-F (perronLaw M hM)|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ C))
  calc
    _ ≤ (ENNReal.ofReal (∫ G, D G/ε ∂μ)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = _ := by
      rw [integral_div,ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hp) hε.le)]

theorem badTestEvent_probability_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (graphLaw M lambda n (x n)).real
      (badTestEvent (perronLaw M hM) (x n) a b R F ε)) atTop (𝓝 0) := by
  have ht := (windowMarkDeviation_expectation_tendsto_zero M hM R lambda a b ha hab
    x D hD hround F hF).div_const ε
  simp only [zero_div] at ht
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    (Eventually.of_forall (fun n ↦ badTestEvent_probability_le M hM lambda a b R n (x n) F ε hε)) ht

def badWeakEvent {n : ℕ} (x : Fin n → S) (a b : ℝ) (R : ℕ)
    (U : Set (ProbabilityMeasure S)) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ C : WindowComponent a b R 1 G, componentMark x C.val ∉ U}

/-- With probability tending to one, every actual component in the fixed
window has its empirical mark in the prescribed genuine weak neighborhood. -/
theorem badWeakEvent_probability_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronLaw M hM)) :
    Tendsto (fun n ↦ (graphLaw M lambda n (x n)).real (badWeakEvent (x n) a b R U)) atTop (𝓝 0) := by
  obtain ⟨T,ε,hε,hTU⟩ := exists_finite_tests_of_mem_nhds (perronLaw M hM) U hU
  let A (n) (f : S →ᵇ ℝ) := badTestEvent (perronLaw M hM) (x n) a b R
    (fun ν ↦ ∫ s, f s ∂(ν : Measure S)) (ε f)
  have ht : Tendsto (fun n ↦ ∑ f ∈ T, (graphLaw M lambda n (x n)).real (A n f)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum T (fun f hf ↦
      badTestEvent_probability_tendsto_zero M hM lambda a b ha hab R x D hD hround
        (fun ν ↦ ∫ s, f s ∂(ν : Measure S))
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f) (ε f) (hε f hf))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ ht
  exact Eventually.of_forall (fun n ↦ by
    have hsub : badWeakEvent (x n) a b R U ⊆ ⋃ f ∈ T, A n f := by
      rintro G ⟨C,hC⟩
      by_contra hG
      apply hC
      apply hTU
      intro f hf
      apply lt_of_not_ge
      intro hb
      apply hG
      exact Set.mem_iUnion.mpr ⟨f,Set.mem_iUnion.mpr ⟨hf,⟨C,hb⟩⟩⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le T _))

end PerronWright.FiniteIrreducibleWindowMarkConcentration
