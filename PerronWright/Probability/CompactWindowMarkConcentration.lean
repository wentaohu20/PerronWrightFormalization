import PerronWright.Probability.CompactWindowMarkedMoments
import PerronWright.Probability.EmpiricalWeakNeighborhood

/-! # All genuine graph-window component marks concentrate weakly

The bad event quantifies over actual window connected components in the
joint sampled graph/type probability space. Markov's inequality uses
the proved expected total actual component-mark deviation, not an
assumed connected-law or residual-law concentration interface.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped Real BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactWindowMarkConcentration

open CompactWindowMarkedMoments ComponentWindowPointMeasures EmpiricalTypeMarks
  EmpiricalMarkConcentration EmpiricalWeakNeighborhood

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def badTestEvent (ν : ProbabilityMeasure S) (a b : ℝ) (R n : ℕ)
    (F : ProbabilityMeasure S → ℝ) (ε : ℝ) : Set (AnnealedTypedGraph.State S n) :=
  {p | ∃ C : WindowComponent a b R 1 (AnnealedTypedGraph.graph p),
    ε ≤ |F (componentMark p.1 C.val)-F ν|}

theorem badTestEvent_measurableSet (ν : ProbabilityMeasure S) (a b : ℝ) (R n : ℕ)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) (ε : ℝ) :
    MeasurableSet (badTestEvent ν a b R n F ε) := by
  have he : badTestEvent ν a b R n F ε =
      ⋃ ea : AnnealedGraph.Assignment n,
        ({x : Fin n → S | ∃ C : WindowComponent a b R 1 (AnnealedGraph.toGraph ea),
          ε ≤ |F (componentMark x C.val)-F ν|} ×ˢ {ea}) := by
    ext ⟨x,ea⟩
    simp [badTestEvent,AnnealedTypedGraph.graph]
  rw [he]
  apply MeasurableSet.iUnion
  intro ea
  apply MeasurableSet.prod _ (measurableSet_singleton ea)
  have hs (C : WindowComponent a b R 1 (AnnealedGraph.toGraph ea)) :
      MeasurableSet {x : Fin n → S | ε ≤ |F (componentMark x C.val)-F ν|} :=
    measurableSet_le measurable_const
      (((hF.comp (AnnealedMarkedFactorialCounting.componentMark_continuous C.val)).sub continuous_const).abs.measurable)
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hs

theorem badTestEvent_probability_le (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) (F : ProbabilityMeasure S → ℝ) (hF : Continuous F)
    (ε : ℝ) (hε : 0 < ε) :
    (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real (badTestEvent (perronMark M hM) a b R n F ε) ≤
        (∫ p, windowMarkDeviation M hM p.1 (AnnealedTypedGraph.graph p) a b R F
          ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n) / ε := by
  let μ := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n
  let D : AnnealedTypedGraph.State S n → ℝ := fun p ↦
    windowMarkDeviation M hM p.1 (AnnealedTypedGraph.graph p) a b R F
  have hI : Integrable D μ := windowMarkDeviation_integrable M hM lambda a b R n F hF
  have hpos (p) : 0 ≤ D p := windowMarkDeviation_nonneg M hM _ _ a b R F
  have hh : μ (badTestEvent (perronMark M hM) a b R n F ε) ≤
      ENNReal.ofReal (∫ p, D p / ε ∂μ) :=
    (hI.div_const ε).measure_le_integral
      (Eventually.of_forall (fun p ↦ div_nonneg (hpos p) hε.le)) (fun p hp ↦ by
        obtain ⟨C,hC⟩ := hp
        apply (le_div_iff₀ hε).mpr
        simp only [one_mul]
        apply hC.trans
        change |F (componentMark p.1 C.val)-F (perronMark M hM)| ≤
          ∑ C : WindowComponent a b R 1 (AnnealedTypedGraph.graph p),
            |F (componentMark p.1 C.val)-F (perronMark M hM)|
        exact Finset.single_le_sum
          (f := fun C : WindowComponent a b R 1 (AnnealedTypedGraph.graph p) ↦
            |F (componentMark p.1 C.val)-F (perronMark M hM)|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ C))
  change (μ (badTestEvent (perronMark M hM) a b R n F ε)).toReal ≤ (∫ p, D p ∂μ) / ε
  calc
    _ ≤ (ENNReal.ofReal (∫ p, D p / ε ∂μ)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = _ := by
      rw [integral_div,ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hpos) hε.le)]

/-- The probability that even one actual window component fails a
fixed continuous mark test tends to zero. -/
theorem badTestEvent_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real
        (badTestEvent (perronMark M hM) a b R n F ε)) atTop (𝓝 0) := by
  have ht := (windowMarkDeviation_expectation_tendsto_zero M hM hQP lambda a b ha hab R F hF).div_const ε
  simp only [zero_div] at ht
  exact squeeze_zero'
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    (Eventually.of_forall (fun n ↦ badTestEvent_probability_le M hM lambda a b R n F hF ε hε)) ht

def badWeakEvent (a b : ℝ) (R n : ℕ) (U : Set (ProbabilityMeasure S)) :
    Set (AnnealedTypedGraph.State S n) :=
  {p | ∃ C : WindowComponent a b R 1 (AnnealedTypedGraph.graph p), componentMark p.1 C.val ∉ U}

/-- Open weak-neighborhood events are measurable through raw type
coordinates; no weak/Giry Borel identification is assumed. -/
theorem badWeakEvent_measurableSet (a b : ℝ) (R n : ℕ)
    (U : Set (ProbabilityMeasure S)) (hU : IsOpen U) :
    MeasurableSet (badWeakEvent a b R n U) := by
  have he : badWeakEvent a b R n U =
      ⋃ ea : AnnealedGraph.Assignment n,
        ({x : Fin n → S | ∃ C : WindowComponent a b R 1 (AnnealedGraph.toGraph ea),
          componentMark x C.val ∉ U} ×ˢ {ea}) := by
    ext ⟨x,ea⟩
    simp [badWeakEvent,AnnealedTypedGraph.graph]
  rw [he]
  apply MeasurableSet.iUnion
  intro ea
  apply MeasurableSet.prod _ (measurableSet_singleton ea)
  have hs (C : WindowComponent a b R 1 (AnnealedGraph.toGraph ea)) :
      MeasurableSet {x : Fin n → S | componentMark x C.val ∉ U} :=
    (hU.preimage (AnnealedMarkedFactorialCounting.componentMark_continuous C.val)).measurableSet.compl
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hs

/-- Every actual component in the requested graph window has its
individual empirical mark in any prescribed Perron weak neighborhood,
with probability tending to one. The neighborhood need not be Borel. -/
theorem badWeakEvent_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMark M hM)) :
    Tendsto (fun n ↦ (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real (badWeakEvent a b R n U)) atTop (𝓝 0) := by
  obtain ⟨T,ε,hε,hTU⟩ := exists_finite_tests_of_mem_nhds (perronMark M hM) U hU
  let μ (n) := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n
  let A (n) (f : S →ᵇ ℝ) := badTestEvent (perronMark M hM) a b R n
    (fun ν ↦ ∫ x, f x ∂(ν : Measure S)) (ε f)
  have ht : Tendsto (fun n ↦ ∑ f ∈ T, (μ n).real (A n f)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum T (fun f hf ↦
      badTestEvent_probability_tendsto_zero M hM hQP lambda a b ha hab R
        (fun ν ↦ ∫ x, f x ∂(ν : Measure S))
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f) (ε f) (hε f hf))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ ht
  exact Eventually.of_forall (fun n ↦ by
    have hsub : badWeakEvent a b R n U ⊆ ⋃ f ∈ T, A n f := by
      rintro p ⟨C,hC⟩
      by_contra hp
      apply hC
      apply hTU
      intro f hf
      apply lt_of_not_ge
      intro hb
      apply hp
      exact Set.mem_iUnion.mpr ⟨f,Set.mem_iUnion.mpr ⟨hf,⟨C,hb⟩⟩⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le T _))

def badJointWeakEvent (a b : ℝ) (R n q : ℕ)
    (U : Set (Fin q → ProbabilityMeasure S)) : Set (AnnealedTypedGraph.State S n) :=
  {p | ∃ t : Fin q ↪ WindowComponent a b R 1 (AnnealedTypedGraph.graph p),
    (fun i ↦ componentMark p.1 (t i).val) ∉ U}

theorem badJointWeakEvent_measurableSet (a b : ℝ) (R n q : ℕ)
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : IsOpen U) :
    MeasurableSet (badJointWeakEvent a b R n q U) := by
  have he : badJointWeakEvent a b R n q U =
      ⋃ ea : AnnealedGraph.Assignment n,
        ({x : Fin n → S | ∃ t : Fin q ↪ WindowComponent a b R 1 (AnnealedGraph.toGraph ea),
          (fun i ↦ componentMark x (t i).val) ∉ U} ×ˢ {ea}) := by
    ext ⟨x,ea⟩
    simp [badJointWeakEvent,AnnealedTypedGraph.graph]
    rfl
  rw [he]
  apply MeasurableSet.iUnion
  intro ea
  apply MeasurableSet.prod _ (measurableSet_singleton ea)
  have hs (t : Fin q ↪ WindowComponent a b R 1 (AnnealedGraph.toGraph ea)) :
      MeasurableSet {x : Fin n → S | (fun i ↦ componentMark x (t i).val) ∉ U} :=
    (hU.preimage (continuous_pi (fun i ↦
      AnnealedMarkedFactorialCounting.componentMark_continuous (t i).val))).measurableSet.compl
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hs

/-- All actual ordered distinct component tuples in the graph window
simultaneously have their individual joint empirical weak marks close
to the Perron marks. This is a statement about the actual typed graph. -/
theorem badJointWeakEvent_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R q : ℕ)
    (U : Set (Fin q → ProbabilityMeasure S))
    (hU : U ∈ 𝓝 (AnnealedMarkedResidualConcentration.perronMarks M hM q)) :
    Tendsto (fun n ↦ (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).real (badJointWeakEvent a b R n q U)) atTop (𝓝 0) := by
  rw [nhds_pi] at hU
  obtain ⟨I,V,hV,hVU⟩ := Filter.mem_pi'.mp hU
  let μ (n) := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n
  have ht : Tendsto (fun n ↦ ∑ i : Fin q, (μ n).real (badWeakEvent a b R n (V i)))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ ↦
        badWeakEvent_probability_tendsto_zero M hM hQP lambda a b ha hab R (V i) (hV i))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ ht
  exact Eventually.of_forall (fun n ↦ by
    have hsub : badJointWeakEvent a b R n q U ⊆
        ⋃ i ∈ (Finset.univ : Finset (Fin q)), badWeakEvent a b R n (V i) := by
      rintro p ⟨t,ht⟩
      by_contra hp
      apply ht
      apply hVU
      intro i _
      by_contra hi
      apply hp
      exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_univ i,⟨t i,hi⟩⟩⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le Finset.univ _))

end PerronWright.CompactWindowMarkConcentration
