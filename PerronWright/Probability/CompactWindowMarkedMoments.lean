import PerronWright.Probability.ComponentWindowMarkedCounts
import PerronWright.Probability.CompactAnnealedMarkedFactorialWindow
import PerronWright.Probability.CompactWindowFactorialMoments

/-! # Joint continuous marks of genuine sampled-graph window components -/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactWindowMarkedMoments

open ComponentWindowMarkedCounts ComponentWindowFactorialCounts ComponentWindowPointMeasures
  CompactAnnealedMarkedFactorialWindow CompactWindowFactorialMoments
  AnnealedMarkedResidualConcentration EmpiricalTypeMarks EmpiricalMarkConcentration FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- A joint, possibly non-product continuous test of the individual
empirical marks of actual distinct sampled-graph window components. -/
theorem windowMarkedCount_expectation_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {q : ℕ} (hq : 0 < q)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n ↦ ∫ p, windowMarkedCount p.1 (AnnealedTypedGraph.graph p) a b R Ψ
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R * Ψ (perronMarks M hM q))) := by
  apply (bounded_surplus_integer_window_marked_expectation_tendsto M hM hQP hq R lambda a b ha hab Ψ hΨ).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  have he := windowMarkedCount_expectation_eq_sum M lambda a b (ha.le.trans hab) R n hnpos Ψ hΨ
  rw [integerWindow_eq_indices hh (ha.le.trans hab),sum_bounded_surplus] at he
  exact he.symm

/-- Genuine joint component-mark deviations vanish even after summing
over all actual ordered distinct components in the window. -/
theorem windowMarkedCount_deviation_expectation_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {q : ℕ} (hq : 0 < q)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n ↦ ∫ p, windowMarkedCount p.1 (AnnealedTypedGraph.graph p) a b R
      (fun ν ↦ |Ψ ν-Ψ (perronMarks M hM q)|)
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) atTop (𝓝 0) := by
  simpa only [sub_self,abs_zero,mul_zero] using
    windowMarkedCount_expectation_tendsto M hM hQP lambda a b ha hab R hq
      (fun ν ↦ |Ψ ν-Ψ (perronMarks M hM q)|) ((hΨ.sub continuous_const).abs)

def singleTupleEquiv (I : Type*) : (Fin 1 ↪ I) ≃ I where
  toFun t := t 0
  invFun x := ⟨fun _ ↦ x,fun i j _ ↦ Subsingleton.elim i j⟩
  left_inv t := by
    apply Function.Embedding.ext
    intro i
    exact congrArg t (Subsingleton.elim 0 i)
  right_inv _ := rfl

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem windowMarkedCount_single_eq_sum {n : ℕ} (x : Fin n → S)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (F : ProbabilityMeasure S → ℝ) :
    windowMarkedCount x G a b R (fun ν : Fin 1 → ProbabilityMeasure S ↦ F (ν 0)) =
      ∑ C : WindowComponent a b R 1 G, F (componentMark x C.val) := by
  unfold windowMarkedCount
  exact Fintype.sum_equiv (singleTupleEquiv _) _ _ (fun _ ↦ rfl)

/-- This is a sum over actual graph components, not marks sampled from a
connected-law auxiliary space. -/
def windowMarkDeviation (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) : ℝ :=
  ∑ C : WindowComponent a b R 1 G,
    |F (componentMark x C.val)-F (perronMark M hM)|

theorem windowMarkDeviation_nonneg (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) : 0 ≤ windowMarkDeviation M hM x G a b R F :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem windowMarkDeviation_integrable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) :
    Integrable (fun p ↦ windowMarkDeviation M hM p.1 (AnnealedTypedGraph.graph p) a b R F)
      (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) := by
  have hc : Continuous (fun ν : Fin 1 → ProbabilityMeasure S ↦
      |F (ν 0)-F (perronMark M hM)|) :=
    ((hF.comp (continuous_apply 0)).sub continuous_const).abs
  have hi := windowMarkedCount_integrable M lambda a b R n _ hc
  exact hi.congr (Eventually.of_forall (fun p ↦
    windowMarkedCount_single_eq_sum p.1 (AnnealedTypedGraph.graph p) a b R
      (fun ν ↦ |F ν-F (perronMark M hM)|)))

/-- Expected total mark deviation across the actual entire graph window
tends to zero. In particular no selection of a single random component
or conditioning on a positive component count is required. -/
theorem windowMarkDeviation_expectation_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) :
    Tendsto (fun n ↦ ∫ p, windowMarkDeviation M hM p.1 (AnnealedTypedGraph.graph p) a b R F
      ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n) atTop (𝓝 0) := by
  have ht := windowMarkedCount_deviation_expectation_tendsto_zero M hM hQP lambda a b ha hab R
    (by norm_num : 0 < 1) (fun ν : Fin 1 → ProbabilityMeasure S ↦ F (ν 0))
      (hF.comp (continuous_apply 0))
  simp only [perronMarks] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n ↦ integral_congr_ae (Eventually.of_forall (fun p ↦
    windowMarkedCount_single_eq_sum p.1 (AnnealedTypedGraph.graph p) a b R
      (fun ν ↦ |F ν-F (perronMark M hM)|))))

end PerronWright.CompactWindowMarkedMoments
