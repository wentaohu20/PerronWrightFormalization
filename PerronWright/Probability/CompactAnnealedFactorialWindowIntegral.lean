import PerronWright.Probability.CompactAnnealedFactorialBound
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Window integrals of the actual floor-size factorial formula

The finite graph expectations are measurable step functions of the size
coordinates. Their window integrals converge to the literal density
integrals using the proved actual-model bounds. No Riemann-sum or
factorial-moment identification is assumed here.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Topology Classical

noncomputable section

namespace PerronWright.CompactAnnealedFactorialWindowIntegral

open CompactAnnealedFactorialLocal CompactAnnealedFactorialSequence
  CompactAnnealedFactorialBound FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem measurable_localExpectation (M : CompactBJRModel S)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (r : Fin q → ℕ) :
    Measurable (fun x : Fin q → ℝ ↦ localExpectation M lambda n x r) := by
  let E : (Fin q → ℕ) → ℝ := fun k ↦
    (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n
  have hsize : Measurable (fun x : Fin q → ℝ ↦
      fun i ↦ CriticalScaling.size (x i) n) := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun x : Fin q → ℝ ↦ ⌊x i * (n : ℝ)^(2/3 : ℝ)⌋₊)
    have hc : Measurable (fun x : Fin q → ℝ ↦ x i) := measurable_pi_apply i
    exact (hc.mul_const ((n : ℝ)^(2/3 : ℝ))).nat_floor
  exact (measurable_of_countable E).comp hsize

theorem eventually_integrableOn_localExpectation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∀ᶠ n in atTop,
      IntegrableOn (fun x ↦ localExpectation M lambda n x r) (sizeWindow q a b) volume := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B, -, hbound⟩ := exists_uniform_scaled_bound M hM hQP hq R lambda a b ha hab
  let : IsFiniteMeasure (volume.restrict (sizeWindow q a b)) :=
    isFiniteMeasure_restrict.mpr (by
      change volume (Set.Icc (fun _ : Fin q ↦ a) (fun _ ↦ b)) ≠ ⊤
      exact isCompact_Icc.measure_lt_top.ne)
  filter_upwards [hbound] with n hn
  apply (integrable_const B).mono' (measurable_localExpectation M lambda n r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa only [Real.norm_eq_abs] using hn r hr x hx

/-- The actual scaled finite-graph step functions integrate to the literal
fixed-surplus window density in the limit. -/
theorem localExpectation_window_integral_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n ↦ ∫ x in sizeWindow q a b, localExpectation M lambda n x r)
      atTop (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r)) := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B, -, hbound⟩ := exists_uniform_scaled_bound M hM hQP hq R lambda a b ha hab
  let : IsFiniteMeasure (volume.restrict (sizeWindow q a b)) :=
    isFiniteMeasure_restrict.mpr (by
      change volume (Set.Icc (fun _ : Fin q ↦ a) (fun _ ↦ b)) ≠ ⊤
      exact isCompact_Icc.measure_lt_top.ne)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
  · exact Eventually.of_forall (fun n ↦
      (measurable_localExpectation M lambda n r).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa only [Real.norm_eq_abs] using hn r hr x hx
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact factorial_pointwise_tendsto M hM hQP hq r x lambda a b ha (ha.le.trans hab)
      (fun i ↦ (mem_sizeWindow.mp hx i).1) (fun i ↦ (mem_sizeWindow.mp hx i).2)

end PerronWright.CompactAnnealedFactorialWindowIntegral
