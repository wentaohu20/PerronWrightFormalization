import PerronWright.Probability.CompactAnnealedMarkedFactorialGrid
import PerronWright.Probability.CriticalFloorWindow

/-! # Actual integer-window moments carrying coupled empirical mark tests -/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactAnnealedMarkedFactorialWindow

open CriticalFloorWindow CompactAnnealedMarkedFactorialLocal
  CompactAnnealedMarkedFactorialSequence CompactAnnealedMarkedFactorialGrid
  AnnealedMarkedFactorialCounting AnnealedMarkedResidualConcentration FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem grid_indicator_localMarkedExpectation_integral_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∫ x in sizeWindow q (a/2) (b+1),
      (grid q ((n : ℝ)^(2/3 : ℝ)) a b).indicator
        (fun x ↦ localMarkedExpectation M lambda n x r Ψ) x)
      atTop (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r *
        Ψ (perronMarks M hM q))) := by
  let U := sizeWindow q (a/2) (b+1)
  have hUa : 0 < a/2 := by positivity
  have hUab : a/2 ≤ b+1 := by linarith
  have hsub : sizeWindow q a b ⊆ U := by
    intro x hx
    apply mem_sizeWindow.mpr
    intro i
    have hxi := mem_sizeWindow.mp hx i
    constructor
    · linarith [hxi.1]
    · linarith [hxi.2]
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    change volume (Set.Icc (fun _ : Fin q ↦ a/2) (fun _ ↦ b+1)) ≠ ⊤
    exact isCompact_Icc.measure_lt_top.ne)
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B,hB,hbound⟩ := exists_uniform_scaled_bound M hM hQP hq R lambda (a/2) (b+1) hUa hUab Ψ hΨ
  have hwms : MeasurableSet (sizeWindow q a b) := measurableSet_Icc
  have heq : (∫ x in U, (sizeWindow q a b).indicator
      (fun x ↦ density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)) x) =
      fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r * Ψ (perronMarks M hM q) := by
    rw [setIntegral_indicator hwms,Set.inter_eq_right.mpr hsub,integral_mul_const]
    rfl
  rw [← heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
  · exact Eventually.of_forall (fun n ↦ ((measurable_localMarkedExpectation M lambda n r Ψ).indicator
      (measurableSet_grid q _ a b)).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc] with x hx
    by_cases hg : x ∈ grid q ((n : ℝ)^(2/3 : ℝ)) a b
    · simpa only [Set.indicator_of_mem hg,Real.norm_eq_abs] using hn r hr x hx
    · simp only [Set.indicator_of_notMem hg,norm_zero]
      exact hB.le
  · exact integrable_const B
  · have hae : (Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) =ᵐ[(volume : Measure (Fin q → ℝ))]
        sizeWindow q a b := Measure.univ_pi_Ioo_ae_eq_Icc
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc,ae_restrict_of_ae hae] with x hx he
    have hxpos (i) : 0 ≤ x i := hUa.le.trans (mem_sizeWindow.mp hx i).1
    have hevent := critical_grid_indicator_eventually ha hab hxpos (Iff.of_eq he)
    by_cases hw : x ∈ sizeWindow q a b
    · simpa only [Set.indicator_of_mem hw] using
        (marked_factorial_pointwise_tendsto M hM hQP hq r x lambda (a/2) (b+1) hUa
          (by linarith) (fun i ↦ (mem_sizeWindow.mp hx i).1)
          (fun i ↦ (mem_sizeWindow.mp hx i).2) Ψ hΨ).congr' (by
            filter_upwards [hevent] with n hn
            exact (Set.indicator_of_mem (hn.mpr hw)
              (fun x ↦ localMarkedExpectation M lambda n x r Ψ)).symm)
    · simp only [Set.indicator_of_notMem hw]
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [hevent] with n hn
      exact (Set.indicator_of_notMem (fun h ↦ hw (hn.mp h))
        (fun x ↦ localMarkedExpectation M lambda n x r Ψ)).symm

/-- No Riemann-sum assumption: these are the actual sampled-type graph
tuple expectations summed over the literal integer size window. -/
theorem integer_window_marked_expectation_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ indices q ((n : ℝ)^(2/3 : ℝ)) a b,
      ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n) atTop
      (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r *
        Ψ (perronMarks M hM q))) := by
  apply (grid_indicator_localMarkedExpectation_integral_tendsto M hM hQP hq r lambda a b ha hab Ψ hΨ).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  have hsmall : 1/(n : ℝ)^(2/3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hh).mpr
    simpa only [one_mul] using Real.one_le_rpow (by exact_mod_cast hn) (by norm_num : (0 : ℝ) ≤ 2/3)
  have hsub := grid_subset_expanded (q := q) hh ha (ha.le.trans hab) hsmall
  rw [setIntegral_indicator (measurableSet_grid q _ a b),Set.inter_eq_right.mpr hsub]
  exact integral_localMarkedExpectation_grid M lambda hnpos _ r Ψ

theorem bounded_surplus_integer_window_marked_expectation_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∑ rr : Fin q → Fin (R+1),
      ∑ k ∈ indices q ((n : ℝ)^(2/3 : ℝ)) a b,
        ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k (fun i ↦ (rr i).val) Ψ
          ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R * Ψ (perronMarks M hM q))) := by
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin q → Fin (R+1))) (fun rr _ ↦
    integer_window_marked_expectation_tendsto M hM hQP hq
      (fun i ↦ (rr i).val) lambda a b ha hab Ψ hΨ)
  simpa only [← Finset.sum_mul,windowMass] using ht

end PerronWright.CompactAnnealedMarkedFactorialWindow
