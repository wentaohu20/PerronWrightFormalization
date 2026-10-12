import PerronWright.Probability.FiniteIrreducibleMarkedWindowGrid
import PerronWright.Probability.ComponentWindowMarkedCounts
import PerronWright.Probability.CompactWindowMarkedMoments
import PerronWright.Probability.CriticalFloorWindow

/-! # Genuine deterministic window factorial integrals of coupled empirical marks

The moving union of full floor cells converges almost everywhere to the
literal window. Dominated convergence uses the actual finite-model marked
local-main bound. In particular expected total mark deviation vanishes.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleMarkedWindowMoments

open CriticalFloorWindow FiniteIrreducibleMarkedWindowGrid
  FiniteIrreducibleNativeMarkConcentration FiniteIrreducibleComponentProcess
  ComponentWindowMarkedCounts ComponentWindowFactorialCounts ComponentWindowPointMeasures
  CompactWindowFactorialMoments
  AnnealedMarkedFactorialCounting EmpiricalTypeMarks FactorialDensity
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem grid_indicator_marked_integral_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∫ y in sizeWindow q (a/2) (b+1),
      (grid q ((n : ℝ)^(2/3 : ℝ)) a b).indicator
        (fun y ↦ localMarkedExpectation M lambda n (x n) y r Ψ) y) atTop
      (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r *
        Ψ (perronMarks M hM q))) := by
  let U := sizeWindow q (a/2) (b+1)
  have hUa : 0 < a/2 := by positivity
  have hUab : a/2 ≤ b+1 := by linarith
  have hsub : sizeWindow q a b ⊆ U := by
    intro y hy
    apply mem_sizeWindow.mpr
    intro i
    have h := mem_sizeWindow.mp hy i
    constructor <;> linarith [h.1,h.2]
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    change volume (Set.Icc (fun _ : Fin q ↦ a/2) (fun _ ↦ b+1)) ≠ ⊤
    exact isCompact_Icc.measure_lt_top.ne)
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B,hB,hbound⟩ := exists_uniform_scaled_marked_bound M hM hq R lambda
    (a/2) (b+1) hUa hUab x D hD hround Ψ hΨ
  have hwms : MeasurableSet (sizeWindow q a b) := measurableSet_Icc
  have heq : (∫ y in U, (sizeWindow q a b).indicator
      (fun y ↦ density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)) y) =
      fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r * Ψ (perronMarks M hM q) := by
    rw [setIntegral_indicator hwms,Set.inter_eq_right.mpr hsub,integral_mul_const]
    rfl
  rw [← heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
  · exact Eventually.of_forall (fun n ↦ ((measurable_localMarkedExpectation M lambda n (x n) r Ψ).indicator
      (measurableSet_grid q _ a b)).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc] with y hy
    by_cases hg : y ∈ grid q ((n : ℝ)^(2/3 : ℝ)) a b
    · simpa only [Set.indicator_of_mem hg,Real.norm_eq_abs] using hn r hr y hy
    · simp only [Set.indicator_of_notMem hg,norm_zero]
      exact hB.le
  · exact integrable_const B
  · have hae : (Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) =ᵐ[(volume : Measure (Fin q → ℝ))]
        sizeWindow q a b := Measure.univ_pi_Ioo_ae_eq_Icc
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc,ae_restrict_of_ae hae] with y hy he
    have hypos (i) : 0 ≤ y i := hUa.le.trans (mem_sizeWindow.mp hy i).1
    have hevent := critical_grid_indicator_eventually ha hab hypos (Iff.of_eq he)
    by_cases hw : y ∈ sizeWindow q a b
    · simpa only [Set.indicator_of_mem hw] using
        (marked_pointwise_tendsto M hM hq r lambda (a/2) (b+1) hUa (by linarith)
          x D hD hround y (fun i ↦ (mem_sizeWindow.mp hy i).1)
          (fun i ↦ (mem_sizeWindow.mp hy i).2) Ψ hΨ).congr' (by
            filter_upwards [hevent] with n hn
            exact (Set.indicator_of_mem (hn.mpr hw)
              (fun y ↦ localMarkedExpectation M lambda n (x n) y r Ψ)).symm)
    · simp only [Set.indicator_of_notMem hw]
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [hevent] with n hn
      exact (Set.indicator_of_notMem (fun h ↦ hw (hn.mp h))
        (fun y ↦ localMarkedExpectation M lambda n (x n) y r Ψ)).symm

theorem integer_window_marked_expectation_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ indices q ((n : ℝ)^(2/3 : ℝ)) a b,
      ∫ G, markedCount (x n) G k r Ψ ∂graphLaw M lambda n (x n)) atTop
      (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r *
        Ψ (perronMarks M hM q))) := by
  apply (grid_indicator_marked_integral_tendsto M hM hq r lambda a b ha hab x D hD hround Ψ hΨ).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  have hsmall : 1/(n : ℝ)^(2/3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hh).mpr
    simpa only [one_mul] using Real.one_le_rpow (by exact_mod_cast hn) (by norm_num : (0 : ℝ) ≤ 2/3)
  have hsub := grid_subset_expanded (q := q) hh ha (ha.le.trans hab) hsmall
  rw [setIntegral_indicator (measurableSet_grid q _ a b),Set.inter_eq_right.mpr hsub]
  exact integral_localMarkedExpectation_grid M lambda hnpos (x n) _ r Ψ

theorem bounded_surplus_integer_window_marked_expectation_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n : ℕ ↦ ∑ rr : Fin q → Fin (R+1),
      ∑ k ∈ indices q ((n : ℝ)^(2/3 : ℝ)) a b,
        ∫ G, markedCount (x n) G k (fun i ↦ (rr i).val) Ψ ∂graphLaw M lambda n (x n)) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R * Ψ (perronMarks M hM q))) := by
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin q → Fin (R+1))) (fun rr _ ↦
    integer_window_marked_expectation_tendsto M hM hq (fun i ↦ (rr i).val)
      lambda a b ha hab x D hD hround Ψ hΨ)
  simpa only [← Finset.sum_mul,windowMass] using ht

theorem windowMarkedCount_expectation_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n ↦ ∫ G, windowMarkedCount (x n) G a b R Ψ ∂graphLaw M lambda n (x n)) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R * Ψ (perronMarks M hM q))) := by
  apply (bounded_surplus_integer_window_marked_expectation_tendsto M hM hq R
    lambda a b ha hab x D hD hround Ψ hΨ).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  simp_rw [windowMarkedCount_eq_sum _ _ hnpos a b (ha.le.trans hab) R Ψ]
  rw [integral_finsetSum]
  · simp_rw [integerWindow_eq_indices hh (ha.le.trans hab)]
    rw [sum_bounded_surplus]
    exact (Finset.sum_congr rfl (fun r _ ↦ integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite))).symm
  · intro _ _
    exact Integrable.of_finite

theorem windowMarkedCount_deviation_expectation_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n ↦ ∫ G, windowMarkedCount (x n) G a b R
      (fun ν ↦ |Ψ ν-Ψ (perronMarks M hM q)|) ∂graphLaw M lambda n (x n)) atTop (𝓝 0) := by
  simpa only [sub_self,abs_zero,mul_zero] using
    windowMarkedCount_expectation_tendsto M hM hq R lambda a b ha hab x D hD hround
      (fun ν ↦ |Ψ ν-Ψ (perronMarks M hM q)|) ((hΨ.sub continuous_const).abs)

/-- Total deviation is a sum over the actual graph's window components. -/
def windowMarkDeviation (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) : ℝ :=
  ∑ C : WindowComponent a b R 1 G,
    |F (componentMark x C.val)-F (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM)|

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem windowMarkDeviation_nonneg (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ)
    (F : ProbabilityMeasure S → ℝ) : 0 ≤ windowMarkDeviation M hM x G a b R F :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem windowMarkDeviation_expectation_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) :
    Tendsto (fun n ↦ ∫ G, windowMarkDeviation M hM (x n) G a b R F
      ∂graphLaw M lambda n (x n)) atTop (𝓝 0) := by
  have ht := windowMarkedCount_deviation_expectation_tendsto_zero M hM
    (by norm_num : 0 < 1) R lambda a b ha hab x D hD hround
    (fun ν : Fin 1 → ProbabilityMeasure S ↦ F (ν 0)) (hF.comp (continuous_apply 0))
  simp only [perronMarks] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n ↦ integral_congr_ae (Eventually.of_forall (fun G ↦
    CompactWindowMarkedMoments.windowMarkedCount_single_eq_sum (x n) G a b R
      (fun ν ↦ |F ν-F (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM)|))))

end PerronWright.FiniteIrreducibleMarkedWindowMoments
