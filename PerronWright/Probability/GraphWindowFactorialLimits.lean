import PerronWright.Probability.GraphWindowSource
import PerronWright.Probability.CriticalFloorWindow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # From proved local graph formulas to actual window count limits

This composition theorem uses the literal floor expectation of an actual
finite graph law. Full-cell integration, dominated convergence, and the
proved factorial moment construction yield the actual window number law
and point-law tightness. The countable-model terminal discharges the local
formula from its already proved realization theorem; no target law or
moment-limit interface is postulated here.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowFactorialLimits

open GraphWindowSource CriticalFloorWindow FactorialDensity
open FinitePointMeasureCompact FinitePointMeasurePolish
open FactorialCountDeterminacy FactorialCountLimitExistence
open CompactWindowFactorialMoments (integerWindow_eq_indices sum_bounded_surplus windowMass_zero)

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

/-- The precise numeric local conclusion consumed by this proved bridge. -/
def HasUniformLocalLimit (alpha beta lambda : ℝ) : Prop :=
  ∀ q R : ℕ, 0 < q → ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε > 0,
    ∀ᶠ n in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |localExpectation ρ n y r - density alpha beta lambda y r| < ε

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem factorial_pointwise_tendsto {alpha beta lambda : ℝ}
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (y : Fin q → ℝ) (hya : ∀ i, a ≤ y i) (hyb : ∀ i, y i ≤ b) :
    Tendsto (fun n ↦ localExpectation ρ n y r) atTop
      (𝓝 (density alpha beta lambda y r)) := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlocal q R hq a b ha hab ε hε] with n hn
  rw [Real.dist_eq]
  exact hn y r hya hyb hr

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem exists_uniform_scaled_bound {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (R : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ y ∈ sizeWindow q a b, |localExpectation ρ n y r| ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_density_window_bound (b := b) hbeta ha R
  let B := C^q * Real.exp (-beta * (a*q)^3/24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  refine ⟨B+1, by linarith, ?_⟩
  filter_upwards [hlocal q R hq a b ha hab 1 (by norm_num)] with n hn r hr y hy
  have hya := fun i ↦ (mem_sizeWindow.mp hy i).1
  have hyb := fun i ↦ (mem_sizeWindow.mp hy i).2
  have he := hn y r hya hyb hr
  have hd := density_pos alpha lambda hbeta y r (fun i ↦ ha.trans_le (hya i))
  have hbnd := hbound q alpha lambda y r (mem_sizeWindow.mp hy) hr
  change density alpha beta lambda y r ≤ B at hbnd
  have h := abs_add_le (localExpectation ρ n y r - density alpha beta lambda y r)
    (density alpha beta lambda y r)
  rw [sub_add_cancel, abs_of_pos hd] at h
  exact h.trans (by linarith)

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem grid_indicator_integral_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ ↦ ∫ x in sizeWindow q (a/2) (b+1),
      (grid q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b).indicator
        (fun x ↦ localExpectation ρ n x r) x) atTop
      (𝓝 (fixedSurplusWindowMass alpha beta lambda a b r)) := by
  let U := sizeWindow q (a/2) (b+1)
  have hUa : 0 < a/2 := by positivity
  have hUab : a/2 ≤ b+1 := by linarith
  have hsub : sizeWindow q a b ⊆ U := by
    intro x hx
    apply mem_sizeWindow.mpr
    intro i
    have hxi := mem_sizeWindow.mp hx i
    constructor <;> linarith [hxi.1, hxi.2]
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    change volume (Set.Icc (fun _ : Fin q ↦ a/2) (fun _ ↦ b+1)) ≠ ⊤
    exact isCompact_Icc.measure_lt_top.ne)
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B, hB, hbound⟩ := exists_uniform_scaled_bound ρ hbeta hlocal hq R hUa hUab
  have hwms : MeasurableSet (sizeWindow q a b) := measurableSet_Icc
  have heq : (∫ x in U, (sizeWindow q a b).indicator
      (fun x ↦ density alpha beta lambda x r) x) =
      fixedSurplusWindowMass alpha beta lambda a b r := by
    rw [setIntegral_indicator hwms, Set.inter_eq_right.mpr hsub]
    rfl
  rw [← heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
  · exact Eventually.of_forall (fun n ↦ ((measurable_localExpectation ρ n r).indicator
      (measurableSet_grid q _ a b)).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc] with x hx
    by_cases hg : x ∈ grid q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b
    · simpa only [Set.indicator_of_mem hg, Real.norm_eq_abs] using hn r hr x hx
    · simp only [Set.indicator_of_notMem hg, norm_zero]
      exact hB.le
  · exact integrable_const B
  · have hae : (Set.univ.pi (fun _ : Fin q ↦ Set.Ioo a b)) =ᵐ[(volume : Measure (Fin q → ℝ))]
        sizeWindow q a b := Measure.univ_pi_Ioo_ae_eq_Icc
    filter_upwards [ae_restrict_mem (s := U) measurableSet_Icc, ae_restrict_of_ae hae] with x hx he
    have hxpos (i) : 0 ≤ x i := hUa.le.trans (mem_sizeWindow.mp hx i).1
    have hevent := (tendsto_add_atTop_nat 1).eventually
      (critical_grid_indicator_eventually ha hab hxpos (Iff.of_eq he))
    by_cases hw : x ∈ sizeWindow q a b
    · simpa only [Set.indicator_of_mem hw] using
        (factorial_pointwise_tendsto ρ hlocal hq r hUa hUab x
          (fun i ↦ (mem_sizeWindow.mp hx i).1) (fun i ↦ (mem_sizeWindow.mp hx i).2)).congr' (by
            filter_upwards [hevent] with n hn
            exact (Set.indicator_of_mem (hn.mpr hw)
              (fun x ↦ localExpectation ρ n x r)).symm)
    · simp only [Set.indicator_of_notMem hw]
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [hevent] with n hn
      exact (Set.indicator_of_notMem (fun h ↦ hw (hn.mp h))
        (fun x ↦ localExpectation ρ n x r)).symm

omit [∀ n, IsProbabilityMeasure (ρ n)] in
theorem integer_window_expectation_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ indices q (((n+1 : ℕ) : ℝ)^(2/3 : ℝ)) a b,
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂ρ n) atTop
      (𝓝 (fixedSurplusWindowMass alpha beta lambda a b r)) := by
  apply (grid_indicator_integral_tendsto ρ hbeta hlocal hq r ha hab).congr'
  filter_upwards [] with n
  have hh : 0 < ((n+1 : ℕ) : ℝ)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
  have hsmall : 1/((n+1 : ℕ) : ℝ)^(2/3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hh).mpr
    simpa only [one_mul] using Real.one_le_rpow
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by norm_num : (0 : ℝ) ≤ 2/3)
  have hsub := grid_subset_expanded (q := q) hh ha (ha.le.trans hab) hsmall
  rw [setIntegral_indicator (measurableSet_grid q _ a b), Set.inter_eq_right.mpr hsub]
  exact integral_localExpectation_grid ρ _ r

theorem windowLaw_all_factorial_moments_tendsto {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R q : ℕ) :
    Tendsto (fun n ↦ ∫ η, ((size η).descFactorial q : ℝ)
      ∂(windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R)))) atTop
      (𝓝 (windowMass q alpha beta lambda a b R)) := by
  cases q with
  | zero =>
    simpa only [Nat.descFactorial_zero, Nat.cast_one, integral_const, probReal_univ,
      smul_eq_mul, mul_one, windowMass_zero _ _ _ _ _ hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  | succ q =>
    have ht := tendsto_finsetSum Finset.univ (fun rr : Fin (q+1) → Fin (R+1) ↦ fun _ ↦
      integer_window_expectation_tendsto ρ hbeta hlocal (Nat.succ_pos q)
        (fun i ↦ (rr i).val) ha hab)
    change Tendsto _ atTop (𝓝 (windowMass (q+1) alpha beta lambda a b R)) at ht
    apply ht.congr'
    filter_upwards [] with n
    have hh : 0 < ((n+1 : ℕ) : ℝ)^(2/3 : ℝ) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _
    have he := windowLaw_descFactorial_expectation_eq_sum ρ a b (ha.le.trans hab) R n (q+1)
    rw [integerWindow_eq_indices hh (ha.le.trans hab), sum_bounded_surplus] at he
    exact he.symm

theorem exists_unique_actualCountLaw_limit {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (Fin 1 → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (Fin 1 → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (Fin 1 → ℕ)) q =
        windowMass (q 0) alpha beta lambda a b R) ∧
      Tendsto (actualCountLaw ρ a b R) atTop (𝓝 ν) := by
  apply exists_unique_limit_of_factorialMoments (actualCountLaw ρ a b R)
    (actualCountLaw_factorial_integrable ρ a b R)
    (fun q ↦ windowMass (q 0) alpha beta lambda a b R)
  · intro q
    simp_rw [actualCountLaw_factorialMoment]
    exact windowLaw_all_factorial_moments_tendsto ρ hbeta hlocal ha hab R (q 0)
  · exact CompactWindowCountLaw.singleton_windowMass_series _ _ hbeta ha hab R

theorem windowLaw_mass_tendsto {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ ∫ η, (mass η : ℝ)
      ∂(windowLaw ρ a b R n : Measure (PointMeasure (SurplusWindow a b R)))) atTop
      (𝓝 (windowMass 1 alpha beta lambda a b R)) := by
  have he (η : PointMeasure (SurplusWindow a b R)) :
      ((size η).descFactorial 1 : ℝ) = (mass η : ℝ) := by
    rw [Nat.descFactorial_one]
    exact_mod_cast (mass_eq_size η).symm
  simpa only [he] using windowLaw_all_factorial_moments_tendsto ρ hbeta hlocal ha hab R 1

theorem exists_window_mass_bound {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ η, (mass η : ℝ) ∂(windowLaw ρ a b R n :
        Measure (PointMeasure (SurplusWindow a b R)))) ≤ B := by
  let F (n : ℕ) := ∫ η, (mass η : ℝ) ∂(windowLaw ρ a b R n :
    Measure (PointMeasure (SurplusWindow a b R)))
  let L := windowMass 1 alpha beta lambda a b R
  have ht := windowLaw_mass_tendsto ρ hbeta hlocal ha hab R
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds (lt_add_one L)))
  let B := |L|+1+∑ n ∈ Finset.range N, |F n|
  have hs : 0 ≤ ∑ n ∈ Finset.range N, |F n| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hb := hN n hn
    change F n < L+1 at hb
    change F n ≤ B
    dsimp only [B]
    have hL : L ≤ |L| := le_abs_self _
    linarith
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hl := Finset.single_le_sum (fun i _ ↦ abs_nonneg (F i)) hm
    change F n ≤ B
    dsimp only [B]
    have habs : F n ≤ |F n| := le_abs_self _
    linarith [abs_nonneg L]

theorem isTight_windowLaws {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsTightMeasureSet (Set.range (fun n ↦ (windowLaw ρ a b R n :
      Measure (PointMeasure (SurplusWindow a b R))))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound ρ hbeta hlocal ha hab R
  exact isTightMeasureSet_of_mass_moment_bound (windowLaw ρ a b R)
    (windowLaw_mass_integrable ρ a b R) B hB hb

theorem isCompact_closure_windowLaws {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    IsCompact (closure (Set.range (windowLaw ρ a b R))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound ρ hbeta hlocal ha hab R
  exact isCompact_closure_of_mass_moment_bound (windowLaw ρ a b R)
    (windowLaw_mass_integrable ρ a b R) B hB hb

end PerronWright.GraphWindowFactorialLimits
