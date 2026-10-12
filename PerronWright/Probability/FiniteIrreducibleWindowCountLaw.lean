import PerronWright.Probability.FiniteIrreducibleWindowFactorialSums
import PerronWright.Probability.CompactWindowCountLaw

/-! # Genuine deterministic finite window count limits and law tightness

All actual factorial moments are proved from the fixed-assignment graph
law. The generic proved moment construction supplies a unique true count
limit; it is not an assumed target law. First-mass convergence also gives
tightness of the actual compact-window point-measure laws. This file does
not yet assert uniqueness of their full point-measure law limit.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleWindowCountLaw

open FiniteIrreducibleComponentProcess FiniteIrreducibleWindowFactorialSums
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open ComponentWindowFactorialCounts FinitePointMeasureCompact FinitePointMeasurePolish
open FactorialCountDeterminacy FactorialCountLimitExistence FactorialDensity
open CompactWindowFactorialMoments (integerWindow_eq_indices sum_bounded_surplus windowMass_zero)
open CompactWindowCountLaw (countLaw continuous_countVector factorialPolynomial_countVector singleton_windowMass_series)

variable {S : Type*} [Fintype S] [DecidableEq S]

def actualCountLaw (M : FiniteIrreducibleModel S) (lambda a b : ℝ) (R n : ℕ)
    (x : Fin n → S) : ProbabilityMeasure (Fin 1 → ℕ) :=
  countLaw (unmarkedWindowLaw M lambda a b R n x)

theorem actualCountLaw_factorial_integrable (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) (q : Fin 1 → ℕ) :
    Integrable (factorialPolynomial q) (actualCountLaw M lambda a b R n x : Measure (Fin 1 → ℕ)) := by
  unfold actualCountLaw countLaw
  rw [ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    continuous_countVector.measurable.aemeasurable).mpr
  change Integrable (fun η ↦ factorialPolynomial q (CompactWindowCountLaw.countVector η))
    (unmarkedWindowLaw M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R)))
  simpa only [Function.comp_apply, factorialPolynomial_countVector] using
    windowLaw_descFactorial_integrable M lambda a b R n (q 0) x

theorem actualCountLaw_factorialMoment (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) (q : Fin 1 → ℕ) :
    factorialMoment (actualCountLaw M lambda a b R n x : Measure (Fin 1 → ℕ)) q =
      ∫ η, ((size η).descFactorial (q 0) : ℝ)
        ∂(unmarkedWindowLaw M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))) := by
  unfold factorialMoment actualCountLaw countLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map continuous_countVector.measurable.aemeasurable
    (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  simp only [factorialPolynomial_countVector]

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem windowLaw_factorial_moment_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {q : ℕ} (hq : 0 < q)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ ∫ η, ((size η).descFactorial q : ℝ)
      ∂(unmarkedWindowLaw M lambda a b R n (x n) : Measure (PointMeasure (SurplusWindow a b R))))
      atTop (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R)) := by
  apply (bounded_surplus_integer_window_expectation_tendsto M hM hq R lambda a b ha hab x D hD hround).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  have he := windowLaw_descFactorial_expectation_eq_sum M lambda a b (ha.le.trans hab) R n q hnpos (x n)
  rw [integerWindow_eq_indices hh (ha.le.trans hab), sum_bounded_surplus] at he
  exact he.symm

theorem windowLaw_all_factorial_moments_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R q : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ ∫ η, ((size η).descFactorial q : ℝ)
      ∂(unmarkedWindowLaw M lambda a b R n (x n) : Measure (PointMeasure (SurplusWindow a b R))))
      atTop (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R)) := by
  cases q with
  | zero =>
    simpa only [Nat.descFactorial_zero, Nat.cast_one, integral_const, probReal_univ,
      smul_eq_mul, mul_one, windowMass_zero _ _ _ _ _ hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  | succ q =>
    exact windowLaw_factorial_moment_tendsto M hM lambda a b ha hab R (Nat.succ_pos q) x D hD hround

/-- Actual density-moment realization and full weak convergence of the
literal component number in a positive compact window. -/
theorem exists_unique_actualCountLaw_limit (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    ∃! ν : ProbabilityMeasure (Fin 1 → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (Fin 1 → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (Fin 1 → ℕ)) q =
        windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R) ∧
      Tendsto (fun n ↦ actualCountLaw M lambda a b R n (x n)) atTop (𝓝 ν) := by
  apply exists_unique_limit_of_factorialMoments
    (fun n ↦ actualCountLaw M lambda a b R n (x n))
    (fun n q ↦ actualCountLaw_factorial_integrable M lambda a b R n (x n) q)
    (fun q ↦ windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R)
  · intro q
    simp_rw [actualCountLaw_factorialMoment]
    exact windowLaw_all_factorial_moments_tendsto M hM lambda a b ha hab R (q 0) x D hD hround
  · exact singleton_windowMass_series _ _ (M.beta_pos hM) ha hab R

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem windowLaw_mass_integrable (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    Integrable (fun η ↦ (mass η : ℝ))
      (unmarkedWindowLaw M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R n x (NNReal.continuous_coe.measurable.comp measurable_mass)

theorem windowLaw_mass_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ ∫ η, (mass η : ℝ)
      ∂(unmarkedWindowLaw M lambda a b R n (x n) : Measure (PointMeasure (SurplusWindow a b R))))
      atTop (𝓝 (windowMass 1 (M.alpha hM) (M.beta hM) lambda a b R)) := by
  have he (η : PointMeasure (SurplusWindow a b R)) :
      ((size η).descFactorial 1 : ℝ) = (mass η : ℝ) := by
    rw [Nat.descFactorial_one]
    exact_mod_cast (mass_eq_size η).symm
  simpa only [he] using windowLaw_all_factorial_moments_tendsto M hM lambda a b ha hab R 1 x D hD hround

theorem exists_window_mass_bound (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda a b R n (x n) :
        Measure (PointMeasure (SurplusWindow a b R)))) ≤ B := by
  let F (n : ℕ) := ∫ η, (mass η : ℝ) ∂(unmarkedWindowLaw M lambda a b R n (x n) :
    Measure (PointMeasure (SurplusWindow a b R)))
  let L := windowMass 1 (M.alpha hM) (M.beta hM) lambda a b R
  have ht := windowLaw_mass_tendsto M hM lambda a b ha hab R x D hD hround
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

theorem isTight_unmarkedWindowLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦ (unmarkedWindowLaw M lambda a b R n (x n) :
      Measure (PointMeasure (SurplusWindow a b R))))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound M hM lambda a b ha hab R x D hD hround
  exact isTightMeasureSet_of_mass_moment_bound (fun n ↦ unmarkedWindowLaw M lambda a b R n (x n))
    (fun n ↦ windowLaw_mass_integrable M lambda a b R n (x n)) B hB hb

theorem isCompact_closure_unmarkedWindowLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    IsCompact (closure (Set.range (fun n ↦ unmarkedWindowLaw M lambda a b R n (x n)))) := by
  obtain ⟨B, hB, hb⟩ := exists_window_mass_bound M hM lambda a b ha hab R x D hD hround
  exact isCompact_closure_of_mass_moment_bound (fun n ↦ unmarkedWindowLaw M lambda a b R n (x n))
    (fun n ↦ windowLaw_mass_integrable M lambda a b R n (x n)) B hB hb

end PerronWright.FiniteIrreducibleWindowCountLaw
