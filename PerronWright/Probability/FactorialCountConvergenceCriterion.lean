import PerronWright.Probability.FactorialCountConvergence
import PerronWright.Probability.MixedFactorialTailIncrement
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The factorial count convergence criterion without a uniform series bound

Actual moment convergence supplies tightness and next-order mixed tail
bounds. Actual weak subsequential limits inherit integrability by a
discrete Fatou argument, and inherit moments by finite atom truncation.
Only the target law's moment series needs to be summable.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FactorialCountConvergenceCriterion

open FactorialCountDeterminacy FactorialGeneratingSeries MixedFactorialTail
open MixedFactorialTailIncrement FactorialCountConvergence

variable {ι : Type*} [Fintype ι]

theorem exists_bound_of_tendsto {f : ℕ → ℝ} {a : ℝ} (ht : Tendsto f atTop (𝓝 a)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, f j ≤ M := by
  obtain ⟨M₀, hM₀⟩ := ht.bddAbove_range
  exact ⟨max M₀ 0, le_max_right _ _, fun j ↦
    (hM₀ (Set.mem_range_self j)).trans (le_max_left _ _)⟩

/-- On the actual discrete count-vector space weak law convergence
gives convergence of the literal real atom probabilities. -/
theorem atom_tendsto_of_weak_tendsto
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (ht : Tendsto μ atTop (𝓝 ν)) (m : ι → ℕ) :
    Tendsto (fun j ↦ (μ j : Measure (ι → ℕ)).real {m}) atTop
      (𝓝 ((ν : Measure (ι → ℕ)).real {m})) := by
  have hopen : IsOpen ({m} : Set (ι → ℕ)) := isOpen_discrete _
  have hclosed : IsClosed ({m} : Set (ι → ℕ)) := isClosed_discrete _
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht
    (E := {m}) (by rw [IsClopen.frontier_eq ⟨hclosed, hopen⟩]; simp)
  exact (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure (ι → ℕ)) {m})).comp he

/-- All actual mixed moments pass to an actual weak limit. No
uniform moment-generating-series domination is assumed. -/
theorem moments_pass_to_weak_limit
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ρ : ProbabilityMeasure (ι → ℕ))
    (hint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (L : (ι → ℕ) → ℝ)
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop (𝓝 (L q)))
    (hweak : Tendsto μ atTop (𝓝 ρ)) :
    (∀ q, Integrable (factorialPolynomial q) (ρ : Measure (ι → ℕ))) ∧
      ∀ q, factorialMoment (ρ : Measure (ι → ℕ)) q = L q := by
  have hatom := atom_tendsto_of_weak_tendsto μ ρ hweak
  choose M hM hMb using fun q ↦ exists_bound_of_tendsto (hmom q)
  have hlimit (q) : Integrable (factorialPolynomial q) (ρ : Measure (ι → ℕ)) ∧
      factorialMoment (ρ : Measure (ι → ℕ)) q ≤ M q :=
    integrable_limit_of_atom_tendsto_nonneg μ ρ (factorialPolynomial q)
      (factorialPolynomial_nonneg q) (fun j ↦ hint j q) (M q) (hMb q) hatom
  refine ⟨fun q ↦ (hlimit q).1, ?_⟩
  intro q
  have ht : Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ρ : Measure (ι → ℕ)) q)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let d : ℕ := ∑ i, q i
    let A : ℝ := ∑ i, M (increment q i)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ ↦ hM (increment q i))
    obtain ⟨H, hHlarge⟩ := exists_nat_gt ((d : ℝ) + 4 * A / ε + 1)
    have hHd : (d : ℝ) < H := by
      have hfrac : 0 ≤ 4 * A / ε := by positivity
      linarith
    have hdH : d < H := by exact_mod_cast hHd
    have hden : 0 < (H : ℝ) - d := sub_pos.mpr hHd
    have hcut : A / ((H : ℝ) - d) < ε / 4 := by
      apply (div_lt_iff₀ hden).mpr
      have hh := (div_lt_iff₀ hε).mp
        (show 4 * A / ε < (H : ℝ) - d by linarith)
      linarith
    let F : Finset (ι → ℕ) := countTruncation H
    have hfinite : Tendsto (fun j ↦ ∑ n ∈ F,
        (μ j : Measure (ι → ℕ)).real {n} * factorialPolynomial q n) atTop
        (𝓝 (∑ n ∈ F, (ρ : Measure (ι → ℕ)).real {n} * factorialPolynomial q n)) :=
      tendsto_finsetSum F (fun n _ ↦ (hatom n).mul_const (factorialPolynomial q n))
    have hevent : ∀ᶠ j in atTop, |(∑ n ∈ F,
        (μ j : Measure (ι → ℕ)).real {n} * factorialPolynomial q n) -
        ∑ n ∈ F, (ρ : Measure (ι → ℕ)).real {n} * factorialPolynomial q n| < ε / 2 := by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hfinite) (ε / 2) (by positivity)
    filter_upwards [hevent] with j hj
    have hμerr := mixed_finite_truncation_error_le_next_mixed (μ j : Measure (ι → ℕ)) q H
      hdH (hint j q) (fun i ↦ hint j (increment q i))
    have hρerr := mixed_finite_truncation_error_le_next_mixed (ρ : Measure (ι → ℕ)) q H
      hdH (hlimit q).1 (fun i ↦ (hlimit (increment q i)).1)
    have hμbound : (∑ i, factorialMoment (μ j : Measure (ι → ℕ)) (increment q i)) ≤ A :=
      Finset.sum_le_sum (fun i _ ↦ hMb (increment q i) j)
    have hρbound : (∑ i, factorialMoment (ρ : Measure (ι → ℕ)) (increment q i)) ≤ A :=
      Finset.sum_le_sum (fun i _ ↦ (hlimit (increment q i)).2)
    have hμe := hμerr.2.trans (div_le_div_of_nonneg_right hμbound hden.le)
    have hρe := hρerr.2.trans (div_le_div_of_nonneg_right hρbound hden.le)
    rw [Real.dist_eq]
    apply abs_lt.mpr
    have hj' := abs_lt.mp hj
    dsimp only [F] at hj'
    exact ⟨by linarith [hμerr.1, hρerr.1], by linarith [hμerr.1, hρerr.1]⟩
  exact (tendsto_nhds_unique (hmom q) ht).symm

/-- The paper's finite-dimensional factorial count criterion: only
actual mixed factorial-moment convergence, actual moment integrability,
and the target law's absolutely convergent determination series are
required. There is no all-index summable majorant. -/
theorem weak_tendsto_of_factorialMoments_of_target_series
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hνint : ∀ q, Integrable (factorialPolynomial q) (ν : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)))
    (hνseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * factorialMoment (ν : Measure (ι → ℕ)) q /
        ∏ i, ((q i).factorial : ℝ))) :
    Tendsto μ atTop (𝓝 ν) := by
  have htight := isTightMeasureSet_of_factorialMoments_tendsto μ hμint
    (fun q ↦ factorialMoment (ν : Measure (ι → ℕ)) q) hmom
  have hcompact : IsCompact (closure (Set.range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have hrange : {x : Measure (ι → ℕ) | ∃ p ∈ Set.range μ, (p : Measure (ι → ℕ)) = x} =
        Set.range (fun j ↦ (μ j : Measure (ι → ℕ))) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_range, exists_exists_eq_and]
    rw [hrange]
    exact htight
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun j ↦ subset_closure (Set.mem_range_self j)))
  intro ρ _hρ hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hsubmom (q) : Tendsto (fun j ↦ factorialMoment (μ (φ j)) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)) := (hmom q).comp hφ.tendsto_atTop
  obtain ⟨hρint, hρmom⟩ := moments_pass_to_weak_limit (μ ∘ φ) ρ
    (fun j q ↦ hμint (φ j) q) (fun q ↦ factorialMoment (ν : Measure (ι → ℕ)) q) hsubmom hlim
  have he : (ν : Measure (ι → ℕ)) = (ρ : Measure (ι → ℕ)) :=
    measure_eq_of_factorialMoments (ν : Measure (ι → ℕ)) (ρ : Measure (ι → ℕ))
      hνint hρint hνseries (fun q ↦ (hρmom q).symm)
  exact ProbabilityMeasure.toMeasure_injective he.symm

/-- Literal target exponential integrability supplies all its mixed
moment integrability, rather than assuming a determination interface. -/
theorem factorialPolynomial_integrable_of_total_exp
    (ν : Measure (ι → ℕ))
    (hexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) ν) (q : ι → ℕ) :
    Integrable (factorialPolynomial q) ν := by
  have he : factorialPolynomial q =
      fun n ↦ (∏ i, ((q i).factorial : ℝ)) * BinomialInversion.binomialPolynomial q n := by
    funext n
    exact factorialPolynomial_eq q n
  rw [he]
  exact (binomialPolynomial_integrable ν hexp q).const_mul _

/-- The actual target exponential moment supplies its determination
series. This condition is imposed only on the target law. -/
theorem target_series_of_total_exp
    (ν : Measure (ι → ℕ))
    (hexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) ν) :
    Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * factorialMoment ν q /
        ∏ i, ((q i).factorial : ℝ)) := by
  simpa only [binomialMoment_eq_div, mul_div_assoc] using
    (mixed_series_hasSum ν hexp).summable

/-- Weak convergence of actual count laws under convergence of their
mixed factorial moments and a single target total-count exponential
moment. No uniform source exponential bound is needed. -/
theorem weak_tendsto_of_factorialMoments_of_target_total_exp
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)))
    (hνexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) (ν : Measure (ι → ℕ))) :
    Tendsto μ atTop (𝓝 ν) :=
  weak_tendsto_of_factorialMoments_of_target_series μ ν hμint
    (factorialPolynomial_integrable_of_total_exp (ν : Measure (ι → ℕ)) hνexp)
    hmom (target_series_of_total_exp (ν : Measure (ι → ℕ)) hνexp)

/-- The target total factorial generating series is enough for the
paper's count-law criterion. Actual source moments converge individually;
they need no all-index summable majorant. -/
theorem weak_tendsto_of_factorialMoments_of_target_total_series
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)))
    (hνint : ∀ q : ℕ, Integrable (fun n ↦ ((totalCount n).choose q : ℝ))
      (ν : Measure (ι → ℕ)))
    (hνseries : Summable (fun q : ℕ ↦
      (2 : ℝ) ^ q * ∫ n, ((totalCount n).choose q : ℝ) ∂(ν : Measure (ι → ℕ)))) :
    Tendsto μ atTop (𝓝 ν) :=
  weak_tendsto_of_factorialMoments_of_target_total_exp μ ν hμint hmom
    (total_exp_integrable_of_moment_series (ν : Measure (ι → ℕ)) hνint hνseries)

end PerronWright.FactorialCountConvergenceCriterion
