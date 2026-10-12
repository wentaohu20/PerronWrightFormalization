import PerronWright.Probability.MixedFactorialTail
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Convergence of actual finite-dimensional count laws

Actual mixed moment convergence and a summable uniform bound on the
normalized moments imply atom-probability convergence by the proved
joint inversion formula and Tannery's theorem. Finite-state truncation
then upgrades atom convergence to genuine weak law convergence.

The summable uniform moment bound below is an explicit mathematical
condition on the actual laws, not a point-probability, tightness, or
uniform-integrability interface. The weaker criterion using only
pointwise moment convergence and limit-law determinacy still requires
a separate subsequence/limit-moment argument.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped Classical BigOperators Topology

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.FactorialCountConvergence

open BinomialInversion FactorialCountDeterminacy FactorialGeneratingSeries MixedFactorialTail

variable {ι : Type*} [Fintype ι]

theorem binomialPolynomial_integrable_of_factorial (μ : Measure (ι → ℕ))
    (q : ι → ℕ) (hint : Integrable (factorialPolynomial q) μ) :
    Integrable (binomialPolynomial q) μ := by
  have hpos : 0 < ∏ i, ((q i).factorial : ℝ) :=
    Finset.prod_pos (fun i _ ↦ by exact_mod_cast Nat.factorial_pos (q i))
  have heq : binomialPolynomial q =
      (fun n ↦ factorialPolynomial q n / ∏ i, ((q i).factorial : ℝ)) := by
    funext n
    rw [factorialPolynomial_eq]
    field_simp [hpos.ne']
  rw [heq]
  exact hint.div_const _

/-- Joint atom probabilities converge under actual mixed binomial
moment convergence with a summable uniform normalized-moment bound. -/
theorem atom_probability_tendsto_of_binomialMoments_of_summable_bound
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (binomialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hνint : ∀ q, Integrable (binomialPolynomial q) (ν : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ binomialMoment (μ j) q) atTop
      (𝓝 (binomialMoment (ν : Measure (ι → ℕ)) q)))
    (B : (ι → ℕ) → ℝ) (_hB : ∀ q, 0 ≤ B q)
    (hbound : ∀ j q, binomialMoment (μ j) q ≤ B q)
    (hsum : Summable (fun q : ι → ℕ ↦ (2 : ℝ) ^ (∑ i, q i) * B q))
    (m : ι → ℕ) :
    Tendsto (fun j ↦ (μ j : Measure (ι → ℕ)).real {m}) atTop
      (𝓝 ((ν : Measure (ι → ℕ)).real {m})) := by
  have hνbound (q) : binomialMoment (ν : Measure (ι → ℕ)) q ≤ B q :=
    le_of_tendsto (hmom q) (Eventually.of_forall (fun j ↦ hbound j q))
  have hsμ (j) : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * binomialMoment (μ j) q) := by
    apply hsum.of_norm_bounded
    intro q
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (binomialMoment_nonneg (μ j) q))]
    exact mul_le_mul_of_nonneg_left (hbound j q) (by positivity)
  have hsν : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * binomialMoment ν q) := by
    apply hsum.of_norm_bounded
    intro q
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (binomialMoment_nonneg (ν : Measure (ι → ℕ)) q))]
    exact mul_le_mul_of_nonneg_left (hνbound q) (by positivity)
  have ht : Tendsto (fun j ↦ ∑' q : ι → ℕ, jointCoefficient m q * binomialMoment (μ j) q)
      atTop (𝓝 (∑' q : ι → ℕ, jointCoefficient m q * binomialMoment ν q)) := by
    apply tendsto_tsum_of_dominated_convergence hsum
      (fun q ↦ (hmom q).const_mul (jointCoefficient m q))
    exact Eventually.of_forall (fun j q ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (binomialMoment_nonneg (μ j) q)]
      exact mul_le_mul (jointCoefficient_abs_le m q) (hbound j q)
        (binomialMoment_nonneg (μ j) q) (by positivity))
  have heq : (fun j ↦ (μ j : Measure (ι → ℕ)).real {m}) =
      (fun j ↦ ∑' q : ι → ℕ, jointCoefficient m q * binomialMoment (μ j) q) := by
    funext j
    exact atom_eq_moment_series (μ j) (hμint j) (hsμ j) m
  rw [heq, atom_eq_moment_series ν hνint hsν m]
  exact ht

/-- The same genuine atom-probability convergence stated in the
literal mixed falling-factorial moments. -/
theorem atom_probability_tendsto_of_factorialMoments_of_summable_bound
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hνint : ∀ q, Integrable (factorialPolynomial q) (ν : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)))
    (B : (ι → ℕ) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hbound : ∀ j q, factorialMoment (μ j) q / ∏ i, ((q i).factorial : ℝ) ≤ B q)
    (hsum : Summable (fun q : ι → ℕ ↦ (2 : ℝ) ^ (∑ i, q i) * B q))
    (m : ι → ℕ) :
    Tendsto (fun j ↦ (μ j : Measure (ι → ℕ)).real {m}) atTop
      (𝓝 ((ν : Measure (ι → ℕ)).real {m})) := by
  apply atom_probability_tendsto_of_binomialMoments_of_summable_bound μ ν
    (fun j q ↦ binomialPolynomial_integrable_of_factorial (μ j) q (hμint j q))
    (fun q ↦ binomialPolynomial_integrable_of_factorial ν q (hνint q)) _ B hB _ hsum m
  · intro q
    simp only [binomialMoment_eq_div]
    exact (hmom q).div_const _
  · simpa only [binomialMoment_eq_div] using hbound

/-- The order-one factorial polynomial for a single coordinate. -/
def coordinateOrder (i : ι) : ι → ℕ := by
  classical
  exact Pi.single i 1

theorem factorialPolynomial_coordinateOrder (i : ι) (n : ι → ℕ) :
    factorialPolynomial (coordinateOrder i) n = (n i : ℝ) := by
  classical
  unfold factorialPolynomial
  rw [Finset.prod_eq_single i]
  · simp [coordinateOrder]
  · intro j _ hji
    simp [coordinateOrder, Pi.single_eq_of_ne hji]
  · simp

theorem totalCount_integrable_of_factorial (μ : Measure (ι → ℕ))
    (hint : ∀ q, Integrable (factorialPolynomial q) μ) :
    Integrable (fun n ↦ (totalCount n : ℝ)) μ := by
  have heq : (fun n : ι → ℕ ↦ (totalCount n : ℝ)) =
      fun n ↦ ∑ i, factorialPolynomial (coordinateOrder i) n := by
    funext n
    simp only [factorialPolynomial_coordinateOrder, totalCount, Nat.cast_sum]
  rw [heq]
  exact integrable_finsetSum _ (fun i _ ↦ hint (coordinateOrder i))

theorem totalFirstMoment_eq_sum (μ : Measure (ι → ℕ))
    (hint : ∀ q, Integrable (factorialPolynomial q) μ) :
    (∫ n, (totalCount n : ℝ) ∂μ) = ∑ i, factorialMoment μ (coordinateOrder i) := by
  have heq : (fun n : ι → ℕ ↦ (totalCount n : ℝ)) =
      fun n ↦ ∑ i, factorialPolynomial (coordinateOrder i) n := by
    funext n
    simp only [factorialPolynomial_coordinateOrder, totalCount, Nat.cast_sum]
  rw [heq, integral_finsetSum Finset.univ (fun i _ ↦ hint (coordinateOrder i))]
  rfl

/-- Actual uniform first-total-moment bounds imply tightness of the
count laws, with finite compact count cutoffs explicitly supplied. -/
theorem isTightMeasureSet_of_first_moment_bound {J : Type*}
    (μ : J → ProbabilityMeasure (ι → ℕ))
    (hint : ∀ j, Integrable (fun n ↦ (totalCount n : ℝ)) (μ j : Measure (ι → ℕ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ n, (totalCount n : ℝ) ∂(μ j : Measure (ι → ℕ))) ≤ M) :
    IsTightMeasureSet (Set.range (fun j ↦ (μ j : Measure (ι → ℕ)))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ by simp [hεtop]⟩
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨H, hHlarge⟩ := exists_nat_gt (M / ε.toReal + 1)
  have hHreal : (0 : ℝ) < H := by
    have hfrac : 0 ≤ M / ε.toReal := div_nonneg hM hεreal.le
    linarith
  have hH : 0 < H := by exact_mod_cast hHreal
  have hcut : M / (H : ℝ) < ε.toReal := by
    apply (div_lt_iff₀ hHreal).mpr
    have hm := (div_lt_iff₀ hεreal).mp (show M / ε.toReal < (H : ℝ) by linarith)
    nlinarith
  refine ⟨(countTruncation (ι := ι) H : Set (ι → ℕ)), (countTruncation H).finite_toSet.isCompact, ?_⟩
  intro ζ hζ
  obtain ⟨j, rfl⟩ := hζ
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) hεtop).mp
  have hb := probability_countTruncation_compl_le (μ j : Measure (ι → ℕ)) H hH (hint j)
  exact hb.trans ((div_le_div_of_nonneg_right (hbound j) hHreal.le).trans hcut.le)

/-- Pointwise convergence of actual mixed factorial moments already
implies tightness, without any summable bound on the moment series. -/
theorem isTightMeasureSet_of_factorialMoments_tendsto
    (μ : ℕ → ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (L : (ι → ℕ) → ℝ)
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop (𝓝 (L q))) :
    IsTightMeasureSet (Set.range (fun j ↦ (μ j : Measure (ι → ℕ)))) := by
  have hfirst : Tendsto (fun j ↦ ∫ n, (totalCount n : ℝ) ∂(μ j : Measure (ι → ℕ)))
      atTop (𝓝 (∑ i, L (coordinateOrder i))) := by
    simp_rw [totalFirstMoment_eq_sum _ (hμint _)]
    exact tendsto_finsetSum _ (fun i _ ↦ hmom (coordinateOrder i))
  obtain ⟨M₀, hM₀⟩ := hfirst.bddAbove_range
  apply isTightMeasureSet_of_first_moment_bound μ
    (fun j ↦ totalCount_integrable_of_factorial (μ j : Measure (ι → ℕ)) (hμint j))
    (max M₀ 0) (le_max_right _ _)
  intro j
  exact (hM₀ (Set.mem_range_self j)).trans (le_max_left _ _)

/-- Actual atom convergence plus an actual uniform first-total-moment
bound implies genuine weak convergence of probability laws. Finite
count truncations provide the necessary tightness and test errors. -/
theorem weak_tendsto_of_atoms_of_first_moment_bound
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j, Integrable (fun n ↦ (totalCount n : ℝ)) (μ j : Measure (ι → ℕ)))
    (hνint : Integrable (fun n ↦ (totalCount n : ℝ)) (ν : Measure (ι → ℕ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ n, (totalCount n : ℝ) ∂(μ j : Measure (ι → ℕ))) ≤ M)
    (hatom : ∀ m : ι → ℕ, Tendsto (fun j ↦ (μ j : Measure (ι → ℕ)).real {m}) atTop
      (𝓝 ((ν : Measure (ι → ℕ)).real {m}))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : ℝ := ‖f‖
  have hB : 0 ≤ B := norm_nonneg _
  let V : ℝ := ∫ n, (totalCount n : ℝ) ∂(ν : Measure (ι → ℕ))
  have hV : 0 ≤ V := integral_nonneg (fun _ ↦ Nat.cast_nonneg _)
  obtain ⟨H, hHlarge⟩ := exists_nat_gt (2 * B * (M + V) / ε + 1)
  have hHreal : (0 : ℝ) < H := by
    have hx : 0 ≤ 2 * B * (M + V) / ε := by positivity
    linarith
  have hH : 0 < H := by exact_mod_cast hHreal
  have hcut : B * (M / (H : ℝ)) + B * (V / (H : ℝ)) < ε / 2 := by
    have hn : 2 * B * (M + V) / ε < (H : ℝ) := by linarith
    have hn' := (div_lt_iff₀ hε).mp hn
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hcancel : (B * (M / (H : ℝ)) + B * (V / (H : ℝ))) * 2 =
        (2 * B * (M + V)) / (H : ℝ) := by ring
    rw [hcancel]
    exact (div_lt_iff₀ hHreal).mpr (by nlinarith)
  let F : Finset (ι → ℕ) := countTruncation H
  have hfinite : Tendsto (fun j ↦ ∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n)
      atTop (𝓝 (∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n)) :=
    tendsto_finsetSum F (fun n _ ↦ (hatom n).mul_const (f n))
  have hevent : ∀ᶠ j in atTop,
      |(∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n) -
        ∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n| < ε / 2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hfinite) (ε / 2) (by positivity)
  filter_upwards [hevent] with j hj
  have hμerr := bounded_test_finite_truncation_error (μ j) f B hB
    (fun n ↦ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm n) H hH (hμint j)
  have hνerr := bounded_test_finite_truncation_error ν f B hB
    (fun n ↦ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm n) H hH hνint
  have hμerr' : |(∫ n, f n ∂(μ j : Measure (ι → ℕ))) -
      ∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n| ≤ B * (M / (H : ℝ)) :=
    hμerr.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hbound j) hHreal.le) hB)
  have htriangle : |(∫ n, f n ∂(μ j : Measure (ι → ℕ))) - ∫ n, f n ∂(ν : Measure (ι → ℕ))| ≤
      |(∫ n, f n ∂(μ j : Measure (ι → ℕ))) -
        ∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n| +
      |(∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n) -
        ∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n| +
      |(∫ n, f n ∂(ν : Measure (ι → ℕ))) -
        ∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n| := by
    calc
      _ ≤ |(∫ n, f n ∂(μ j : Measure (ι → ℕ))) -
          ∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n| +
          |(∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n) -
            ∫ n, f n ∂(ν : Measure (ι → ℕ))| := abs_sub_le _ _ _
      _ ≤ _ := by
        have ht := abs_sub_le (∑ n ∈ F, (μ j : Measure (ι → ℕ)).real {n} * f n)
          (∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n)
          (∫ n, f n ∂(ν : Measure (ι → ℕ)))
        rw [abs_sub_comm (∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n)] at ht
        linarith
  rw [Real.dist_eq]
  change |(∫ n, f n ∂(μ j : Measure (ι → ℕ))) - ∫ n, f n ∂(ν : Measure (ι → ℕ))| < ε
  dsimp only [V] at hcut
  dsimp only [F] at hμerr' hj htriangle
  linarith

/-- Genuine weak convergence of finite-dimensional count laws under
literal factorial-moment convergence and a summable uniform bound
on their normalized factorial moments. -/
theorem weak_tendsto_of_factorialMoments_of_summable_bound
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (hμint : ∀ j q, Integrable (factorialPolynomial q) (μ j : Measure (ι → ℕ)))
    (hνint : ∀ q, Integrable (factorialPolynomial q) (ν : Measure (ι → ℕ)))
    (hmom : ∀ q, Tendsto (fun j ↦ factorialMoment (μ j) q) atTop
      (𝓝 (factorialMoment (ν : Measure (ι → ℕ)) q)))
    (B : (ι → ℕ) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hbound : ∀ j q, factorialMoment (μ j) q / ∏ i, ((q i).factorial : ℝ) ≤ B q)
    (hsum : Summable (fun q : ι → ℕ ↦ (2 : ℝ) ^ (∑ i, q i) * B q)) :
    Tendsto μ atTop (𝓝 ν) := by
  have hfirst : Tendsto (fun j ↦ ∫ n, (totalCount n : ℝ) ∂(μ j : Measure (ι → ℕ)))
      atTop (𝓝 (∫ n, (totalCount n : ℝ) ∂(ν : Measure (ι → ℕ)))) := by
    simp_rw [totalFirstMoment_eq_sum _ (hμint _)]
    rw [totalFirstMoment_eq_sum _ hνint]
    exact tendsto_finsetSum _ (fun i _ ↦ hmom (coordinateOrder i))
  obtain ⟨M₀, hM₀⟩ := hfirst.bddAbove_range
  have hmean (j) : (∫ n, (totalCount n : ℝ) ∂(μ j : Measure (ι → ℕ))) ≤ max M₀ 0 :=
    (hM₀ (Set.mem_range_self j)).trans (le_max_left _ _)
  exact weak_tendsto_of_atoms_of_first_moment_bound μ ν
    (fun j ↦ totalCount_integrable_of_factorial (μ j : Measure (ι → ℕ)) (hμint j))
    (totalCount_integrable_of_factorial (ν : Measure (ι → ℕ)) hνint)
    (max M₀ 0) (le_max_right _ _) hmean
    (atom_probability_tendsto_of_factorialMoments_of_summable_bound μ ν hμint hνint hmom B hB hbound hsum)

end PerronWright.FactorialCountConvergence
