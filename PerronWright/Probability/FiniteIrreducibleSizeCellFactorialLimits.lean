import PerronWright.Probability.FiniteIrreducibleWeightedFactorialWindow
import PerronWright.Probability.FiniteIrreducibleCellFactorialCounts
import PerronWright.Probability.CompactSizeCellFactorialLimits

/-! # Genuine deterministic mixed factorial density integrals

Only the pure labelled cell grids, indicators, and literal density
integrals are reused from the compact chain. No regular-critical model
or annealed graph law is used.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleSizeCellFactorialLimits

open SizeCellIndicators CriticalWeightedFloorIntegral CriticalFloorWindow
  CompactWindowFactorialMoments ComponentWindowMixedFactorials
  FinitePointMeasureMixedFactorials FactorialDensity FactorialCountDeterminacy
open CompactSizeCellFactorialLimits (cellMomentMass cellMomentMass_zero)
open FiniteIrreducibleWeightedFactorialWindow FiniteIrreducibleCellFactorialCounts
  FiniteIrreducibleComponentProcess

variable {D : Type*} [Fintype D]
variable {T : Type*} [Fintype T] [DecidableEq T] [MetricSpace T]
  [DiscreteTopology T] [MeasurableSpace T] [BorelSpace T]

theorem filtered_integer_window_expectation_tendsto (M : FiniteIrreducibleModel T)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (J : D → Set ℝ) (q : D → ℕ)
    (hq : 0 < ∑ i, q i) (r : Fin (∑ i, q i) → ℕ)
    (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (v : (n : ℕ) → Fin n → T) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ cellSizeIndices n a b J q,
      ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n (v n)) atTop
      (𝓝 (∫ x in sizeWindow (∑ i, q i) a b,
        cellWeight (fun j ↦ J (label q j)) x * density (M.alpha hM) (M.beta hM) lambda x r)) := by
  have ht := weighted_integer_window_expectation_tendsto M hM hq r lambda a b ha hab v E hE hround
    (cellWeight (fun j ↦ J (label q j))) 1 (by norm_num)
    (cellWeight_norm_le _) (ae_continuousAt_cellWeight _ (fun j ↦ hJf (label q j)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (by omega : 0 < n)) _
  unfold cellSizeIndices
  rw [integerWindow_eq_indices hh (ha.le.trans hab),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [cellWeight_eq]
  by_cases hk : ∀ j, (normalizedInteger n k) j ∈ J (label q j)
  · have hk' : ∀ j, (k j : ℝ)/(n : ℝ)^(2/3 : ℝ) ∈ J (label q j) := hk
    simp only [if_pos hk,if_pos hk',one_mul]
  · have hk' : ¬∀ j, (k j : ℝ)/(n : ℝ)^(2/3 : ℝ) ∈ J (label q j) := hk
    simp only [if_neg hk,if_neg hk',zero_mul]

/-- Actual source cell-count laws converge in each positive mixed
factorial order to the literal density integral, with genuine disjoint
cell conditions and Lebesgue-null cell boundaries only. -/
theorem sizeSurplusCountLaw_mixed_factorial_tendsto (M : FiniteIrreducibleModel T)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (q : D → ℕ) (hq : 0 < ∑ i, q i)
    (v : (n : ℕ) → Fin n → T) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ factorialMoment
      (sizeSurplusCountLaw M lambda a b R n (v n) J S hJ : Measure (D → ℕ)) q) atTop
      (𝓝 (cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q)) := by
  have ht : Tendsto (fun n : ℕ ↦ ∑ r ∈ cellSurplusIndices R S q,
      ∑ k ∈ cellSizeIndices n a b J q,
        ∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n (v n)) atTop
      (𝓝 (cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q)) :=
    tendsto_finsetSum _ (fun r _ ↦ filtered_integer_window_expectation_tendsto M hM
      lambda a b ha hab J q hq r hJf v E hE hround)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (sizeSurplusCountLaw_mixed_factorial_integral_eq_sum M lambda a b (ha.le.trans hab)
    R n (v n) (by omega) J S hJ q hdis).symm

theorem sizeSurplusCountLaw_all_mixed_factorials_tendsto (M : FiniteIrreducibleModel T)
    (hM : M.IsCritical) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (hJf : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0)
    (hdis : Pairwise (fun i j ↦ Disjoint (sizeSurplusCells J S i) (sizeSurplusCells J S j)))
    (q : D → ℕ)
    (v : (n : ℕ) → Fin n → T) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ factorialMoment
      (sizeSurplusCountLaw M lambda a b R n (v n) J S hJ : Measure (D → ℕ)) q) atTop
      (𝓝 (cellMomentMass (M.alpha hM) (M.beta hM) lambda a b R J S q)) := by
  by_cases hq : 0 < ∑ i, q i
  · exact sizeSurplusCountLaw_mixed_factorial_tendsto M hM lambda a b ha hab R
      J S hJ hJf hdis q hq v E hE hround
  · have hzero : q = fun _ ↦ 0 := by
      funext i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ Nat.zero_le (q j))
        (Finset.mem_univ i)
      omega
    subst q
    simpa only [factorialMoment,factorialPolynomial,Nat.descFactorial_zero,Nat.cast_one,
      Finset.prod_const_one,integral_const,probReal_univ,smul_eq_mul,mul_one,
      cellMomentMass_zero _ _ _ _ _ hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))

end PerronWright.FiniteIrreducibleSizeCellFactorialLimits

