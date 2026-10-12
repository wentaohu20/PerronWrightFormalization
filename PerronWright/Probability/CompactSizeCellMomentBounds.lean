import PerronWright.Probability.CompactSizeCellFactorialLimits
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge

/-! # Summable numerical moments for actual disjoint size-surplus cells

The literal cell integrals are bounded by the already proved full-window
density masses. Their multivariate factorial series is then dominated by
a finite product of exponential series, with no moment-realization premise.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactSizeCellMomentBounds

open SizeCellIndicators CompactSizeCellFactorialLimits FactorialDensity
  ComponentWindowMixedFactorials CompactWindowFactorialMoments
  FinitePointMeasureMixedFactorials CompactAnnealedFactorialWindowMoments
  ComponentWindowFactorialCounts

variable {D : Type*} [Fintype D]

theorem weighted_density_integrableOn (alpha beta lambda : ℝ) {a b : ℝ}
    (ha : 0 < a) {N : ℕ} (J : Fin N → Set ℝ) (hJ : ∀ i, MeasurableSet (J i))
    (r : Fin N → ℕ) :
    IntegrableOn (fun x ↦ cellWeight J x * density alpha beta lambda x r)
      (sizeWindow N a b) volume := by
  have hi := density_integrableOn_sizeWindow alpha beta lambda r (b := b) ha
  apply hi.norm.mono'
  · exact (measurable_cellWeight J hJ).aestronglyMeasurable.mul hi.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (cellWeight_norm_le J x) (norm_nonneg _)).trans_eq
      (one_mul _)

theorem cellMomentMass_nonneg (alpha lambda a b : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (q : D → ℕ) :
    0 ≤ cellMomentMass alpha beta lambda a b R J S q := by
  apply Finset.sum_nonneg
  intro r _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (s := sizeWindow (∑ i, q i) a b) measurableSet_Icc]
    with x hx
  exact mul_nonneg (cellWeight_nonneg _ _) (density_pos alpha lambda hbeta x r
    (fun i ↦ lt_of_lt_of_le ha ((mem_sizeWindow.mp hx) i).1)).le

theorem cellMomentMass_le_windowMass (alpha lambda a b : ℝ) {beta : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) (q : D → ℕ) :
    cellMomentMass alpha beta lambda a b R J S q ≤
      windowMass (∑ i, q i) alpha beta lambda a b R := by
  have hi (r : Fin (∑ i, q i) → ℕ) :
      (∫ x in sizeWindow (∑ i, q i) a b,
        cellWeight (fun j ↦ J (label q j)) x * density alpha beta lambda x r) ≤
      fixedSurplusWindowMass alpha beta lambda a b r := by
    apply integral_mono_ae
      (weighted_density_integrableOn alpha beta lambda ha _ (fun j ↦ hJ (label q j)) r)
      (density_integrableOn_sizeWindow alpha beta lambda r ha)
    filter_upwards [ae_restrict_mem (s := sizeWindow (∑ i, q i) a b) measurableSet_Icc]
      with x hx
    have hd := (density_pos alpha lambda hbeta x r
      (fun i ↦ lt_of_lt_of_le ha ((mem_sizeWindow.mp hx) i).1)).le
    have hc : cellWeight (fun j ↦ J (label q j)) x ≤ 1 :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using cellWeight_norm_le _ _)
    exact (mul_le_mul_of_nonneg_right hc hd).trans_eq (one_mul _)
  calc
    cellMomentMass alpha beta lambda a b R J S q ≤
        ∑ r ∈ cellSurplusIndices R S q, fixedSurplusWindowMass alpha beta lambda a b r :=
      Finset.sum_le_sum (fun r _ ↦ hi r)
    _ ≤ ∑ r ∈ surplusIndices (∑ i, q i) R,
        fixedSurplusWindowMass alpha beta lambda a b r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact mem_surplusIndices.mpr (fun j ↦ (mem_cellSurplusIndices R S q r |>.mp hr j).1)
      · intro r _ _
        exact fixedSurplusWindowMass_nonneg alpha lambda a b hbeta ha r
    _ = windowMass (∑ i, q i) alpha beta lambda a b R := sum_bounded_surplus _

theorem summable_finite_exponential_product (z : ℝ) :
    Summable (fun q : D → ℕ ↦ ∏ i, z^(q i) / ((q i).factorial : ℝ)) := by
  let e := Fintype.equivFin D
  let a := Equiv.arrowCongr e (Equiv.refl ℕ)
  have hs := (GraphCore.summable_finFunction_prod_and_tsum
    (fun _ : Fin (Fintype.card D) ↦ fun m : ℕ ↦ z^m/(m.factorial : ℝ))
    (fun _ ↦ Real.summable_pow_div_factorial z)).1
  have ht := a.summable_iff.mpr hs
  apply ht.congr
  intro q
  exact e.symm.prod_comp (fun i : D ↦ z^(q i)/((q i).factorial : ℝ))

theorem summable_cellMomentMass_factorial (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i)) :
    Summable (fun q : D → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      cellMomentMass alpha beta lambda a b R J S q / ∏ i, ((q i).factorial : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := exists_windowMass_bound hbeta ha hab R
  apply (summable_finite_exponential_product (D := D) (2*C)).of_norm_bounded
  intro q
  have hm0 := cellMomentMass_nonneg alpha lambda a b hbeta ha R J S q
  have hm := (cellMomentMass_le_windowMass alpha lambda a b hbeta ha R J S hJ q).trans
    (hbound (∑ i, q i) alpha lambda).2
  have he : Real.exp (-beta*(a*(∑ i, q i))^3/24) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ beta*(a*(∑ i, q i))^3/24 := by positivity
    linarith
  have hm' : cellMomentMass alpha beta lambda a b R J S q ≤ C^(∑ i, q i) :=
    hm.trans ((mul_le_mul_of_nonneg_left he (pow_nonneg hC _)).trans_eq (mul_one _))
  rw [norm_div,norm_mul,Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
    Real.norm_of_nonneg hm0,Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ∏ i, ((q i).factorial : ℝ))]
  calc
    (2 : ℝ)^(∑ i, q i) * cellMomentMass alpha beta lambda a b R J S q /
        ∏ i, ((q i).factorial : ℝ) ≤
        (2*C)^(∑ i, q i) / ∏ i, ((q i).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hm'
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    _ = ∏ i, (2*C)^(q i) / ((q i).factorial : ℝ) := by
      rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]

end PerronWright.CompactSizeCellMomentBounds
