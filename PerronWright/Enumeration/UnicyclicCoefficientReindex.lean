import PerronWright.Enumeration.UnicyclicFullAnalytic

/-!
# Reindexing the unicyclic composition coefficient by cycle length

The antidiagonal core/off-core definition is converted to the finite
cycle-length sum used by the analytic truncations.
-/

open scoped Classical
noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem unicyclicProfileCompositionCoeff_eq_sum_range
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ)) (k : ℕ) :
    unicyclicProfileCompositionCoeff M T k =
      ∑ q ∈ Finset.range (k + 1),
        (∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q 0 H},
          PowerSeries.coeff k
            (fixedCoreProfileCompositionSeries M T H.1)) /
          (q.factorial : ℂ) := by
  unfold unicyclicProfileCompositionCoeff
  let f : ℕ × ℕ → ℂ := fun p =>
    (∑ H : {H : SimpleGraph (Fin p.1) //
        IsAdmissibleAttachmentCore p.1 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) /
      (p.1.factorial : ℂ)
  change (∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k}, f p.1) = _
  rw [Finset.sum_coe_sort]
  change (∑ p ∈ coreOffSizePairs k, f p) = _
  rw [coreOffSizePairs, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem unicyclicProfileCompositionCoeff_eq_shifted_sum
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ)) (k : ℕ) :
    unicyclicProfileCompositionCoeff M T k =
      ∑ n ∈ Finset.range (k + 1),
        (∑ H : {H : SimpleGraph (Fin (n + 3)) //
            IsAdmissibleAttachmentCore (n + 3) 0 H},
          PowerSeries.coeff k
            (fixedCoreProfileCompositionSeries M T H.1)) /
          ((n + 3).factorial : ℂ) := by
  let F : ℕ → ℂ := fun q =>
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) /
      (q.factorial : ℂ)
  have hsmall : ∀ q < 3, F q = 0 := by
    intro q hq
    dsimp only [F]
    rw [show (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) = 0 by
      apply Fintype.sum_eq_zero
      intro H
      exact False.elim (by
        have hthree := three_le_of_isAdmissibleAttachmentCore_zero H.2
        omega)]
    simp
  have hlarge : ∀ q, k < q → F q = 0 := by
    intro q hq
    dsimp only [F]
    rw [show (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) = 0 by
      apply Fintype.sum_eq_zero
      intro H
      exact fixedCoreProfileCompositionSeries_coeff_eq_zero_of_lt
        M T H.1 hq]
    simp
  rw [unicyclicProfileCompositionCoeff_eq_sum_range]
  change (∑ q ∈ Finset.range (k + 1), F q) =
    ∑ n ∈ Finset.range (k + 1), F (n + 3)
  calc
    (∑ q ∈ Finset.range (k + 1), F q) =
        ∑ q ∈ Finset.range (k + 4), F q := by
      apply Finset.sum_subset_zero_on_sdiff
      · exact Finset.range_mono (by omega)
      · intro q hq
        have hnot := (Finset.mem_sdiff.mp hq).2
        have : k < q := by
          have := Nat.le_of_not_gt
            (fun h => hnot (Finset.mem_range.mpr (by omega)))
          omega
        exact hlarge q this
      · intro q hq
        rfl
    _ = ∑ n ∈ Finset.range (k + 1), F (n + 3) := by
      have hsplit := Finset.sum_range_add F 3 (k + 1)
      have hzero : ∑ q ∈ Finset.range 3, F q = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        exact hsmall q (Finset.mem_range.mp hq)
      rw [hzero, zero_add] at hsplit
      simpa only [Nat.reduceAdd, Nat.add_comm] using hsplit

theorem coeff_finite_cycle_sum_eq_unicyclicProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ)) (k : ℕ) :
    PowerSeries.coeff k
        (∑ n ∈ Finset.range (k + 1),
          (((n + 3).factorial : ℂ)⁻¹) •
            ∑ H : {H : SimpleGraph (Fin (n + 3)) //
                IsAdmissibleAttachmentCore (n + 3) 0 H},
              fixedCoreProfileCompositionSeries M T H.1) =
      unicyclicProfileCompositionCoeff M T k := by
  rw [unicyclicProfileCompositionCoeff_eq_shifted_sum]
  simp only [map_sum, PowerSeries.coeff_smul, Finset.smul_sum,
    smul_eq_mul, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.mul_sum]
  ring

end PerronWright.GraphCore
