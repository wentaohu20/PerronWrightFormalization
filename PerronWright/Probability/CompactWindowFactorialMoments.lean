import PerronWright.Probability.ComponentWindowFactorialCounts
import PerronWright.Probability.CompactAnnealedFactorialWindowMoments

/-! # Literal factorial moments of the genuine compact-window law

The actual graph tuple/cardinality identities and the proved cell-integral
limit give the falling factorial moments of the actual weak-Borel window
point-process law. No target process or source moment interface is assumed.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology

noncomputable section

namespace PerronWright.CompactWindowFactorialMoments

open ComponentWindowFactorialCounts ComponentWindowPointMeasures
  FinitePointMeasureCompact CompactAnnealedFactorialWindowMoments FactorialDensity

theorem fixedSurplusWindowMass_zero (alpha beta lambda a b : ℝ)
    (hab : a ≤ b) (r : Fin 0 → ℕ) :
    fixedSurplusWindowMass alpha beta lambda a b r = 1 := by
  have hd (x : Fin 0 → ℝ) : density alpha beta lambda x r = 1 := by
    simp [density,criticalExponent]
  unfold fixedSurplusWindowMass
  simp_rw [hd]
  rw [setIntegral_const,smul_eq_mul,mul_one,measureReal_def,
    sizeWindow_volume_toReal 0 hab,pow_zero]

theorem windowMass_zero (alpha beta lambda a b : ℝ) (hab : a ≤ b) (R : ℕ) :
    windowMass 0 alpha beta lambda a b R = 1 := by
  unfold windowMass
  simp_rw [fixedSurplusWindowMass_zero alpha beta lambda a b hab]
  simp

theorem integerWindow_eq_indices {q : ℕ} {h a b : ℝ} (hh : 0 < h) (hb : 0 ≤ b) :
    integerWindow h (fun _ : Fin q ↦ a) (fun _ ↦ b) = CriticalFloorWindow.indices q h a b := by
  ext k
  exact (mem_integerWindow hh _ _ (fun _ ↦ hb)).trans (CriticalFloorWindow.mem_indices hh hb).symm

theorem sum_bounded_surplus {q R : ℕ} (F : (Fin q → ℕ) → ℝ) :
    (∑ r ∈ surplusIndices q R, F r) =
      ∑ rr : Fin q → Fin (R+1), F (fun i ↦ (rr i).val) := by
  let e : (Fin q → Fin (R+1)) ↪ (Fin q → ℕ) :=
    ⟨fun rr i ↦ (rr i).val,by
      intro x y h
      funext i
      exact Fin.ext (congrFun h i)⟩
  have hm : surplusIndices q R = Finset.univ.map e := by
    ext r
    simp only [mem_surplusIndices,Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · intro hr
      exact ⟨fun i ↦ ⟨r i,Nat.lt_succ_of_le (hr i)⟩,rfl⟩
    · rintro ⟨rr,he⟩ i
      rw [← he]
      exact Nat.le_of_lt_succ (rr i).isLt
  rw [hm,Finset.sum_map]
  rfl

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Actual positive-order falling factorial moments of the genuine
unmarked compact-window point measure converge to the literal density
mass from the paper. -/
theorem windowLaw_factorial_moment_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n ↦ ∫ η, ((size η).descFactorial q : ℝ)
      ∂(unmarkedWindowLaw M lambda a b R n :
        Measure (PointMeasure (SurplusWindow a b R)))) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R)) := by
  apply (bounded_surplus_integer_window_expectation_tendsto M hM hQP hq R lambda a b ha hab).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hh : 0 < (n : ℝ)^(2/3 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  have he := windowLaw_descFactorial_expectation_eq_sum M lambda a b (ha.le.trans hab) R n q hnpos
  rw [integerWindow_eq_indices hh (ha.le.trans hab),sum_bounded_surplus] at he
  exact he.symm

/-- All orders, including the genuine zeroth probability moment. -/
theorem windowLaw_all_factorial_moments_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R q : ℕ) :
    Tendsto (fun n ↦ ∫ η, ((size η).descFactorial q : ℝ)
      ∂(unmarkedWindowLaw M lambda a b R n :
        Measure (PointMeasure (SurplusWindow a b R)))) atTop
      (𝓝 (windowMass q (M.alpha hM) (M.beta hM) lambda a b R)) := by
  cases q with
  | zero =>
    simpa only [Nat.descFactorial_zero,Nat.cast_one,integral_const,probReal_univ,
      smul_eq_mul,mul_one,windowMass_zero _ _ _ _ _ hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  | succ q =>
    exact windowLaw_factorial_moment_tendsto M hM hQP lambda a b ha hab R (Nat.succ_pos q)

end PerronWright.CompactWindowFactorialMoments
