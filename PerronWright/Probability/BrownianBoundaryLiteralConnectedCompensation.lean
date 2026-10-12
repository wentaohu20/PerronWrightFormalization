import PerronWright.Probability.BrownianBoundarySeriesInitialSlope
import PerronWright.Enumeration.CubicConnectedComponentRecurrence

/-! # Actual boundary slopes equal literal connected cubic compensation

The Brownian coefficients and the unchanged labelled connected-kernel
sum satisfy the same proved recurrence. Strong induction identifies
them, with the order-zero exception handled explicitly.
-/

open Polynomial
open scoped Polynomial PowerSeries Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundaryLiteralConnectedCompensation

open BrownianBoundaryWrightCoefficients BrownianBoundarySeriesInitialSlope
open BrownianKilledBoundaryPolynomial GraphCore

def compensationCandidate (n : ℕ) : ℝ :=
  if n = 0 then 1/2 else 3*(n : ℝ)*connectedCubicCompensation n

private theorem candidate_convolution (n : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ Finset.antidiagonal n, compensationCandidate a.1*compensationCandidate a.2) =
      9*∑ a ∈ Finset.antidiagonal n,
        ((a.1 : ℝ)*connectedCubicCompensation a.1)*
          ((a.2 : ℝ)*connectedCubicCompensation a.2)+
      3*(n : ℝ)*connectedCubicCompensation n := by
  have hrange : Finset.range (n+1) = insert 0 (insert n (Finset.Ioo 0 n)) := by
    ext k
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Ioo]
    omega
  have h0mem : 0 ∉ insert n (Finset.Ioo 0 n) := by
    simp only [Finset.mem_insert,Finset.mem_Ioo]
    omega
  have hnmem : n ∉ Finset.Ioo 0 n := by simp
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,hrange,
    Finset.sum_insert h0mem,Finset.sum_insert hnmem,
    Finset.sum_insert h0mem,Finset.sum_insert hnmem]
  simp only [Nat.sub_zero,Nat.sub_self,Nat.cast_zero,zero_mul,mul_zero,
    compensationCandidate,if_true,if_neg hn]
  have hinner : (∑ k ∈ Finset.Ioo 0 n,
      (if k = 0 then 1/2 else 3*(k : ℝ)*connectedCubicCompensation k)*
      (if n-k = 0 then 1/2 else 3*((n-k : ℕ) : ℝ)*connectedCubicCompensation (n-k))) =
      9*∑ k ∈ Finset.Ioo 0 n,
        ((k : ℝ)*connectedCubicCompensation k)*
          (((n-k : ℕ) : ℝ)*connectedCubicCompensation (n-k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by have h := Finset.mem_Ioo.mp hk; omega
    have hj0 : n-k ≠ 0 := by have h := Finset.mem_Ioo.mp hk; omega
    rw [if_neg hk0,if_neg hj0]
    ring
  rw [hinner]
  ring

theorem compensationCandidate_recurrence (n : ℕ) :
    2*compensationCandidate (n+1) =
      (3*(n : ℝ)+2)*compensationCandidate n+
        ∑ a ∈ Finset.antidiagonal n, compensationCandidate a.1*compensationCandidate a.2 := by
  by_cases hn : n = 0
  · subst n
    norm_num [compensationCandidate,Finset.antidiagonal,connectedCubicCompensation_one]
  · rw [candidate_convolution n hn]
    have h := connectedCubicCompensation_nonlinear_recurrence n
    rw [if_neg hn] at h
    simp only [compensationCandidate,if_neg (by omega : n+1 ≠ 0),if_neg hn]
    push_cast
    linear_combination h/4

theorem logCoefficient_succ_eq_literal_compensation (n : ℕ) :
    logCoefficient (n+1) = compensationCandidate n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [compensationCandidate,logCoefficient_one]
    | succ n =>
      have hB := logCoefficient_recurrence n
      have hC := compensationCandidate_recurrence n
      have hn : n < n+1 := by omega
      rw [ih n hn] at hB
      have hsum : (∑ a ∈ Finset.antidiagonal n,
          logCoefficient (a.1+1)*logCoefficient (a.2+1)) =
          ∑ a ∈ Finset.antidiagonal n, compensationCandidate a.1*compensationCandidate a.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hab := Finset.mem_antidiagonal.mp ha
        rw [ih a.1 (by omega),ih a.2 (by omega)]
      rw [hsum] at hB
      linarith

theorem logCoefficient_positive_order_eq_literal (n : ℕ) (hn : 0 < n) :
    logCoefficient (n+1) = 3*(n : ℝ)*connectedCubicCompensation n := by
  rw [logCoefficient_succ_eq_literal_compensation,compensationCandidate,if_neg (by omega)]

theorem actual_boundary_slope_eq_literal_connected_compensation (n : ℕ) (hn : 0 < n) :
    (boundaryPolynomial (n+1) 1).derivative.eval 0 =
      6*(n : ℝ)*((n+1).factorial : ℝ)*connectedCubicCompensation n := by
  rw [actual_slope_eq_logCoefficient,logCoefficient_positive_order_eq_literal n hn]
  ring

end PerronWright.BrownianBoundaryLiteralConnectedCompensation
