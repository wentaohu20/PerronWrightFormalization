import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.Order.Field

/-! # Genuine finite quadratures for continuous Brownian-area tests

The analytic convergence and finite minimum-kernel sums below are purely
deterministic. They are used to pass actual finite Gaussian bridge laws
to the literal continuous path integral, without an assumed area law.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.BrownianUniformQuadrature

def grid (T : ℝ) (m i : ℕ) : ℝ := (i : ℝ)*T/(m : ℝ)

def leftSum (T : ℝ) (m : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, (T/(m : ℝ))*g (grid T m i)

theorem grid_step (T : ℝ) (m i : ℕ) :
    grid T m (i+1)-grid T m i = T/(m : ℝ) := by
  simp only [grid,Nat.cast_add,Nat.cast_one]
  ring

theorem grid_zero (T : ℝ) (m : ℕ) : grid T m 0 = 0 := by simp [grid]

theorem grid_end (T : ℝ) (m : ℕ) (hm : 0 < m) : grid T m m = T := by
  have hne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [grid,hne]

theorem grid_mem (T : ℝ) (hT : 0 ≤ T) (m i : ℕ) (hi : i ≤ m) :
    grid T m i ∈ Icc 0 T := by
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) (Nat.cast_nonneg _)
  · by_cases hm : m = 0
    · subst m
      simp [grid,hT]
    · have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      apply (div_le_iff₀ hmpos).mpr
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hT).trans_eq (mul_comm _ _)

theorem grid_mono (T : ℝ) (hT : 0 ≤ T) (m : ℕ) : Monotone (grid T m) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT) (Nat.cast_nonneg _)

theorem integral_sub_leftSum (T : ℝ) (m : ℕ) (hm : 0 < m)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in 0..T, g x)-leftSum T m g =
      ∑ i ∈ Finset.range m,
        ∫ x in grid T m i..grid T m (i+1), g x-g (grid T m i) := by
  have hp := intervalIntegral.sum_integral_adjacent_intervals
    (a := grid T m) (n := m) (f := g) (μ := volume)
    (fun i _ ↦ hg.intervalIntegrable _ _)
  rw [grid_zero,grid_end T m hm] at hp
  rw [← hp,leftSum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const]
  simp only [smul_eq_mul,grid_step]

theorem quadrature_error_le (T : ℝ) (hT : 0 ≤ T) (m : ℕ) (hm : 0 < m)
    (g : ℝ → ℝ) (hg : Continuous g) (η : ℝ)
    (hclose : ∀ i < m, ∀ x ∈ Icc (grid T m i) (grid T m (i+1)),
      ‖g x-g (grid T m i)‖ ≤ η) :
    ‖(∫ x in 0..T, g x)-leftSum T m g‖ ≤ η*T := by
  rw [integral_sub_leftSum T m hm g hg]
  apply (norm_sum_le _ _).trans
  have hi (i : ℕ) (him : i ∈ Finset.range m) :
      ‖∫ x in grid T m i..grid T m (i+1), g x-g (grid T m i)‖ ≤
        η*(T/(m : ℝ)) := by
    have hab := grid_mono T hT m (Nat.le_succ i)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := grid T m i) (b := grid T m (i+1))
      (fun x hx ↦ hclose i (Finset.mem_range.mp him) x (by
        have hx' : x ∈ Ioc (grid T m i) (grid T m (i+1)) := by
          simpa only [uIoc_of_le hab] using hx
        exact ⟨le_of_lt hx'.1,hx'.2⟩))
    simpa only [grid_step,abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg _))] using h
  apply (Finset.sum_le_sum hi).trans_eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

theorem leftSum_tendsto_integral (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n : ℕ ↦ leftSum T (n+1) g) atTop (𝓝 (∫ x in 0..T, g x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(T+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) η hη
  have hd : Tendsto (fun n : ℕ ↦ T/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds hδ))
  refine ⟨N,fun n hn ↦ ?_⟩
  rw [dist_comm,dist_eq_norm]
  have he := quadrature_error_le T hT (n+1) (Nat.succ_pos n) g hg η (by
    intro i hi x hx
    have hl := grid_mem T hT (n+1) i (Nat.le_of_lt hi)
    have hr := grid_mem T hT (n+1) (i+1) hi
    apply le_of_lt (hunif x ⟨hl.1.trans hx.1,hx.2.trans hr.2⟩
      (grid T (n+1) i) hl ?_)
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hx.1)]
    apply lt_of_le_of_lt ?_ (hN n hn)
    calc x-grid T (n+1) i ≤ grid T (n+1) (i+1)-grid T (n+1) i := sub_le_sub_right hx.2 _
      _ = T/((n+1 : ℕ) : ℝ) := grid_step _ _ _)
  apply lt_of_le_of_lt he
  dsimp [η]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by linarith : 0 < T+1)).mpr
  convert (mul_lt_mul_of_pos_left (show T < T+1 by linarith) hε) using 1

private def sumIndex (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (i : ℝ)
private def sumMin (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, min (i : ℝ) (j : ℝ)

private theorem sumIndex_formula (m : ℕ) : 2*sumIndex m = (m : ℝ)*((m : ℝ)-1) := by
  induction m with
  | zero => simp [sumIndex]
  | succ m ih =>
    simp only [sumIndex,Finset.sum_range_succ] at *
    push_cast
    nlinarith

private theorem sumMin_step (m : ℕ) : sumMin (m+1) = sumMin m+(m : ℝ)^2 := by
  have hl : ∑ i ∈ Finset.range m, min (i : ℝ) (m : ℝ) = sumIndex m := by
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_left (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have hr : ∑ i ∈ Finset.range m, min (m : ℝ) (i : ℝ) = sumIndex m := by
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_right (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hi)))
  unfold sumMin
  simp only [Finset.sum_range_succ,Finset.sum_add_distrib,min_self]
  rw [hl,hr]
  have h := sumIndex_formula m
  nlinarith

private theorem sumMin_formula (m : ℕ) :
    6*sumMin m = (m : ℝ)*((m : ℝ)-1)*(2*(m : ℝ)-1) := by
  induction m with
  | zero => simp [sumMin]
  | succ m ih =>
    rw [sumMin_step]
    push_cast
    nlinarith

theorem grid_quadratic_sum (T : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (T/(m : ℝ))*(T/(m : ℝ))*
        (min (grid T m i) (grid T m j)-grid T m i*grid T m j/T)) =
      T^3/12*(1-1/(m : ℝ)^2) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hTne := ne_of_gt hT
  have hmne := ne_of_gt hmpos
  have hterm (i j : ℕ) :
      (T/(m : ℝ))*(T/(m : ℝ))*
        (min (grid T m i) (grid T m j)-grid T m i*grid T m j/T) =
      (T^3/(m : ℝ)^3)*min (i : ℝ) (j : ℝ) -
        (T^3/(m : ℝ)^4)*((i : ℝ)*(j : ℝ)) := by
    simp only [grid,mul_div_assoc]
    rw [← min_mul_of_nonneg _ _ (le_of_lt (div_pos hT hmpos))]
    field_simp
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
  change (T^3/(m : ℝ)^3)*sumMin m - (T^3/(m : ℝ)^4)*(sumIndex m*sumIndex m) = _
  have h1 := sumIndex_formula m
  have h2 := sumMin_formula m
  have he1 : sumIndex m = (m : ℝ)*((m : ℝ)-1)/2 := by linarith
  have he2 : sumMin m = (m : ℝ)*((m : ℝ)-1)*(2*(m : ℝ)-1)/6 := by linarith
  rw [he1,he2]
  field_simp
  ring

end PerronWright.BrownianUniformQuadrature
