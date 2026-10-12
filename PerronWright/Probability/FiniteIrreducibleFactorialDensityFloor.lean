import PerronWright.Probability.FiniteIrreducibleCriticalFloorPrefactor
import PerronWright.Probability.FactorialWindowBounds
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform literal-density approximation by actual integer floors

Continuity is proved for the literal Wright size factors. Compactness of
the positive finite-dimensional size box and finiteness of the bounded
surplus vectors give a single threshold for every floor in the window.
This file is pure real analysis and does not identify a random law.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleFactorialDensityFloor

open FiniteIrreducibleCriticalPrefactorScaling

theorem density_tendsto_positive (alpha beta lambda : ℝ) {q : ℕ}
    (r : Fin q → ℕ) (x : ℕ → Fin q → ℝ) (s : Fin q → ℝ)
    (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun n ↦ x n i) atTop (𝓝 (s i))) :
    Tendsto (fun n ↦ FactorialDensity.density alpha beta lambda (x n) r)
      atTop (𝓝 (FactorialDensity.density alpha beta lambda s r)) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hxs i)
  have he : Tendsto (fun n ↦
      Real.exp (-FactorialDensity.criticalExponent alpha beta lambda (∑ i, x n i)))
      atTop (𝓝 (Real.exp (-FactorialDensity.criticalExponent alpha beta lambda (∑ i, s i)))) := by
    have hc : Continuous (fun z : ℝ ↦ Real.exp (-FactorialDensity.criticalExponent alpha beta lambda z)) := by
      unfold FactorialDensity.criticalExponent
      fun_prop
    exact hc.tendsto _ |>.comp hsum
  have hp := tendsto_finsetProd Finset.univ (fun i _ ↦
    (CriticalLocalSizeFactor.sizeFactor_continuousAt_positive beta (r i) (hs i)).tendsto.comp (hxs i))
  exact he.mul hp

theorem density_continuousOn_box (alpha beta lambda : ℝ) {q : ℕ}
    (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : Fin q → ℝ ↦ FactorialDensity.density alpha beta lambda x r)
      (Set.Icc (fun _ ↦ a) (fun _ ↦ b)) := by
  unfold FactorialDensity.density
  apply ContinuousOn.mul
  · have h : Continuous (fun x : Fin q → ℝ ↦
        Real.exp (-FactorialDensity.criticalExponent alpha beta lambda (∑ i, x i))) := by
      unfold FactorialDensity.criticalExponent
      fun_prop
    exact h.continuousOn
  · apply continuousOn_finsetProd
    intro i _
    exact (FactorialDensity.sizeFactor_continuousOn_Icc beta (r i) ha).comp
      (continuous_apply i).continuousOn (fun x hx ↦ ⟨hx.1 i, hx.2 i⟩)

theorem density_uniformContinuousOn_box (alpha beta lambda : ℝ) {q : ℕ}
    (r : Fin q → ℕ) {a b : ℝ} (ha : 0 < a) :
    UniformContinuousOn (fun x : Fin q → ℝ ↦ FactorialDensity.density alpha beta lambda x r)
      (Set.Icc (fun _ ↦ a) (fun _ ↦ b)) :=
  isCompact_Icc.uniformContinuousOn_of_continuous
    (density_continuousOn_box alpha beta lambda r ha)

theorem normalized_floor_tuple_dist_le {q n : ℕ} (hn : 0 < n)
    (x : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i) :
    dist (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) x ≤
      1 / (n : ℝ)^(2/3 : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  rw [Real.dist_eq]
  exact CriticalScaling.size_normalized_error (hx i) hn

theorem floor_error_tendsto :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)^(2/3 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2/3)).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _), one_div] using h

theorem eventually_floor_normalized_box (q : ℕ) (a b : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) →
      (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) ∈
        Set.Icc (fun _ ↦ a/2) (fun _ ↦ b) := by
  filter_upwards [floor_error_tendsto.eventually
      (Iio_mem_nhds (show (0 : ℝ) < a/2 by linarith)),
    eventually_ge_atTop (1 : ℕ)] with n he hn x hxa hxb
  constructor
  · intro i
    have h := CriticalScaling.size_normalized_error (ha.le.trans (hxa i)) (by omega : 0 < n)
    have hl := (abs_le.mp h).1
    change a/2 ≤ (CriticalScaling.size (x i) n : ℝ)/(n : ℝ)^(2/3 : ℝ)
    linarith [hxa i]
  · intro i
    have hs := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega : 0 < n)) (2/3 : ℝ)
    change (CriticalScaling.size (x i) n : ℝ)/(n : ℝ)^(2/3 : ℝ) ≤ b
    apply (div_le_iff₀ hs).mpr
    exact (CriticalSizeTuple.size_le_scaled (ha.le.trans (hxa i)) n).trans
      (mul_le_mul_of_nonneg_right (hxb i) hs.le)

theorem eventually_uniform_floor_density_fixed_surplus
    (alpha beta lambda : ℝ) {q : ℕ} (r : Fin q → ℕ)
    (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) →
      |FactorialDensity.density alpha beta lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) r -
        FactorialDensity.density alpha beta lambda x r| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (density_uniformContinuousOn_box alpha beta lambda r (show 0 < a/2 by linarith)) ε hε
  filter_upwards [eventually_floor_normalized_box q a b ha,
    floor_error_tendsto.eventually (Iio_mem_nhds hδ),
    eventually_ge_atTop (1 : ℕ)] with n hbox he hn x hxa hxb
  rw [← Real.dist_eq]
  exact hclose _ (hbox x hxa hxb) x ⟨fun i ↦ by linarith [hxa i], hxb⟩
    ((normalized_floor_tuple_dist_le (by omega) x (fun i ↦ ha.le.trans (hxa i))).trans_lt he)

/-- A common threshold covers the actual floors and every surplus vector
in the finite bounded family; no uniform-continuity interface is assumed. -/
theorem eventually_uniform_floor_density (alpha beta lambda : ℝ) (q R : ℕ)
    (a b : ℝ) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) → (∀ i, r i ≤ R) →
      |FactorialDensity.density alpha beta lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) r -
        FactorialDensity.density alpha beta lambda x r| < ε := by
  have hfamily : ∀ r : Fin q → Fin (R+1), ∀ᶠ n : ℕ in atTop,
      ∀ x : Fin q → ℝ, (∀ i, a ≤ x i) → (∀ i, x i ≤ b) →
      |FactorialDensity.density alpha beta lambda
          (fun i ↦ normalizedSize n (CriticalScaling.size (x i) n)) (fun i ↦ (r i : ℕ)) -
        FactorialDensity.density alpha beta lambda x (fun i ↦ (r i : ℕ))| < ε :=
    fun r ↦ eventually_uniform_floor_density_fixed_surplus alpha beta lambda _ a b ha hε
  filter_upwards [eventually_all.mpr hfamily] with n hn x r hxa hxb hr
  exact hn (fun i ↦ ⟨r i, Nat.lt_succ_of_le (hr i)⟩) x hxa hxb

end PerronWright.FiniteIrreducibleFactorialDensityFloor
