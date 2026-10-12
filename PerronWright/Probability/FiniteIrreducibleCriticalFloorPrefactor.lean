import PerronWright.Probability.FiniteIrreducibleCriticalTuplePrefactor

/-!
# Literal floor-size instances of the finite enumeration prefactor

The floor window and its normalized limit are proved from the actual
integer floor. The underlying prefactor is the genuine factorial-formula
prefactor; this file makes no claim about the residual expectation.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleCriticalFloorPrefactor

open FiniteIrreducibleCriticalPrefactorScaling FiniteIrreducibleCriticalTuplePrefactor

/-- One eventual threshold covers every literal floor in the real window. -/
theorem eventually_floor_normalized_window
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (a b : ℝ) (ha : 0 < a) :
    ∀ᶠ m in atTop, ∀ x : ℝ, a ≤ x → x ≤ b →
      a/2 ≤ normalizedSize (N m) (CriticalScaling.size x (N m)) ∧
        normalizedSize (N m) (CriticalScaling.size x (N m)) ≤ b := by
  have he : Tendsto (fun m ↦ 1 / (N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2/3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
    simpa only [Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _), one_div] using hpow
  filter_upwards [he.eventually (Iio_mem_nhds (show (0 : ℝ) < a/2 by linarith))]
    with m hm x hxa hxb
  have hx : 0 ≤ x := ha.le.trans hxa
  have herror := CriticalScaling.size_normalized_error hx (hN m)
  have hscale : (0 : ℝ) < (N m : ℝ)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hN m)) _
  constructor
  · change a/2 ≤ (CriticalScaling.size x (N m) : ℝ) / (N m : ℝ)^(2/3 : ℝ)
    have hl := (abs_le.mp herror).1
    linarith
  · change (CriticalScaling.size x (N m) : ℝ) / (N m : ℝ)^(2/3 : ℝ) ≤ b
    apply (div_le_iff₀ hscale).mpr
    exact (CriticalSizeTuple.size_le_scaled hx (N m)).trans
      (mul_le_mul_of_nonneg_right hxb hscale.le)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Uniform enumeration prefactor ratio for literal floors across the whole
real size window and every bounded surplus vector. -/
theorem eventually_uniform_floor_prefactor_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ x : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ x i) → (∀ i, x i ≤ b) → (∀ i, r i ≤ R) →
      |((N m : ℝ)^(2*(q : ℝ)/3) *
          enumerationPrefactor M (N m) (fun i ↦ CriticalScaling.size (x i) (N m)) r
            (rawTime lambda (N m))) /
        tupleGaussianMainTerm M hM lambda (N m)
          (fun i ↦ CriticalScaling.size (x i) (N m)) r - 1| ≤ ε := by
  filter_upwards [hNt.eventually (eventually_uniform_tuple_prefactor_ratio M hM q R
    lambda (a/2) b (by linarith) hb hε),
    eventually_floor_normalized_window N hN hNt a b ha]
    with m hm hfloor x r hxa hxb hr
  exact hm _ r (fun i ↦ (hfloor (x i) (hxa i) (hxb i)).1)
    (fun i ↦ (hfloor (x i) (hxa i) (hxb i)).2) hr

/-- The true prefactor for actual floors, including varying real size
coordinates, converges to the literal Gaussian product. -/
theorem tendsto_scaled_tuple_prefactor_floor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ}
    (R : ℕ) (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (x : ℕ → Fin q → ℝ) (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ (N m : ℝ)^(2*(q : ℝ)/3) *
      enumerationPrefactor M (N m) (fun i ↦ CriticalScaling.size (x m i) (N m)) r
        (rawTime lambda (N m))) atTop
      (𝓝 (limitingTupleGaussianMainTerm M hM lambda s r)) := by
  have hwindow := eventually_floor_normalized_window N hN hNt a b ha
  apply tendsto_scaled_tuple_prefactor M hM R lambda (a/2) b (by linarith) hb N hNt
    (fun m i ↦ CriticalScaling.size (x m i) (N m)) r hr
  · filter_upwards [hwindow] with m hm i
    exact (hm (x m i) (hxa m i) (hxb m i)).1
  · filter_upwards [hwindow] with m hm i
    exact (hm (x m i) (hxa m i) (hxb m i)).2
  · exact hs
  · intro i
    exact CriticalSizeTuple.size_normalized_varying_tendsto N hN hNt (fun m ↦ x m i)
      (fun m ↦ ha.le.trans (hxa m i)) (hxs i)

end PerronWright.FiniteIrreducibleCriticalFloorPrefactor

