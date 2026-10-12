import PerronWright.Probability.CriticalScalarField
import PerronWright.Probability.CriticalConnectedSampling

/-! # Actual Gaussian enumeration on the local graph size scale -/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalConnectedEnumeration

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The already proved compact enumeration applies to the actual graph
critical time, with no square-root window condition supplied as an
additional hypothesis. Sizes may vary across the whole bounded window. -/
theorem gaussian_ratio_tendsto_one_critical_scale (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (N k r : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (hk : Tendsto k atTop atTop) (lambda b : ℝ) (hb : 0 ≤ b)
    (hsize : ∀ᶠ m in atTop, (k m : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ))
    (hr : ∀ᶠ m in atTop, r m ≤ R) :
    Tendsto (fun m ↦ M.connectedWeight (CriticalScaling.time lambda (N m)) (k m) (r m) /
      BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm
        M hM (k m) (r m) (CriticalScaling.time lambda (N m))) atTop (𝓝 1) := by
  let L : ℝ := Real.sqrt b * |lambda|
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  obtain ⟨C,hC,hbound⟩ :=
    CompactPerronWrightTheorem.exists_boundedSurplus_gaussian_relative_bound M hM R L hL
  have herror : Tendsto (fun m ↦ C*(k m : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
      (tendsto_natCast_atTop_atTop.comp hk)
    simpa only [mul_zero,Function.comp_def] using hpow.const_mul C
  have he : ∀ᶠ m in atTop,
      |M.connectedWeight (CriticalScaling.time lambda (N m)) (k m) (r m) /
        BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm
          M hM (k m) (r m) (CriticalScaling.time lambda (N m)) - 1| ≤
          C*(k m : ℝ)^(-(1/2 : ℝ)) := by
    filter_upwards [hk.eventually hbound,hk.eventually (eventually_ge_atTop 1),
      CriticalScalarField.sqrt_time_bound_eventually N hN hNt lambda b hb,hsize,hr]
      with m hm hk1 htime hsz hrr
    have hkpos : (0 : ℝ) < k m := Nat.cast_pos.mpr (by omega)
    have hsqrt : 0 < Real.sqrt (k m : ℝ) := Real.sqrt_pos.mpr hkpos
    have hwindow : |CriticalScaling.time lambda (N m)-1| ≤ L*(k m : ℝ)^(-(1/2 : ℝ)) := by
      have h : |CriticalScaling.time lambda (N m)-1| ≤ L / Real.sqrt (k m : ℝ) :=
        (le_div_iff₀ hsqrt).mpr (by
        simpa only [L,mul_comm] using htime (k m) hsz)
      simpa only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg (Nat.cast_nonneg _)] using h
    exact hm (r m) hrr _ hwindow
  have hlo := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub herror
  have hhi := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add herror
  simp only [sub_zero,add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [he] with m hm
    linarith [(abs_le.mp hm).1]
  · filter_upwards [he] with m hm
    linarith [(abs_le.mp hm).2]

/-- The enumeration ratio for the literal floors in a positive compact
size window converges to one, even for varying sizes and surpluses. -/
theorem gaussian_ratio_tendsto_one_floor_window (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (N : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → ℝ) (r : ℕ → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m, a ≤ x m) (hxb : ∀ m, x m ≤ b)
    (hr : ∀ᶠ m in atTop, r m ≤ R) :
    Tendsto (fun m ↦ M.connectedWeight (CriticalScaling.time lambda (N m))
      (CriticalScaling.size (x m) (N m)) (r m) /
      BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm M hM
        (CriticalScaling.size (x m) (N m)) (r m) (CriticalScaling.time lambda (N m)))
      atTop (𝓝 1) := by
  have hk : Tendsto (fun m ↦ CriticalScaling.size (x m) (N m)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [CriticalConnectedSampling.eventually_size_ge_on_window N hNt a ha K]
      with m hm
    exact hm (x m) (hxa m)
  apply gaussian_ratio_tendsto_one_critical_scale M hM R N
    (fun m ↦ CriticalScaling.size (x m) (N m)) r hN hNt hk lambda b hb
  · exact Eventually.of_forall (fun m ↦
      (CriticalSizeTuple.size_le_scaled (ha.le.trans (hxa m)) _).trans
        (mul_le_mul_of_nonneg_right (hxb m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  · exact hr

end PerronWright.CriticalConnectedEnumeration
