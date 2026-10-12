import PerronWright.Probability.CriticalScaling

/-!
# Exact conversion of countable spectral drift to a critical parameter shift

The unrenormalized edge time is expressed exactly as a spectrally normalized
time with a varying critical-window parameter.  Its convergence to
`lambda+theta` is proved from the drift hypothesis of the last main theorem.
No factorial asymptotic or process convergence is assumed in this algebraic
conversion.
-/

open Filter Topology
open scoped Topology Real

noncomputable section

namespace PerronWright.CriticalParameterDrift

/-- Critical-window parameter obtained when the truncated Perron root is
absorbed into the normalized graph time. -/
def effectiveParameter (lambda : ℝ) (sigma : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) *
    ((1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) * sigma n - 1)

private theorem scale_cancel {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = 1 := by
  rw [← Real.rpow_add (by exact_mod_cast hn)]
  norm_num

/-- Exact critical-parameter decomposition, including the lower-order
product of the fixed window parameter and the spectral perturbation. -/
theorem effectiveParameter_eq {n : ℕ} (hn : 0 < n)
    (lambda : ℝ) (sigma : ℕ → ℝ) :
    effectiveParameter lambda sigma n =
      lambda + (n : ℝ) ^ (1 / 3 : ℝ) * (sigma n - 1) + lambda * (sigma n - 1) := by
  unfold effectiveParameter
  calc
    _ = (n : ℝ) ^ (1 / 3 : ℝ) * (sigma n - 1) +
        lambda * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) * sigma n := by ring
    _ = _ := by rw [scale_cancel hn]; ring

theorem inverseScale_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ ↦ x ^ (-(1 / 3 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  exact h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

/-- The critical drift hypothesis already implies convergence of the
truncated spectral roots to one. -/
theorem sigma_tendsto_one {sigma : ℕ → ℝ} {theta : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (sigma n - 1)) atTop (nhds theta)) :
    Tendsto sigma atTop (nhds 1) := by
  have hd : Tendsto (fun n ↦ sigma n - 1) atTop (nhds 0) := by
    have hp := inverseScale_tendsto_zero.mul h
    simp only [zero_mul] at hp
    apply hp.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hc := scale_cancel (by omega : 0 < n)
    calc
      _ = ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) * (sigma n - 1) := by ring
      _ = _ := by rw [hc, one_mul]
  have ht := hd.add_const 1
  simpa only [sub_add_cancel, zero_add] using ht

/-- The varying normalized parameter converges to the shifted parameter
in the unrenormalized countable theorem. -/
theorem effectiveParameter_tendsto {sigma : ℕ → ℝ} {theta : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (sigma n - 1)) atTop (nhds theta))
    (lambda : ℝ) :
    Tendsto (effectiveParameter lambda sigma) atTop (nhds (lambda + theta)) := by
  have hs : Tendsto (fun n ↦ sigma n - 1) atTop (nhds 0) := by
    simpa only [sub_self] using (sigma_tendsto_one h).sub_const 1
  have hl : Tendsto (fun _ : ℕ ↦ lambda) atTop (nhds lambda) := tendsto_const_nhds
  have ht := (hl.add h).add (hl.mul hs)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (effectiveParameter_eq (by omega : 0 < n) lambda sigma).symm

theorem sigma_pos_eventually {sigma : ℕ → ℝ} {theta : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (sigma n - 1)) atTop (nhds theta)) :
    ∀ᶠ n : ℕ in atTop, 0 < sigma n :=
  (sigma_tendsto_one h).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Exact unclipped normalized time identity at every positive size. -/
theorem effective_raw_time_eq {n : ℕ} (hn : 0 < n)
    (lambda : ℝ) (sigma : ℕ → ℝ) :
    1 + effectiveParameter lambda sigma n * (n : ℝ) ^ (-(1 / 3 : ℝ)) =
      (1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) * sigma n := by
  unfold effectiveParameter
  have hc := scale_cancel hn
  calc
    _ = 1 + ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) *
        ((1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) * sigma n - 1) := by ring
    _ = _ := by rw [hc]; ring

/-- The nonnegative finite-size time convention is also compatible with
spectral normalization, not only the eventual unclipped times. -/
theorem effective_time_eq {n : ℕ} (hn : 0 < n)
    (lambda : ℝ) (sigma : ℕ → ℝ) (hs : 0 ≤ sigma n) :
    CriticalScaling.time (effectiveParameter lambda sigma n) n =
      CriticalScaling.time lambda n * sigma n := by
  unfold CriticalScaling.time
  rw [effective_raw_time_eq hn lambda sigma]
  simpa only [zero_mul] using
    (max_mul_of_nonneg (1 + lambda * (n : ℝ) ^ (-(1 / 3 : ℝ))) 0 hs).symm

/-- Equality of the literal edge hazards with and without absorbing the
truncated Perron root into the time parameter. -/
theorem edge_hazard_eq {n : ℕ} (hn : 0 < n)
    (lambda : ℝ) (sigma : ℕ → ℝ) (hs : 0 < sigma n) (kernelValue : ℝ) :
    CriticalScaling.time lambda n * kernelValue / (n : ℝ) =
      CriticalScaling.time (effectiveParameter lambda sigma n) n * kernelValue /
        ((n : ℝ) * sigma n) := by
  rw [effective_time_eq hn lambda sigma hs.le]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end PerronWright.CriticalParameterDrift
