import PerronWright.Probability.BrownianKilledAreaResolventMassBounds
import PerronWright.Probability.BrownianKilledAreaResolventSymmetry
import PerronWright.Probability.BrownianKilledGreenWeightedBound

/-! # Actual pointwise finiteness of every killed-area moment resolvent

The genuine weighted zeroth Green estimate dominates each Kac insertion
by a finite total state mass. Actual all-order symmetry converts the
initial-state mass to the already proved target-state mass. Thus every
pointwise value is finite, and its real kernels are integrable in both
states. No pointwise finiteness or boundary-exchange premise is assumed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledAreaResolventPointwiseFiniteness

open BrownianKilledAreaMomentResolvent BrownianKilledAreaResolventMassBounds
open BrownianKilledAreaResolventSymmetry BrownianKilledGreenWeightedBound
open BrownianKilledGreenKernel

theorem initial_total_mass_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    (∫⁻ z : ℝ, resolvent n p z y) ≠ ⊤ := by
  rw [initial_lintegral_eq_target_lintegral n p hp y]
  exact resolvent_total_mass_ne_top n p hp y

theorem resolvent_succ_mass_bound (n : ℕ) (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent (n+1) p x y ≤ ((n+1 : ℕ) : ℝ≥0∞)*
      (ENNReal.ofReal ((|x|+1/Real.sqrt (2*p))/Real.sqrt (2*p))*
        ∫⁻ z : ℝ, resolvent n p z y) := by
  rw [resolvent_succ]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∫⁻ z : ℝ, ENNReal.ofReal ((|x|+1/Real.sqrt (2*p))/Real.sqrt (2*p))*
        resolvent n p z y := by
      apply lintegral_mono
      intro z
      exact mul_le_mul' (actual_resolvent_mul_target_le p hp x z) le_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem resolvent_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    resolvent n p x y ≠ ⊤ := by
  cases n with
  | zero => exact resolvent_zero_ne_top p hp x y
  | succ n =>
    have hf : ((n+1 : ℕ) : ℝ≥0∞)*
        (ENNReal.ofReal ((|x|+1/Real.sqrt (2*p))/Real.sqrt (2*p))*
          ∫⁻ z : ℝ, resolvent n p z y) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp : ((n+1 : ℕ) : ℝ≥0∞) ≠ ⊤)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (initial_total_mass_ne_top n p hp y))
    exact ne_of_lt ((resolvent_succ_mass_bound n p hp x y).trans_lt (lt_top_iff_ne_top.mpr hf))

theorem integrable_resolvent_real_target (n : ℕ) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    Integrable (fun y : ℝ ↦ (resolvent n p x y).toReal) volume :=
  integrable_toReal_of_lintegral_ne_top
    ((measurable_resolvent n p).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (resolvent_total_mass_ne_top n p hp x)

theorem integrable_resolvent_real_initial (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    Integrable (fun x : ℝ ↦ (resolvent n p x y).toReal) volume :=
  integrable_toReal_of_lintegral_ne_top
    ((measurable_resolvent n p).comp (measurable_id.prodMk measurable_const)).aemeasurable
    (initial_total_mass_ne_top n p hp y)

end PerronWright.BrownianKilledAreaResolventPointwiseFiniteness
