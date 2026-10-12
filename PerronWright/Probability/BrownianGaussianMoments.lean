import PerronWright.Probability.BrownianGaussianSkeleton

/-!
# Proved fourth-moment and tail bounds on the constructed Gaussian skeleton

The constant is the literal finite standard-Gaussian fourth moment, not
an assumed integrability or moment interface. Gaussian scaling proves
the exact variance-squared identity. Applied to the genuine rational
skeleton law, this supplies the increment estimate needed for a later
dyadic continuity construction. No continuous Brownian realization is
claimed here.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGaussianMoments

open BrownianGaussianSkeleton

def fourthMomentConstant : ℝ := ∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 1

theorem gaussian_fourth_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ ‖x‖ ^ 4) (gaussianReal 0 v) := by
  simpa only [id_eq] using
    (memLp_id_gaussianReal' (μ := 0) (v := v) 4 (by norm_num)).integrable_norm_pow' (p := 4)

theorem fourthMomentConstant_nonneg : 0 ≤ fourthMomentConstant :=
  integral_nonneg (fun _ ↦ by positivity)

/-- Exact Gaussian scaling of the actual finite fourth moment. No
fourth-moment formula or integrability hypothesis is postulated. -/
theorem gaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 v) = (v : ℝ) ^ 2 * fourthMomentConstant := by
  have hsqrt : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt v.property
  have hv : NNReal.mk ((Real.sqrt (v : ℝ)) ^ 2) (sq_nonneg _) * 1 = v := by
    apply NNReal.eq
    change (Real.sqrt (v : ℝ)) ^ 2 * 1 = (v : ℝ)
    simpa only [mul_one] using hsqrt
  have hs : HasLaw (fun x : ℝ ↦ Real.sqrt (v : ℝ) * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    simpa only [id_eq,mul_zero,hv] using
      gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt (v : ℝ))
  have hnorm : AEStronglyMeasurable (fun x : ℝ ↦ ‖x‖ ^ 4) (gaussianReal 0 v) :=
    (continuous_norm.pow 4).aestronglyMeasurable
  calc
    _ = ∫ x : ℝ, ‖Real.sqrt (v : ℝ) * x‖ ^ 4 ∂gaussianReal 0 1 := by
      simpa only [Function.comp_def] using (hs.integral_comp hnorm).symm
    _ = _ := by
      have hfun : (fun x : ℝ ↦ ‖Real.sqrt (v : ℝ) * x‖ ^ 4) =
          fun x : ℝ ↦ (v : ℝ) ^ 2 * ‖x‖ ^ 4 := by
        funext x
        rw [norm_mul,mul_pow,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        have hp : (Real.sqrt (v : ℝ)) ^ 4 = (v : ℝ) ^ 2 := by
          calc
            _ = ((Real.sqrt (v : ℝ)) ^ 2) ^ 2 := by ring
            _ = _ := congrArg (fun z : ℝ ↦ z ^ 2) hsqrt
        rw [hp]
      rw [hfun,integral_const_mul]
      rfl

theorem rational_increment_fourth_integrable (q r : RationalTime) :
    Integrable (fun x ↦ ‖rationalProcess q x - rationalProcess r x‖ ^ 4) rationalLaw := by
  have hh : MemLp (fun x ↦ rationalProcess q x - rationalProcess r x) 4 rationalLaw :=
    (rational_hasLaw_sub q r).hasGaussianLaw.memLp (by norm_num)
  exact hh.integrable_norm_pow' (p := 4)

/-- Exact fourth moment under the genuinely constructed rational-time
probability law, with the actual rational-time distance. -/
theorem rational_increment_fourth_moment (q r : RationalTime) :
    (∫ x, ‖rationalProcess q x - rationalProcess r x‖ ^ 4 ∂rationalLaw) =
      fourthMomentConstant * |(q.val : ℝ) - (r.val : ℝ)| ^ 2 := by
  calc
    _ = ∫ u : ℝ, ‖u‖ ^ 4 ∂gaussianReal 0 (nndist (q.val : ℝ) (r.val : ℝ)) := by
      have hm : AEStronglyMeasurable (fun u : ℝ ↦ ‖u‖ ^ 4)
          (gaussianReal 0 (nndist (q.val : ℝ) (r.val : ℝ))) :=
        (continuous_norm.pow 4).aestronglyMeasurable
      simpa only [Function.comp_def] using (rational_hasLaw_sub q r).integral_comp
        hm
    _ = _ := by
      rw [gaussian_fourth_moment]
      simp only [coe_nndist,Real.dist_eq]
      ring

/-- Genuine sampled-law increment tail bound, proved by applying
Markov's inequality to the actual integrable fourth power. -/
theorem rational_increment_tail_bound (q r : RationalTime) {ε : ℝ} (hε : 0 < ε) :
    rationalLaw.real {x | ε ≤ ‖rationalProcess q x - rationalProcess r x‖} ≤
      fourthMomentConstant * |(q.val : ℝ) - (r.val : ℝ)| ^ 2 / ε ^ 4 := by
  have hpow : 0 < ε ^ 4 := pow_pos hε _
  have hi := (rational_increment_fourth_integrable q r).div_const (ε ^ 4)
  have hnn : 0 ≤ᵐ[rationalLaw] (fun x ↦ ‖rationalProcess q x - rationalProcess r x‖ ^ 4 / ε ^ 4) :=
    Filter.Eventually.of_forall (fun _ ↦ by positivity)
  have hh := hi.measure_le_integral hnn (s := {x | ε ≤ ‖rationalProcess q x - rationalProcess r x‖})
    (fun x hx ↦ by
      rw [le_div_iff₀ hpow,one_mul]
      exact pow_le_pow_left₀ hε.le hx 4)
  have ht : rationalLaw.real {x | ε ≤ ‖rationalProcess q x - rationalProcess r x‖} ≤
      ∫ x, ‖rationalProcess q x - rationalProcess r x‖ ^ 4 / ε ^ 4 ∂rationalLaw := by
    calc
      _ ≤ (ENNReal.ofReal (∫ x, ‖rationalProcess q x - rationalProcess r x‖ ^ 4 / ε ^ 4 ∂rationalLaw)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
      _ = _ := ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ by positivity))
  simpa only [integral_div,rational_increment_fourth_moment] using ht

end PerronWright.BrownianGaussianMoments
