import PerronWright.Analysis.ScalarRadiusSecond
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.ScalarLogRadiusTaylor

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A scalar analytic germ with zero constant and linear terms has a cubic
big-O remainder after its exact quadratic Taylor term. -/
private theorem analytic_cubic_remainder {F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticAt ℂ F 1) (h0 : F 1 = 0)
    (h1 : deriv F 1 = 0) (h2 : deriv (deriv F) 1 = c) :
    (fun y : ℂ => F (1 + y) - (c / 2) * y ^ 2)
      =O[𝓝 (0 : ℂ)] (fun y : ℂ => ‖y‖ ^ 3) := by
  obtain ⟨p, hp⟩ := hF
  have hp0 : p.coeff 0 = 0 := by
    have hone : (1 : Fin 0 → ℂ) = fun _ => 1 := by funext i; simp
    rw [FormalMultilinearSeries.coeff, hone]
    simpa only [h0] using hp.coeff_zero (fun _ : Fin 0 => (1 : ℂ))
  have hp1 : p.coeff 1 = 0 := by
    have hone : (1 : Fin 1 → ℂ) = fun _ => 1 := by funext i; simp
    rw [FormalMultilinearSeries.coeff, hone]
    simpa only [h1] using hp.deriv.symm
  have hb := hp.isBigO_sub_partialSum_pow 3
  obtain ⟨r, hpr⟩ := hp
  have hfac := hpr.factorial_smul (1 : ℂ) 2
  have hp2 : p.coeff 2 = c / 2 := by
    have h2' : (iteratedFDeriv ℂ 2 F 1) (fun _ => (1 : ℂ)) = c := by
      have hh : iteratedDeriv 2 F 1 = c := by
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2
      simpa only [iteratedDeriv_eq_iteratedFDeriv] using hh
    have hh : (2 : ℂ) * p.coeff 2 = c := by
      have hone : (1 : Fin 2 → ℂ) = fun _ => 1 := by funext i; simp
      rw [FormalMultilinearSeries.coeff, hone]
      simpa only [show Nat.factorial 2 = 2 by decide,
        nsmul_eq_mul, Nat.cast_ofNat] using hfac.trans h2'
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    simpa only [mul_comm] using hh
  have hsum (y : ℂ) : p.partialSum 3 y = (c / 2) * y ^ 2 := by
    change (∑ k ∈ Finset.range 3, p k (fun _ => y)) = (c / 2) * y ^ 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, hp0, hp1, hp2,
      smul_eq_mul, mul_zero, zero_add, pow_zero, pow_one]
    ring
  simp_rw [hsum] at hb
  exact hb

/-- The principal logarithm is the local analytic branch of the actual
critical radius, normalized to vanish at `t = 1`. -/
def logScalarRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (t : ℂ) : ℂ := Complex.log (ScalarRadiusSecond.scalarRadius M hM t)

theorem logScalarRadius_analytic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (logScalarRadius M hM) 1 := by
  have hlog : AnalyticAt ℂ Complex.log (ScalarRadiusSecond.scalarRadius M hM 1) := by
    simpa only [ScalarRadiusSecond.scalarRadius_one] using
      analyticAt_clog Complex.one_mem_slitPlane
  exact hlog.comp (ScalarRadiusSecond.scalarRadius_analytic M hM)

@[simp] theorem logScalarRadius_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : logScalarRadius M hM 1 = 0 := by
  simp [logScalarRadius]

theorem logScalarRadius_deriv_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : deriv (logScalarRadius M hM) 1 = 0 := by
  have hlog : HasDerivAt Complex.log
      (ScalarRadiusSecond.scalarRadius M hM 1)⁻¹
      (ScalarRadiusSecond.scalarRadius M hM 1) := by
    simpa only [ScalarRadiusSecond.scalarRadius_one] using
      Complex.hasDerivAt_log Complex.one_mem_slitPlane
  have h := hlog.comp 1
    (ScalarRadiusSecond.scalarRadius_analytic M hM).hasStrictDerivAt.hasDerivAt
  have hd := h.deriv
  change deriv (Complex.log ∘ ScalarRadiusSecond.scalarRadius M hM) 1 = 0
  simpa only [logScalarRadius, ScalarRadiusSecond.scalarRadius_one,
    ScalarRadiusSecond.scalarRadius_deriv_one,
    inv_one, mul_zero] using hd

theorem logScalarRadius_deriv_eventually (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      deriv (logScalarRadius M hM) t =
        deriv (ScalarRadiusSecond.scalarRadius M hM) t *
          (ScalarRadiusSecond.scalarRadius M hM t)⁻¹ := by
  let R := ScalarRadiusSecond.scalarRadius M hM
  have hRlim : Filter.Tendsto R (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa only [R, ScalarRadiusSecond.scalarRadius_one] using
      (ScalarRadiusSecond.scalarRadius_analytic M hM).continuousAt.tendsto
  have hslit : ∀ᶠ t : ℂ in 𝓝 1, R t ∈ Complex.slitPlane :=
    hRlim.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  filter_upwards [hslit,
    (ScalarRadiusSecond.scalarRadius_analytic M hM).eventually_analyticAt]
    with t ht hRt
  have h := (Complex.hasDerivAt_log ht).comp t hRt.hasStrictDerivAt.hasDerivAt
  have hd := h.deriv
  change deriv (Complex.log ∘ R) t = _ at hd
  change deriv (Complex.log ∘ R) t = deriv R t * (R t)⁻¹
  simpa only [mul_comm] using hd

theorem logScalarRadius_second_deriv_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    deriv (deriv (logScalarRadius M hM)) 1 =
      (M.alpha hM : ℂ) ^ 2 / (M.beta hM : ℂ) := by
  let R := ScalarRadiusSecond.scalarRadius M hM
  have heq : deriv (logScalarRadius M hM) =ᶠ[𝓝 (1 : ℂ)]
      (fun t => deriv R t * (R t)⁻¹) := logScalarRadius_deriv_eventually M hM
  have hd := heq.deriv_eq (𝕜 := ℂ)
  have hR' := (ScalarRadiusSecond.scalarRadius_analytic M hM).deriv.hasStrictDerivAt.hasDerivAt
  have hR := (ScalarRadiusSecond.scalarRadius_analytic M hM).hasStrictDerivAt.hasDerivAt
  have hinv := hR.inv (by simp [R] : R 1 ≠ 0)
  have hp := hR'.mul hinv
  change deriv (deriv (logScalarRadius M hM)) 1 =
    deriv (deriv R * R⁻¹) 1 at hd
  rw [hp.deriv] at hd
  rw [ScalarRadiusSecond.scalarRadius_one,
    ScalarRadiusSecond.scalarRadius_deriv_one,
    ScalarRadiusSecond.scalarRadius_second_deriv_one] at hd
  simpa only [Pi.inv_apply, R, ScalarRadiusSecond.scalarRadius_one,
    inv_one, mul_one, zero_mul, add_zero] using hd

/-- Third-order local Taylor estimate for the logarithm of the actual
analytic critical radius. The error is uniform in a complex neighborhood
of the scalar parameter `t = 1`. -/
theorem logScalarRadius_cubic_remainder (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    (fun y : ℂ => logScalarRadius M hM (1 + y) -
      ((M.alpha hM : ℂ) ^ 2 / (2 * (M.beta hM : ℂ))) * y ^ 2)
      =O[𝓝 (0 : ℂ)] (fun y : ℂ => ‖y‖ ^ 3) := by
  have h := analytic_cubic_remainder
    (logScalarRadius_analytic M hM)
    (logScalarRadius_one M hM)
    (logScalarRadius_deriv_one M hM)
    (logScalarRadius_second_deriv_one M hM)
  have hb : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  have hcoef : ((M.alpha hM : ℂ) ^ 2 / (M.beta hM : ℂ)) / 2 =
      (M.alpha hM : ℂ) ^ 2 / (2 * (M.beta hM : ℂ)) := by
    field_simp
  simpa only [hcoef] using h

/-- On the real slice near one, the chosen principal complex logarithm
agrees exactly with the ordinary real logarithm of the positive radius. -/
theorem logScalarRadius_real_branch (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ t : ℝ in 𝓝 1,
      logScalarRadius M hM (t : ℂ) =
        ((Real.log ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re)) : ℂ) := by
  filter_upwards [ScalarFieldResponse.scalarCriticalRadius_real_positive_near_one M hM]
    with t ht
  change (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).im = 0 ∧
    0 < (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re at ht
  have hz : ScalarRadiusSecond.scalarRadius M hM (t : ℂ) =
      ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using ht.1
  simp only [logScalarRadius, ScalarRadiusSecond.scalarRadius] at hz ⊢
  rw [hz]
  exact (Complex.ofReal_log ht.2.le).symm

end PerronWright.ScalarLogRadiusTaylor
