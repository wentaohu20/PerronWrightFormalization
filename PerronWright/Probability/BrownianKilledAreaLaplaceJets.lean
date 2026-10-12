import PerronWright.Probability.BrownianKilledAreaLaplaceTaylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Genuine all-order one-sided jets of killed-area Laplace kernels

The coefficients are the already proved actual finite surviving moments.
The half-line little-o remainder and the genuine right derivative at zero
are consequences of the global next-moment error estimate, not assumptions
about analytic or Feynman--Kac solutions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaLaplaceJets

open BrownianKilledAreaKernel BrownianKilledAreaSemigroup
open BrownianKilledAreaMomentKernel BrownianKilledAreaLaplaceTaylor

theorem law_zero_eq_momentLaw (level : ℝ) (T : ℝ≥0) (x : ℝ) :
    law level 0 T x = momentLaw level 0 T x := by
  rw [law_zero,momentLaw_zero]

theorem law_integral_taylor_isLittleO (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) :
    (fun v : ℝ ↦ (∫ y, F y ∂law level (Real.toNNReal v) T x)-
      ∑ j ∈ Finset.range (n+1), ((-v)^j/(j.factorial : ℝ))*
        (∫ y, F y ∂momentLaw level j T x)) =o[𝓝[Ici 0] 0]
          (fun v : ℝ ↦ v^n) := by
  let D : ℝ := (∫ y, |F y| ∂momentLaw level (n+1) T x)/((n+1).factorial : ℝ)
  have hbig : IsBigOWith D (𝓝[Ici (0 : ℝ)] 0)
      (fun v : ℝ ↦ (∫ y, F y ∂law level (Real.toNNReal v) T x)-
        ∑ j ∈ Finset.range (n+1), ((-v)^j/(j.factorial : ℝ))*
          (∫ y, F y ∂momentLaw level j T x)) (fun v : ℝ ↦ v^(n+1)) := by
    rw [isBigOWith_iff]
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv0 : 0 ≤ v := hv
    have h := law_integral_taylor_bound level (Real.toNNReal v) T x n hF hC
    rw [Real.coe_toNNReal _ hv0] at h
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hv0 (n+1))]
    exact h.trans_eq (by dsimp only [D]; ring)
  exact hbig.isBigO.trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) n.lt_succ_self).mono nhdsWithin_le_nhds)

theorem law_integral_hasDerivWithinAt_zero (level : ℝ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ y, |F y| ≤ C) :
    HasDerivWithinAt (fun v : ℝ ↦ ∫ y, F y ∂law level (Real.toNNReal v) T x)
      (-(∫ y, F y ∂momentLaw level 1 T x)) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO]
  have h := law_integral_taylor_isLittleO level T x 1 hF hC
  have he : (fun v : ℝ ↦ (∫ y, F y ∂law level (Real.toNNReal v) T x)-
      ∑ j ∈ Finset.range (1+1), ((-v)^j/(j.factorial : ℝ))*
        (∫ y, F y ∂momentLaw level j T x)) =
      (fun v : ℝ ↦ (∫ y, F y ∂law level (Real.toNNReal v) T x)-
        (∫ y, F y ∂law level (Real.toNNReal 0) T x)-
          (v-0) • (-(∫ y, F y ∂momentLaw level 1 T x))) := by
    funext v
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
      Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,one_mul,
      Real.toNNReal_zero,law_zero_eq_momentLaw,sub_zero,smul_eq_mul]
    ring
  rw [he] at h
  simpa only [pow_one,sub_zero] using h

end PerronWright.BrownianKilledAreaLaplaceJets
