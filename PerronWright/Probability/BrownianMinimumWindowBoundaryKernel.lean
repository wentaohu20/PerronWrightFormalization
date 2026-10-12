import PerronWright.Probability.BrownianKilledBoundaryEntrance

/-! # Boundary kernel for an actual minimum-depth window

The terminal coordinate shifts with the lower barrier. This proves its
true small-window limit and a Gaussian bound before any interchange of
level, time or path limits is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumWindowBoundaryKernel

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance

theorem shifted_gaussian_difference_hasDerivAt_zero (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    HasDerivAt (fun δ : ℝ ↦ gaussianPDFReal 0 T y-gaussianPDFReal (-2*δ) T y)
      (2*y/(T : ℝ)*gaussianPDFReal 0 T y) 0 := by
  have hg := (gaussianPDFReal_mean_hasDerivAt T hT y (-2*0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul (-2))
  apply ((hasDerivAt_const (0 : ℝ) (gaussianPDFReal 0 T y)).sub hg).congr_deriv
  simp only [mul_zero,sub_zero]
  ring

theorem shifted_densityReal_eq (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (y : ℝ) (hy : 0 ≤ y) :
    densityReal δ T (y+δ) = gaussianPDFReal 0 T y-gaussianPDFReal (-2*δ) T y := by
  rw [densityReal,indicator_of_mem (show y+δ ∈ Ioi (0 : ℝ) from by
    exact add_pos_of_nonneg_of_pos hy hδ),gaussianPDFReal_add,gaussianPDFReal_add,
    sub_self,show -δ-δ = -2*δ by ring]

theorem shifted_densityReal_div_start_tendsto (T : ℝ≥0) (hT : 0 < T)
    (y : ℝ) (hy : 0 < y) :
    Tendsto (fun δ ↦ densityReal δ T (y+δ)/δ) (𝓝[>] (0 : ℝ)) (𝓝 (entranceReal T y)) := by
  have hg := (shifted_gaussian_difference_hasDerivAt_zero T hT y).tendsto_slope_zero_right
  have he : (fun δ : ℝ ↦ densityReal δ T (y+δ)/δ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ ↦ (gaussianPDFReal 0 T y-gaussianPDFReal (-2*δ) T y)/δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [shifted_densityReal_eq δ hδ T y hy.le]
  apply (show Tendsto (fun δ : ℝ ↦ (gaussianPDFReal 0 T y-gaussianPDFReal (-2*δ) T y)/δ)
    (𝓝[>] (0 : ℝ)) (𝓝 (entranceReal T y)) from by
      simpa only [entranceReal,indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),
        mul_zero,zero_mul,sub_self,zero_add,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hg).congr' he.symm

theorem shifted_density_div_start_tendsto (T : ℝ≥0) (hT : 0 < T)
    (y : ℝ) (hy : 0 < y) :
    Tendsto (fun δ ↦ ENNReal.ofReal (densityReal δ T (y+δ)/δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (entrance T y)) :=
  ENNReal.tendsto_ofReal (shifted_densityReal_div_start_tendsto T hT y hy)

theorem shifted_densityReal_div_start_le (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (y : ℝ) (hy : 0 ≤ y) :
    densityReal δ T (y+δ)/δ ≤ 2*(y+δ)/(T : ℝ)*gaussianPDFReal 0 T y := by
  apply (div_le_iff₀ hδ).mpr
  rw [densityReal_eq_factor δ T hT (y+δ) (add_pos_of_nonneg_of_pos hy hδ),
    gaussianPDFReal_add,sub_self]
  have he : 1-Real.exp (-2*δ*(y+δ)/(T : ℝ)) ≤ 2*δ*(y+δ)/(T : ℝ) := by
    have hx := Real.add_one_le_exp (-2*δ*(y+δ)/(T : ℝ))
    rw [show -2*δ*(y+δ)/(T : ℝ) = -(2*δ*(y+δ)/(T : ℝ)) by ring] at hx ⊢
    linarith
  calc
    _ ≤ gaussianPDFReal 0 T y*(2*δ*(y+δ)/(T : ℝ)) :=
      mul_le_mul_of_nonneg_left he (gaussianPDFReal_nonneg 0 T y)
    _ = _ := by ring

end PerronWright.BrownianMinimumWindowBoundaryKernel
