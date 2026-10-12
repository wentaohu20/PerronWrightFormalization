import PerronWright.Probability.BrownianPositiveBridgeTwoPointKernelBounds

/-! # Uniform linear exit bound for the actual positive bridge

The entrance density is retained literally rather than replaced by an
interior envelope. Consequently the bound has no positive lower bound
on the entrance time. These are bounds on the actual conditioned bridge
density; no tightness or positive-excursion identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeBoundaryKernelBounds

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianPositiveBridgeTwoPointKernelBounds

def exitCoefficient (δ : ℝ≥0) : ℝ :=
  (2/(δ : ℝ))*(Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹

def boundaryCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0*ENNReal.ofReal (exitCoefficient δ)

theorem exitCoefficient_nonneg (δ : ℝ≥0) : 0 ≤ exitCoefficient δ := by
  unfold exitCoefficient
  positivity

theorem boundaryCoefficient_ne_top (δ T : ℝ≥0) (hT : 0 < T) :
    boundaryCoefficient δ T ≠ ∞ := by
  have hp : gaussianPDF 0 T 0 ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (gaussianPDFReal_pos 0 T 0 (ne_of_gt hT))
  exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hp) ENNReal.ofReal_ne_top

theorem normalized_density_le_linear_exit (a : ℝ) (ha : 0 < a) (δ t : ℝ≥0)
    (hδ : 0 < δ) (hδt : δ ≤ t) (y : ℝ) :
    density a t y/ENNReal.ofReal a ≤ ENNReal.ofReal (exitCoefficient δ)*ENNReal.ofReal y := by
  have ht : 0 < t := hδ.trans_le hδt
  have hδR : (0 : ℝ) < δ := hδ
  have hδtR : (δ : ℝ) ≤ t := hδt
  by_cases hy : 0 < y
  · have hp := densityReal_div_start_le a ha t ht y hy
    have hq : 2*y/(t : ℝ) ≤ 2*y/(δ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hδR hδtR
    have hroot : 0 < Real.sqrt (2*Real.pi*(δ : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt (2*Real.pi*(δ : ℝ)) ≤ Real.sqrt (2*Real.pi*(t : ℝ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hδtR (by positivity))
    have hi : (Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹ ≤
        (Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hroot hs
    have hb : densityReal a t y/a ≤ exitCoefficient δ*y := hp.trans
      ((mul_le_mul hq hi (by positivity) (by positivity)).trans_eq (by unfold exitCoefficient; ring))
    rw [density,← ENNReal.ofReal_div_of_pos ha]
    simpa only [ENNReal.ofReal_mul (exitCoefficient_nonneg δ)] using ENNReal.ofReal_le_ofReal hb
  · simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hy,ENNReal.ofReal_zero,ENNReal.zero_div]
    exact zero_le

theorem exit_density_le_linear (a : ℝ) (ha : 0 < a) (δ t : ℝ≥0)
    (hδ : 0 < δ) (hδt : δ ≤ t) (y : ℝ) :
    density y t a ≤ ENNReal.ofReal a*ENNReal.ofReal (exitCoefficient δ)*ENNReal.ofReal y := by
  rw [density_symm y a t (hδ.trans_le hδt)]
  have hb := normalized_density_le_linear_exit a ha δ t hδ hδt y
  have he := (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top).mp hb
  simpa only [mul_assoc,mul_comm,mul_left_comm] using he

theorem eventually_uniform_boundary_twoPointDensity_bound (δ T : ℝ≥0)
    (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), δ ≤ t → s+h+t = T →
      ∀ x y : ℝ, twoPointDensity a s h t x y ≤
        boundaryCoefficient δ T*(density a s x/ENNReal.ofReal a)*
          gaussianPDF x h y*ENNReal.ofReal y := by
  filter_upwards [self_mem_nhdsWithin,eventually_normalization_sq_ratio_bound T hT] with a ha hratio
  intro s h t ht hsum x y
  have hb3 := exit_density_le_linear a ha δ t hδ ht y
  have he : density a s x = (density a s x/ENNReal.ofReal a)*ENNReal.ofReal a :=
    (ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top).symm
  unfold twoPointDensity
  rw [hsum]
  calc
    _ ≤ (normalization a T)⁻¹*((density a s x)*gaussianPDF x h y*
        (ENNReal.ofReal a*ENNReal.ofReal (exitCoefficient δ)*ENNReal.ofReal y))/gaussianPDF 0 T 0 :=
      ENNReal.div_le_div_right (mul_le_mul' le_rfl (mul_le_mul'
        (mul_le_mul' le_rfl (density_le_gaussian x y h)) hb3)) _
    _ = ((normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a))/gaussianPDF 0 T 0*
        ENNReal.ofReal (exitCoefficient δ)*(density a s x/ENNReal.ofReal a)*
          gaussianPDF x h y*ENNReal.ofReal y := by
      conv_lhs => rw [he]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
        (ENNReal.div_le_div_right hratio _) le_rfl) le_rfl) le_rfl) le_rfl

end PerronWright.BrownianPositiveBridgeBoundaryKernelBounds
