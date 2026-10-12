import PerronWright.Probability.BrownianKilledCenteredEntranceMoments

/-! # Actual fourth moments centered at the bridge boundary

The common bound includes time zero and every observation time with a
remaining interval bounded below. It is centered at the actual endpoint
`a`, not at a hypothesized excursion endpoint or candidate limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeBoundaryCenteredMoments

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeTwoPointKernelBounds
open BrownianPositiveBridgeBoundaryKernelBounds BrownianKilledCenteredEntranceMoments

def centeredBoundaryCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  boundaryCoefficient δ T*ENNReal.ofReal entranceFourthCoefficient

theorem centeredBoundaryCoefficient_ne_top (δ T : ℝ≥0) (hT : 0 < T) :
    centeredBoundaryCoefficient δ T ≠ ∞ :=
  ENNReal.mul_ne_top (boundaryCoefficient_ne_top δ T hT) ENNReal.ofReal_ne_top

theorem eventually_uniform_boundary_onePointDensity_bound (δ T : ℝ≥0)
    (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s t : ℝ≥0), δ ≤ t → s+t = T → ∀ y : ℝ,
      onePointDensity a s t y ≤ boundaryCoefficient δ T*(density a s y/ENNReal.ofReal a)*ENNReal.ofReal y := by
  filter_upwards [self_mem_nhdsWithin,eventually_normalization_sq_ratio_bound T hT] with a ha hratio
  intro s t ht hsum y
  have hb := exit_density_le_linear a ha δ t hδ ht y
  have he : density a s y = (density a s y/ENNReal.ofReal a)*ENNReal.ofReal a :=
    (ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top).symm
  unfold onePointDensity
  rw [hsum]
  calc
    _ ≤ (normalization a T)⁻¹*(density a s y*(ENNReal.ofReal a*ENNReal.ofReal (exitCoefficient δ)*ENNReal.ofReal y))/gaussianPDF 0 T 0 :=
      ENNReal.div_le_div_right (mul_le_mul' le_rfl (mul_le_mul' le_rfl hb)) _
    _ = ((normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a))/gaussianPDF 0 T 0*
        ENNReal.ofReal (exitCoefficient δ)*(density a s y/ENNReal.ofReal a)*ENNReal.ofReal y := by
      conv_lhs => rw [he]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' (mul_le_mul' (ENNReal.div_le_div_right hratio _) le_rfl) le_rfl) le_rfl

theorem eventually_uniform_boundary_centered_fourth (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s t : ℝ≥0), δ ≤ t → s+t = T →
      (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a T) ≤
        centeredBoundaryCoefficient δ T*ENNReal.ofReal ((s : ℝ)^2) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_boundary_onePointDensity_bound δ T hδ hT]
    with a ha hb
  intro s t ht hsum
  by_cases hs : s = 0
  · have he : (∫⁻ g, ENNReal.ofReal (‖g s-a‖^4) ∂positiveBridgeLaw a T) = 0 := by
      calc
        _ = ∫⁻ _ : Path, (0 : ℝ≥0∞) ∂positiveBridgeLaw a T := by
          apply lintegral_congr_ae
          filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
          simp only [hs,hg.1,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),ENNReal.ofReal_zero]
        _ = 0 := lintegral_zero
    rw [he,hs]
    exact zero_le
  have hspos : 0 < s := (zero_le : (0 : ℝ≥0) ≤ s).lt_of_ne (Ne.symm hs)
  have hΦ : Measurable (fun y : ℝ ↦ ENNReal.ofReal (‖y-a‖^4)) := by fun_prop
  have hactual := onePoint_lintegral a ha s t hspos (hδ.trans_le ht) _ hΦ
  rw [hsum] at hactual
  rw [hactual]
  have hm : Measurable (fun y : ℝ ↦ (density a s y/ENNReal.ofReal a)*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4)) :=
    ((measurable_density a s).div_const _ |>.mul measurable_id.ennreal_ofReal).mul (by fun_prop)
  calc
    _ ≤ ∫⁻ y : ℝ, (boundaryCoefficient δ T*(density a s y/ENNReal.ofReal a)*ENNReal.ofReal y)*ENNReal.ofReal (|y-a|^4) := by
      apply lintegral_mono
      intro y
      simpa only [Real.norm_eq_abs] using mul_le_mul' (hb s t ht hsum y) (le_refl (ENNReal.ofReal (|y-a|^4)))
    _ = boundaryCoefficient δ T*(∫⁻ y : ℝ, (density a s y/ENNReal.ofReal a)*ENNReal.ofReal y*ENNReal.ofReal (|y-a|^4)) := by
      simpa only [mul_assoc] using lintegral_const_mul (boundaryCoefficient δ T) hm
    _ ≤ boundaryCoefficient δ T*ENNReal.ofReal ((s : ℝ)^2*entranceFourthCoefficient) :=
      mul_le_mul' le_rfl (normalized_entrance_centered_fourth_bound a ha s hspos)
    _ = _ := by
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      unfold centeredBoundaryCoefficient
      ac_rfl

end PerronWright.BrownianPositiveBridgeBoundaryCenteredMoments
