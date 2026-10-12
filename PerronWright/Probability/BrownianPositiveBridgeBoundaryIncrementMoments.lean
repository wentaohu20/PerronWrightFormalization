import PerronWright.Probability.BrownianPositiveBridgeBoundaryKernelBounds
import PerronWright.Probability.BrownianKilledSurvivalMoment
import PerronWright.Probability.BrownianGaussianCenteredWeightedMoments
import PerronWright.Probability.BrownianPositiveBridgeIncrementMoments

/-! # Fourth increments reaching arbitrarily close to the initial boundary

The time increment may be as small as desired and the initial observation
time has no fixed lower bound. The condition `h ≤ s` describes one genuine
geometric case; the complementary boundary-centered estimate is separate.
Every probability integral is under the actual positive conditioned bridge.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeBoundaryIncrementMoments

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianKilledHarmonicMoment BrownianKilledSurvivalMoment
open BrownianGaussianCenteredWeightedMoments BrownianPositiveBridgeBoundaryKernelBounds
open BrownianPositiveBridgeTwoPointKernelBounds BrownianPositiveBridgeIncrementMoments

def fourthBoundaryCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  boundaryCoefficient δ T*(ENNReal.ofReal (centeredCoefficient 4)+
    ENNReal.ofReal survivalCoefficient*ENNReal.ofReal (centeredCoefficient 5))

theorem fourthBoundaryCoefficient_ne_top (δ T : ℝ≥0) (hT : 0 < T) :
    fourthBoundaryCoefficient δ T ≠ ∞ :=
  ENNReal.mul_ne_top (boundaryCoefficient_ne_top δ T hT)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)

theorem normalized_entrance_gaussian_fourth_bound (a : ℝ) (ha : 0 < a)
    (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) (hhs : h ≤ s) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, (density a s x/ENNReal.ofReal a)*gaussianPDF x h y*
      ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) ≤
      (ENNReal.ofReal (centeredCoefficient 4)+ENNReal.ofReal survivalCoefficient*
        ENNReal.ofReal (centeredCoefficient 5))*ENNReal.ofReal ((h : ℝ)^2) := by
  have hpoint (x : ℝ) :
      (∫⁻ y : ℝ, (density a s x/ENNReal.ofReal a)*gaussianPDF x h y*
        ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) ≤
      (density a s x/ENNReal.ofReal a)*(ENNReal.ofReal x*centeredBound h 4+centeredBound h 5) := by
    by_cases hx : 0 ≤ x
    · have hm : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) := by fun_prop
      have he := lintegral_const_mul (μ := volume) (density a s x/ENNReal.ofReal a) hm
      simp only [mul_assoc] at he ⊢
      rw [he]
      simpa only [mul_assoc] using mul_le_mul' (le_refl (density a s x/ENNReal.ofReal a))
        (positive_weight_centered_fourth_bound x hx h hh)
    · have hx' : ¬ 0 < x := fun h ↦ hx h.le
      simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hx',ENNReal.ofReal_zero,
        ENNReal.zero_div,zero_mul,lintegral_zero,le_refl]
  have hmass : Measurable (fun x : ℝ ↦ density a s x/ENNReal.ofReal a) := (measurable_density a s).div_const _
  have hfirst : Measurable (fun x : ℝ ↦ (density a s x/ENNReal.ofReal a)*ENNReal.ofReal x) :=
    hmass.mul measurable_id.ennreal_ofReal
  have hfirstint : (∫⁻ x : ℝ, (density a s x/ENNReal.ofReal a)*ENNReal.ofReal x) = 1 := by
    simpa only [mul_comm] using normalized_density_first_moment a ha s hs
  calc
    _ ≤ ∫⁻ x : ℝ, (density a s x/ENNReal.ofReal a)*
        (ENNReal.ofReal x*centeredBound h 4+centeredBound h 5) := lintegral_mono hpoint
    _ = centeredBound h 4+(∫⁻ x : ℝ, density a s x/ENNReal.ofReal a)*centeredBound h 5 := by
      simp only [mul_add,← mul_assoc]
      rw [lintegral_add_left (hfirst.mul_const _),lintegral_mul_const _ hfirst,
        lintegral_mul_const _ hmass,hfirstint,one_mul]
    _ = ENNReal.ofReal (centeredCoefficient 4)*ENNReal.ofReal ((h : ℝ)^2)+
        ((∫⁻ x : ℝ, density a s x/ENNReal.ofReal a)*ENNReal.ofReal (Real.sqrt (h : ℝ)))*
          ENNReal.ofReal (centeredCoefficient 5)*ENNReal.ofReal ((h : ℝ)^2) := by
      rw [centeredBound_fourth,centeredBound_fifth]
      ac_rfl
    _ ≤ ENNReal.ofReal (centeredCoefficient 4)*ENNReal.ofReal ((h : ℝ)^2)+
        ENNReal.ofReal survivalCoefficient*ENNReal.ofReal (centeredCoefficient 5)*ENNReal.ofReal ((h : ℝ)^2) :=
      add_le_add le_rfl (mul_le_mul' (mul_le_mul' (normalized_density_mass_mul_sqrt_bound a ha s hs h hhs) le_rfl) le_rfl)
    _ = _ := by rw [add_mul]

theorem eventually_uniform_boundary_fourth_increment (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), 0 < s → h ≤ s → δ ≤ t → s+h+t = T →
      (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a T) ≤
        fourthBoundaryCoefficient δ T*ENNReal.ofReal ((h : ℝ)^2) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_boundary_twoPointDensity_bound δ T hδ hT]
    with a ha hb
  intro s h t hs hhs ht hsum
  by_cases hh : h = 0
  · simp only [hh,add_zero,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),
      ENNReal.ofReal_zero,lintegral_zero,NNReal.coe_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,le_refl]
  have hhpos : 0 < h := (zero_le : (0 : ℝ≥0) ≤ h).lt_of_ne (Ne.symm hh)
  have hΦ : Measurable (fun p : ℝ×ℝ ↦ ENNReal.ofReal (‖p.2-p.1‖^4)) := by fun_prop
  have hactual := actual_twoPoint_lintegral a ha s h t hs hhpos (hδ.trans_le ht) _ hΦ
  rw [hsum] at hactual
  rw [hactual]
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ,
        (boundaryCoefficient δ T*(density a s x/ENNReal.ofReal a)*gaussianPDF x h y*ENNReal.ofReal y)*
          ENNReal.ofReal (|y-x|^4) := by
      apply lintegral_mono
      intro x
      exact lintegral_mono (fun y ↦ by
        simpa only [Real.norm_eq_abs] using mul_le_mul' (hb s h t ht hsum x y) le_rfl)
    _ = boundaryCoefficient δ T*(∫⁻ x : ℝ, ∫⁻ y : ℝ,
        (density a s x/ENNReal.ofReal a)*gaussianPDF x h y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) := by
      have hm : Measurable (fun p : ℝ×ℝ ↦ (density a s p.1/ENNReal.ofReal a)*
          gaussianPDF p.1 h p.2*ENNReal.ofReal p.2*ENNReal.ofReal (|p.2-p.1|^4)) := by
        have hp : Measurable (fun p : ℝ×ℝ ↦ gaussianPDF p.1 h p.2) :=
          measurable_uncurry_gaussianPDF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
        exact (((measurable_density a s).comp measurable_fst |>.div_const _).mul hp |>.mul
          measurable_snd.ennreal_ofReal).mul ((measurable_snd.sub measurable_fst).abs.pow_const 4 |>.ennreal_ofReal)
      have hmInt : Measurable (fun x : ℝ ↦ ∫⁻ y : ℝ, (density a s x/ENNReal.ofReal a)*
          gaussianPDF x h y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) :=
        hm.lintegral_prod_right'
      calc
        _ = ∫⁻ x : ℝ, boundaryCoefficient δ T*(∫⁻ y : ℝ, (density a s x/ENNReal.ofReal a)*
            gaussianPDF x h y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) := by
          apply lintegral_congr
          intro x
          simpa only [Function.comp_def,id_eq,mul_assoc] using lintegral_const_mul (μ := volume) (boundaryCoefficient δ T)
            (hm.comp (measurable_const.prodMk measurable_id))
        _ = _ := lintegral_const_mul _ hmInt
    _ ≤ _ := by
      unfold fourthBoundaryCoefficient
      simpa only [mul_assoc] using mul_le_mul' (le_refl (boundaryCoefficient δ T))
        (normalized_entrance_gaussian_fourth_bound a ha s h hs hhpos hhs)

end PerronWright.BrownianPositiveBridgeBoundaryIncrementMoments
