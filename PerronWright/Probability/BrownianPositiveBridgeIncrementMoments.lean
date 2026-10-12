import PerronWright.Probability.BrownianPositiveBridgeTwoPointKernelBounds
import PerronWright.Probability.BrownianGaussianMoments

/-! # Actual uniform fourth increment moments on every interior window

Every small positive endpoint shares one finite constant, uniformly over
all interior evaluation pairs. The proof integrates the genuine two-point
conditional density against a proved Gaussian majorant and evaluates the
actual Gaussian fourth moment. No tightness or moment hypothesis is an
input. Boundary control and path-law tightness are separate next steps.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeIncrementMoments

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianPositiveBridgeGaussianBounds BrownianPositiveBridgeGaussianEnvelopeIntegrability
open BrownianPositiveBridgeTwoPointKernelBounds BrownianGaussianMoments

def fourthIncrementCoefficient (δ T : ℝ≥0) : ℝ≥0∞ :=
  interiorCoefficient δ T*envelopeMass δ T*ENNReal.ofReal fourthMomentConstant

theorem fourthIncrementCoefficient_ne_top (δ T : ℝ≥0) (hT : 0 < T) :
    fourthIncrementCoefficient δ T ≠ ∞ := by
  have hp : gaussianPDF 0 T 0 ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (gaussianPDFReal_pos 0 T 0 (ne_of_gt hT))
  have hc : interiorCoefficient δ T ≠ ∞ := by
    unfold interiorCoefficient
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hp) ENNReal.ofReal_ne_top
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hc (envelopeMass_lt_top δ T hT).ne) ENNReal.ofReal_ne_top

theorem lintegral_freeVector_two {F : FreeVector 2 → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ x : ℝ, ∫⁻ y : ℝ, F ![x,y] := by
  rw [lintegral_volume_freeAppend 1 hF]
  have hm : Measurable (fun v : FreeVector 1 ↦ ∫⁻ y : ℝ, F (freeAppend 1 (v,y))) :=
    (hF.comp (continuous_freeAppend 1).measurable).lintegral_prod_right'
  rw [lintegral_volume_freeAppend 0 hm,Measure.volume_pi_eq_dirac,lintegral_dirac]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  congr 1
  funext i
  fin_cases i <;> rfl

theorem actual_twoPoint_lintegral (a : ℝ) (ha : 0 < a) (s h t : ℝ≥0)
    (hs : 0 < s) (hh : 0 < h) (ht : 0 < t) (Φ : ℝ×ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g, Φ (g s,g (s+h)) ∂positiveBridgeLaw a (s+h+t)) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, twoPointDensity a s h t x y*Φ (x,y) := by
  have hp : Measurable (fun v : FreeVector 2 ↦ (v 0,v 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hprev : ∀ j < 2, 0 < twoPointGaps s h t j := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simpa [twoPointGaps] using hs
    · simpa [twoPointGaps] using hh
  have hgap : 0 < twoPointGaps s h t 2 := by simpa [twoPointGaps] using ht
  have he := multiPoint_lintegral 2 a ha (twoPointGaps s h t) hprev hgap
    (fun v ↦ Φ (v 0,v 1)) (hΦ.comp hp)
  change (∫⁻ g, Φ ((internalEval 2 (twoPointGaps s h t) g) 0,
      (internalEval 2 (twoPointGaps s h t) g) 1) ∂positiveBridgeLaw a (sampleTime (twoPointGaps s h t) 3)) = _ at he
  rw [sampleTime_twoPointGaps] at he
  simp [internalEval_twoPointGaps] at he
  have hm : Measurable (fun v : FreeVector 2 ↦ multiDensity 2 a (twoPointGaps s h t) v*Φ (v 0,v 1)) :=
    (measurable_multiDensity 2 a _).mul (hΦ.comp hp)
  rw [he,lintegral_freeVector_two hm]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  rw [multiDensity_twoPointGaps]
  rfl

theorem gaussian_centered_fourth_lintegral (x : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (‖y-x‖^4)) =
      ENNReal.ofReal ((h : ℝ)^2)*ENNReal.ofReal fourthMomentConstant := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (‖z‖^4)) := by fun_prop
  have hsub : Measurable (fun z : ℝ ↦ z-x) := by fun_prop
  have hl := lintegral_map hm hsub (μ := gaussianReal x h)
  rw [gaussianReal_map_sub_const,sub_self] at hl
  have hφ : Measurable (fun y : ℝ ↦ ENNReal.ofReal (‖y-x‖^4)) := by fun_prop
  have he : (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (‖y-x‖^4)) =
      ∫⁻ y : ℝ, ENNReal.ofReal (‖y-x‖^4) ∂gaussianReal x h := by
    rw [gaussianReal_of_var_ne_zero x (ne_of_gt hh),
      lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF x h) hφ]
    rfl
  rw [he,← hl,← ofReal_integral_eq_lintegral_ofReal (gaussian_fourth_integrable h)
    (ae_of_all _ (fun z : ℝ ↦ pow_nonneg (norm_nonneg z) 4)),gaussian_fourth_moment,
    ENNReal.ofReal_mul (sq_nonneg (h : ℝ))]

theorem eventually_uniform_interior_fourth_increment (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (s h t : ℝ≥0), δ ≤ s → δ ≤ t → s+h+t = T →
      (∫⁻ g, ENNReal.ofReal (‖g (s+h)-g s‖^4) ∂positiveBridgeLaw a T) ≤
        fourthIncrementCoefficient δ T*ENNReal.ofReal ((h : ℝ)^2) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_twoPointDensity_bound δ T hδ hT]
    with a ha hb
  intro s h t hs ht hsum
  by_cases hh : h = 0
  · simp only [hh,add_zero,sub_self,norm_zero,zero_pow (by norm_num : (4 : ℕ) ≠ 0),
      ENNReal.ofReal_zero,lintegral_zero,NNReal.coe_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,le_refl]
  have hhpos : 0 < h := (zero_le : (0 : ℝ≥0) ≤ h).lt_of_ne (Ne.symm hh)
  have hΦ : Measurable (fun p : ℝ×ℝ ↦ ENNReal.ofReal (‖p.2-p.1‖^4)) := by fun_prop
  have hactual := actual_twoPoint_lintegral a ha s h t (hδ.trans_le hs) hhpos (hδ.trans_le ht) _ hΦ
  rw [hsum] at hactual
  rw [hactual]
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ,
        (interiorCoefficient δ T*envelope δ T x*gaussianPDF x h y)*ENNReal.ofReal (‖y-x‖^4) := by
      apply lintegral_mono
      intro x
      exact lintegral_mono (fun y ↦ mul_le_mul' (hb s h t hs ht hsum x y) le_rfl)
    _ = ∫⁻ x : ℝ, (interiorCoefficient δ T*envelope δ T x)*
        (ENNReal.ofReal ((h : ℝ)^2)*ENNReal.ofReal fourthMomentConstant) := by
      apply lintegral_congr
      intro x
      have hm : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal (‖y-x‖^4)) := by fun_prop
      have he : (∫⁻ y : ℝ, (interiorCoefficient δ T*envelope δ T x*gaussianPDF x h y)*
          ENNReal.ofReal (‖y-x‖^4)) = (interiorCoefficient δ T*envelope δ T x)*
            (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (‖y-x‖^4)) := by
        simpa only [mul_assoc] using lintegral_const_mul (interiorCoefficient δ T*envelope δ T x) hm
      rw [he,gaussian_centered_fourth_lintegral x h hhpos]
    _ = _ := by
      have hm : Measurable (fun x : ℝ ↦ interiorCoefficient δ T*envelope δ T x) :=
        measurable_const.mul (measurable_envelope δ T)
      rw [lintegral_mul_const _ hm,lintegral_const_mul _ (measurable_envelope δ T)]
      unfold fourthIncrementCoefficient envelopeMass
      ac_rfl

end PerronWright.BrownianPositiveBridgeIncrementMoments
