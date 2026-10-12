import PerronWright.Probability.BrownianKilledDensityConvolution
import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds

/-! # Genuine boundary entrance convolution

The actual finite killed endpoint law supplies the integration measure.
The proved uniform Gaussian bound is bounded on the whole state space,
so dominated convergence differentiates the genuine killed convolution
at the absorbing boundary. No entrance semigroup is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceConvolution

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalEntrance BrownianPositiveBridgeGaussianBounds
open BrownianKilledDensityConvolution
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFiniteDimensionalDensity

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem normalized_density_tendsto (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    Tendsto (fun a : ℝ ↦ density a T y/ENNReal.ofReal a) (𝓝[>] 0) (𝓝 (entrance T y)) := by
  apply (density_div_start_tendsto T hT y).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact ENNReal.ofReal_div_of_pos ha

theorem entrance_last_integral (x : ℝ) (s t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ y, entrance t y ∂law x s) = entrance (s+t) x := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  let D : ℝ≥0∞ := ENNReal.ofReal (envelopeSup t t)
  have hid : Tendsto (fun a : ℝ ↦ a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (fun y ↦ density a t y/ENNReal.ofReal a) :=
    Eventually.of_forall (fun a ↦ (measurable_density a t).div_const _)
  have hbd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ y ∂law x s, density a t y/ENNReal.ofReal a ≤ D := by
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with a ha ha1
    exact Eventually.of_forall (fun y ↦
      (normalized_density_le_envelope a ha ha1.le t t t ht le_rfl le_rfl y).trans
        (envelope_le_sup t t ht y))
  have hfin : (∫⁻ _y, D ∂law x s) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ univ)
  have hlim : ∀ᵐ y ∂law x s, Tendsto (fun a : ℝ ↦ density a t y/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (entrance t y)) := Eventually.of_forall (normalized_density_tendsto t ht)
  have hdct := tendsto_lintegral_filter_of_dominated_convergence (μ := law x s) (fun _y ↦ D) hm hbd hfin hlim
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ y, density a t y/ENNReal.ofReal a ∂law x s) = density a (s+t) x/ENNReal.ofReal a := by
    apply Eventually.of_forall
    intro a
    simp_rw [density_symm a _ t ht]
    have hf : Measurable (fun y : ℝ ↦ density y t a) := by
      have hp : Measurable (fun y : ℝ ↦ (y,a)) := measurable_id.prodMk measurable_const
      simpa only [Function.comp_def] using (measurable_joint_density t).comp hp
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const _ hf,density_last_integral x s t ht,density_symm x a (s+t) hT]
  exact tendsto_nhds_unique (hdct.congr' he) (normalized_density_tendsto (s+t) hT x)

theorem entrance_convolution (x : ℝ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ y, density x s y*entrance t y) = entrance (s+t) x := by
  rw [← entrance_last_integral x s t ht,law_eq_withDensity_all x s hs,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density x s) (measurable_entrance t)]
  rfl

theorem entrance_convolution_reversed (x : ℝ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ y, entrance t y*density y s x) = entrance (s+t) x := by
  simp_rw [density_symm _ x s hs,mul_comm (entrance t _)]
  exact entrance_convolution x s t hs ht

theorem jointDensity_entrance_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) :
    (∫⁻ v : FreeVector n, jointDensity n a gaps v*entrance (gaps n) (lastState n a v)) =
      entrance (sampleTime gaps (n+1)) a := by
  have he := measurable_entrance (gaps n)
  have hv : Measurable (fun v : FreeVector n ↦ entrance (gaps n) (lastState n a v)) := by
    simpa only [Function.comp_def] using he.comp (continuous_lastState n a).measurable
  calc
    _ = ∫⁻ v, entrance (gaps n) (lastState n a v) ∂volume.withDensity (jointDensity n a gaps) := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul volume (measurable_jointDensity n a gaps) hv).symm
    _ = ∫⁻ v, entrance (gaps n) (lastState n a v) ∂freeTupleLaw a gaps n := by
      rw [freeTupleLaw_eq_withDensity n a ha gaps (fun j hj ↦ hgaps j (Nat.lt_succ_of_lt hj))]
    _ = ∫⁻ x, entrance (gaps n) x ∂law a (sampleTime gaps n) := by
      rw [← freeTupleLaw_last_marginal a gaps n,lintegral_map he (continuous_lastState n a).measurable]
    _ = _ := by rw [entrance_last_integral a _ _ (hgaps n (Nat.lt_succ_self n)),sampleTime_succ]

end PerronWright.BrownianEntranceConvolution
