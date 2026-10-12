import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalEntrance

/-! # Actual small-positive-endpoint bridge window tests

Every bounded Borel one-point test supported on a fixed bounded positive
window has the entrance--exit density limit. The bound is proved from the
actual Gaussian difference kernels and their quadratic normalization.
No convergence, uniform-integrability or excursion-law interface is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalTests

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance

def windowBound (s t : ℝ≥0) (b : ℝ) : ℝ :=
  (((2*b/(s : ℝ))*(Real.sqrt (2*Real.pi*(s : ℝ)))⁻¹)*
    ((2*b/(t : ℝ))*(Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹))/
      (((s+t : ℝ≥0) : ℝ)⁻¹*gaussianPDFReal 0 (s+t) 0)

theorem eventually_onePointDensity_window_bound (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x ∈ Icc 0 b,
      onePointDensity a s t x ≤ ENNReal.ofReal (windowBound s t b) := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hTR : (0 : ℝ) < s+t := hT
  have hp := gaussianPDFReal_pos 0 (s+t) 0 (ne_of_gt hT)
  have hlow : ((s+t : ℝ≥0) : ℝ)⁻¹ < 2/((s+t : ℝ≥0) : ℝ) := by
    have hi : (0 : ℝ) < ((s+t : ℝ≥0) : ℝ)⁻¹ := inv_pos.mpr hTR
    rw [div_eq_mul_inv]
    linarith
  filter_upwards [self_mem_nhdsWithin,
    (normalization_div_sq_tendsto (s+t) hT).eventually_const_lt hlow] with a ha hn
  intro x hx
  rw [onePointDensity_eq_scaled a ha s t hs ht x]
  apply ENNReal.ofReal_le_ofReal
  have hsa := div_nonneg (densityReal_nonneg a ha s hs x) ha.le
  have hta := div_nonneg (densityReal_nonneg a ha t ht x) ha.le
  have hsb := densityReal_div_start_le_window a ha s hs b x hb hx.2
  have htb := densityReal_div_start_le_window a ha t ht b x hb hx.2
  have hprod := mul_le_mul hsb htb hta (by positivity)
  have hdenlow : 0 < ((s+t : ℝ≥0) : ℝ)⁻¹*gaussianPDFReal 0 (s+t) 0 := mul_pos (inv_pos.mpr hTR) hp
  have hden : ((s+t : ℝ≥0) : ℝ)⁻¹*gaussianPDFReal 0 (s+t) 0 ≤
      ((1-Real.exp (-2*a^2/(s+t : ℝ≥0)))/a^2)*gaussianPDFReal 0 (s+t) 0 :=
    mul_le_mul_of_nonneg_right hn.le hp.le
  unfold scaledDensityReal windowBound
  exact (div_le_div_of_nonneg_left (mul_nonneg hsa hta) hdenlow hden).trans
    (div_le_div_of_nonneg_right hprod hdenlow.le)

theorem actual_onePoint_bounded_window_test_tendsto (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (b C : ℝ) (hb : 0 ≤ b) (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ x, Ψ x ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, (Icc 0 b).indicator Ψ (g s) ∂positiveBridgeLaw a (s+t))
      (𝓝[>] 0) (𝓝 (∫⁻ x in Icc 0 b, entranceExit s t x*Ψ x)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 b)
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (Icc (0 : ℝ) b)) univ < ∞
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let D : ℝ≥0∞ := ENNReal.ofReal (windowBound s t b)*ENNReal.ofReal C
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (fun x ↦ onePointDensity a s t x*Ψ x) :=
    Eventually.of_forall (fun a ↦ (measurable_onePointDensity a s t).mul hΨ)
  have hbd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ x ∂μ, onePointDensity a s t x*Ψ x ≤ D := by
    filter_upwards [eventually_onePointDensity_window_bound s t hs ht b hb] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_le_mul' (ha x hx) (hbound x)
  have hfin : (∫⁻ _x, D ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (measure_ne_top μ univ)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun a : ℝ ↦ onePointDensity a s t x*Ψ x)
      (𝓝[>] 0) (𝓝 (entranceExit s t x*Ψ x)) := Eventually.of_forall (fun x ↦
    ENNReal.Tendsto.mul_const (onePointDensity_tendsto s t hs ht x)
      (Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound x))))
  have he := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _x ↦ D) hm hbd hfin hlim
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [onePoint_lintegral a ha s t hs ht ((Icc 0 b).indicator Ψ) (hΨ.indicator measurableSet_Icc)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Icc 0 b
  · rw [indicator_of_mem hx,indicator_of_mem hx]
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero]

theorem actual_onePoint_window_probability_tendsto (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun a : ℝ ↦ positiveBridgeLaw a (s+t) ((fun g ↦ g s) ⁻¹' Icc 0 b))
      (𝓝[>] 0) (𝓝 (∫⁻ x in Icc 0 b, entranceExit s t x)) := by
  have he := actual_onePoint_bounded_window_test_tendsto s t hs ht b 1 hb (fun _ ↦ 1)
    measurable_const (fun _ ↦ by simp)
  have hI : (fun g : BrownianPathLaw.Path ↦ (Icc 0 b).indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞)) (g s)) =
      ((fun g : BrownianPathLaw.Path ↦ g s) ⁻¹' Icc 0 b).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext g
    by_cases hg : g s ∈ Icc 0 b <;> simp only [Set.indicator,mem_preimage,hg,if_true,if_false]
  simp only [mul_one,hI] at he
  apply he.congr
  intro a
  exact lintegral_indicator_one ((BrownianPathLaw.continuous_eval s).measurable measurableSet_Icc)

end PerronWright.BrownianPositiveBridgeFiniteDimensionalTests
