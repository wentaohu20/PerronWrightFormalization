import PerronWright.Probability.WeakContinuousMomentIdentification

/-! # Genuine integral convergence from a proved uniform square bound

Continuous truncations and the explicit quadratic remainder prove the
transfer. Uniform integrability is a conclusion of the estimates, not an
additional premise beyond the displayed actual second-integral bound.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.WeakContinuousSquareIntegralTransfer

open WeakContinuousMomentIdentification

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem square_integrable (ρ : ProbabilityMeasure X) (h : X → ℝ) (hc : Continuous h)
    (C : ℝ) (hsquare : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
    Integrable (fun x ↦ h x^2) (ρ:Measure X) := by
  refine ⟨(hc.pow 2).measurable.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ sq_nonneg _))).mpr
  exact lt_of_le_of_lt hsquare ENNReal.ofReal_lt_top

private theorem integrable_of_square_bound (ρ : ProbabilityMeasure X) (h : X → ℝ)
    (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ)
    (hsquare : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
    Integrable h (ρ:Measure X) := by
  have hi := (integrable_const (1:ℝ)).add (square_integrable ρ h hc C hsquare)
  apply hi.mono' hc.measurable.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]
  change h x ≤ 1+h x^2
  nlinarith [sq_nonneg (h x-1/2)]

private theorem real_square_integral_le (ρ : ProbabilityMeasure X) (h : X → ℝ)
    (hc : Continuous h) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
    (∫ x, h x^2 ∂(ρ:Measure X)) ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ sq_nonneg _))
    (hc.pow 2).measurable.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hsquare).trans_eq (ENNReal.toReal_ofReal hC)

private theorem integral_truncation_error_le (ρ : ProbabilityMeasure X) (h : X → ℝ)
    (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C)
    (B : ℝ) (hB : 0 < B) :
    |(∫ x, h x ∂(ρ:Measure X))-
      (∫ x, truncateTest h hc h0 B hB.le x ∂(ρ:Measure X))| ≤ C/B := by
  let Ψ := truncateTest h hc h0 B hB.le
  have hi := integrable_of_square_bound ρ h hc h0 C hsquare
  have hi2 := square_integrable ρ h hc C hsquare
  have hΨ : Integrable (fun x ↦ Ψ x) (ρ:Measure X) := Ψ.integrable _
  have hlo : (∫ x, Ψ x ∂(ρ:Measure X)) ≤ ∫ x, h x ∂(ρ:Measure X) :=
    integral_mono hΨ hi (fun x ↦ min_le_left _ _)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  calc
    _ = ∫ x, h x-Ψ x ∂(ρ:Measure X) := (integral_sub hi hΨ).symm
    _ ≤ ∫ x, (1/B)*h x^2 ∂(ρ:Measure X) :=
      integral_mono (hi.sub hΨ) (hi2.const_mul _) (fun x ↦ by
        change h x-min (h x) B ≤ (1/B)*h x^2
        have ht := nonnegative_le_truncate_add_square (h x) B (h0 x) hB
        linarith)
    _ = (1/B)*(∫ x, h x^2 ∂(ρ:Measure X)) := integral_const_mul _ _
    _ ≤ (1/B)*C := mul_le_mul_of_nonneg_left (real_square_integral_le ρ h hc C hC hsquare)
      (by positivity)
    _ = C/B := by ring

theorem tendsto_integral_nonnegative_of_uniform_square_bound
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : ∀ᶠ i in L,
      (∫⁻ x, ENNReal.ofReal (h x^2) ∂(μ i:Measure X)) ≤ ENNReal.ofReal C) :
    Tendsto (fun i ↦ ∫ x, h x ∂(μ i:Measure X)) L (𝓝 (∫ x, h x ∂(ν:Measure X))) := by
  have ht : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ν:Measure X)) ≤ ENNReal.ofReal C :=
    target_lintegral_le_of_eventual_bound μ ν hweak (fun x ↦ h x^2) (hc.pow 2)
      (fun _ ↦ sq_nonneg _) _ hsquare
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := 6*C/ε+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hratio : C/B < ε/3 := by
    apply (div_lt_iff₀ hB).mpr
    have he : (ε/3)*B = 2*C+ε/3 := by
      dsimp [B]
      field_simp
      ring
    rw [he]
    linarith
  have he := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    (truncateTest h hc h0 B hB.le)
  have hcentral := (Metric.tendsto_nhds.mp he) (ε/3) (by positivity)
  filter_upwards [hsquare,hcentral] with i hi hm
  rw [Real.dist_eq] at hm ⊢
  have hs := integral_truncation_error_le (μ i) h hc h0 C hC hi B hB
  have hv := integral_truncation_error_le ν h hc h0 C hC ht B hB
  have htriangle := abs_sub_le (∫ x, h x ∂(μ i:Measure X))
    (∫ x, truncateTest h hc h0 B hB.le x ∂(μ i:Measure X))
    (∫ x, h x ∂(ν:Measure X))
  have htriangle2 := abs_sub_le
    (∫ x, truncateTest h hc h0 B hB.le x ∂(μ i:Measure X))
    (∫ x, truncateTest h hc h0 B hB.le x ∂(ν:Measure X))
    (∫ x, h x ∂(ν:Measure X))
  rw [abs_sub_comm (∫ x, truncateTest h hc h0 B hB.le x ∂(ν:Measure X))] at htriangle2
  nlinarith

private theorem positive_part_square_le (x : ℝ) : (max x 0)^2 ≤ x^2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · simpa only [max_eq_right (le_of_not_ge hx),pow_two,zero_mul] using sq_nonneg x

theorem tendsto_integral_of_uniform_square_bound
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (hweak : Tendsto μ L (𝓝 ν))
    (h : X → ℝ) (hc : Continuous h) (C : ℝ) (hC : 0 ≤ C)
    (hsquare : ∀ᶠ i in L,
      (∫⁻ x, ENNReal.ofReal (h x^2) ∂(μ i:Measure X)) ≤ ENNReal.ofReal C) :
    Tendsto (fun i ↦ ∫ x, h x ∂(μ i:Measure X)) L (𝓝 (∫ x, h x ∂(ν:Measure X))) := by
  let hp : X → ℝ := fun x ↦ max (h x) 0
  let hn : X → ℝ := fun x ↦ max (-h x) 0
  have hpc : Continuous hp := hc.max continuous_const
  have hnc : Continuous hn := hc.neg.max continuous_const
  have hp0 : ∀ x, 0 ≤ hp x := fun _ ↦ le_max_right _ _
  have hn0 : ∀ x, 0 ≤ hn x := fun _ ↦ le_max_right _ _
  have hplus (ρ : ProbabilityMeasure X)
      (hs : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
      (∫⁻ x, ENNReal.ofReal (hp x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C :=
    (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (positive_part_square_le (h x)))).trans hs
  have hminus (ρ : ProbabilityMeasure X)
      (hs : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
      (∫⁻ x, ENNReal.ofReal (hn x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C := by
    apply le_trans (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (positive_part_square_le (-h x))))
    simpa only [neg_sq] using hs
  have hdiff (ρ : ProbabilityMeasure X)
      (hs : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ρ:Measure X)) ≤ ENNReal.ofReal C) :
      (∫ x, h x ∂(ρ:Measure X)) =
        (∫ x, hp x ∂(ρ:Measure X))-(∫ x, hn x ∂(ρ:Measure X)) := by
    rw [← integral_sub (integrable_of_square_bound ρ hp hpc hp0 C (hplus ρ hs))
      (integrable_of_square_bound ρ hn hnc hn0 C (hminus ρ hs))]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp [hp,hn]
    by_cases hx : 0 ≤ h x
    · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right (le_of_not_ge hx),max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring
  have ht : (∫⁻ x, ENNReal.ofReal (h x^2) ∂(ν:Measure X)) ≤ ENNReal.ofReal C :=
    target_lintegral_le_of_eventual_bound μ ν hweak (fun x ↦ h x^2) (hc.pow 2)
      (fun _ ↦ sq_nonneg _) _ hsquare
  rw [hdiff ν ht]
  apply ((tendsto_integral_nonnegative_of_uniform_square_bound μ ν hweak hp hpc hp0 C hC
    (hsquare.mono (fun i hi ↦ hplus (μ i) hi))).sub
      (tendsto_integral_nonnegative_of_uniform_square_bound μ ν hweak hn hnc hn0 C hC
        (hsquare.mono (fun i hi ↦ hminus (μ i) hi)))).congr'
  exact hsquare.mono (fun i hi ↦ (hdiff (μ i) hi).symm)

end PerronWright.WeakContinuousSquareIntegralTransfer
