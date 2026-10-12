import PerronWright.Probability.BrownianBridgeSurvivalLaw

/-! # Genuine positive-start Brownian killed endpoint density

The finite measure is a literal restriction of the actual Brownian path
law to survival above -a, followed by the endpoint shift +a. The proved
actual reflection law implies its density above zero is the Gaussian
density with mean a minus the reflected density with mean -a.
No killed semigroup, Markov property or excursion law is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveKilledEndpoint

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledTransitionKernel
open BrownianBridgeSurvivalLaw BrownianKilledGaussianAlgebra

theorem measurable_endpointShift (a : ℝ) : Measurable (fun z : ℝ ↦ z+a) := by fun_prop

def law (a : ℝ) (T : ℝ≥0) : Measure ℝ :=
  (pathLaw.restrict (survival (-a) T)).map (fun f : Path ↦ f T+a)

instance law_isFinite (a : ℝ) (T : ℝ≥0) : IsFiniteMeasure (law a T) := by
  unfold law
  infer_instance

theorem law_eq_shift_killed (a : ℝ) (T : ℝ≥0) :
    law a T = (killedEndpointLaw (-a) T).map (fun z ↦ z+a) := by
  rw [killedEndpointLaw,Measure.map_map (measurable_endpointShift a) (continuous_eval T).measurable]
  rfl

theorem law_apply (a : ℝ) (T : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    law a T B = pathLaw {f | (T : ℝ≥0∞) < firstPassage (-a) f ∧ f T+a ∈ B} := by
  rw [law_eq_shift_killed,Measure.map_apply (measurable_endpointShift a) hB,
    killedEndpointLaw_apply (-a) T ((measurable_endpointShift a) hB)]
  rfl

theorem map_restrict_above_shift (μ : Measure ℝ) (a : ℝ) :
    (μ.restrict (Ioi (-a))).map (fun z ↦ z+a) = (μ.map (fun z ↦ z+a)).restrict (Ioi 0) := by
  have he : (fun z : ℝ ↦ z+a) ⁻¹' Ioi 0 = Ioi (-a) := by
    ext z
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [Measure.restrict_map (measurable_endpointShift a) measurableSet_Ioi,he]

theorem law_add_reflected (a : ℝ) (ha : 0 < a) (T : ℝ≥0) :
    law a T+(gaussianReal (-a) T).restrict (Ioi 0) = (gaussianReal a T).restrict (Ioi 0) := by
  have he := congrArg (fun μ : Measure ℝ ↦ μ.map (fun z ↦ z+a))
    (killedEndpointLaw_add_reflected (-a) (by linarith) T)
  rw [Measure.map_add _ _ (measurable_endpointShift a),
    map_restrict_above_shift,map_restrict_above_shift,
    gaussianReal_map_add_const,gaussianReal_map_add_const,
    show 2*(-a)+a = -a by ring,zero_add,← law_eq_shift_killed] at he
  exact he

def densityReal (a : ℝ) (T : ℝ≥0) : ℝ → ℝ :=
  (Ioi 0).indicator (fun y ↦ gaussianPDFReal a T y-gaussianPDFReal (-a) T y)

def density (a : ℝ) (T : ℝ≥0) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (densityReal a T y)

theorem measurable_densityReal (a : ℝ) (T : ℝ≥0) : Measurable (densityReal a T) :=
  ((measurable_gaussianPDFReal a T).sub (measurable_gaussianPDFReal (-a) T)).indicator measurableSet_Ioi

theorem measurable_density (a : ℝ) (T : ℝ≥0) : Measurable (density a T) :=
  (measurable_densityReal a T).ennreal_ofReal

theorem gaussianPDFReal_negativeMean_le (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (y : ℝ) (hy : 0 < y) : gaussianPDFReal (-a) T y ≤ gaussianPDFReal a T y := by
  have he := gaussianPDFReal_reflected_le (-a) (by linarith) T hT (x := y-a) (by linarith)
  rw [gaussianPDFReal_sub,gaussianPDFReal_sub,zero_add,show 2*(-a)+a = -a by ring] at he
  exact he

theorem densityReal_nonneg (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    0 ≤ densityReal a T y := by
  by_cases hy : 0 < y
  · exact Set.indicator_nonneg (fun z hz ↦ sub_nonneg.mpr
      (gaussianPDFReal_negativeMean_le a ha T hT z hz)) y
  · simp only [densityReal,Set.indicator,mem_Ioi,if_neg hy,le_refl]

theorem density_add_reflected (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    density a T+(Ioi 0).indicator (gaussianPDF (-a) T) = (Ioi 0).indicator (gaussianPDF a T) := by
  funext y
  by_cases hy : 0 < y
  · simp only [Pi.add_apply,density,densityReal,Set.indicator,mem_Ioi,if_pos hy,gaussianPDF]
    rw [ENNReal.ofReal_sub _ (gaussianPDFReal_nonneg (-a) T y)]
    exact tsub_add_cancel_of_le (ENNReal.ofReal_le_ofReal
      (gaussianPDFReal_negativeMean_le a ha T hT y hy))
  · simp only [Pi.add_apply,density,densityReal,Set.indicator,mem_Ioi,if_neg hy,
      ENNReal.ofReal_zero,add_zero]

theorem densityLaw_add_reflected (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    volume.withDensity (density a T)+(gaussianReal (-a) T).restrict (Ioi 0) =
      (gaussianReal a T).restrict (Ioi 0) := by
  rw [gaussianReal_of_var_ne_zero (-a) (ne_of_gt hT),
    gaussianReal_of_var_ne_zero a (ne_of_gt hT),restrict_withDensity measurableSet_Ioi,
    restrict_withDensity measurableSet_Ioi,← withDensity_indicator measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi,← withDensity_add_left (measurable_density a T),
    density_add_reflected a ha T hT]

theorem law_eq_withDensity (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    law a T = volume.withDensity (density a T) := by
  ext B hB
  have h₁ := congrArg (fun μ : Measure ℝ ↦ μ B) (law_add_reflected a ha T)
  have h₂ := congrArg (fun μ : Measure ℝ ↦ μ B) (densityLaw_add_reflected a ha T hT)
  simp only [Measure.add_apply] at h₁ h₂
  exact (ENNReal.add_left_inj (measure_ne_top _ B)).mp (h₁.trans h₂.symm)

theorem law_probability_density (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f | (T : ℝ≥0∞) < firstPassage (-a) f ∧ f T+a ∈ B} =
      ∫⁻ y in B, density a T y := by
  rw [← law_apply a T hB,law_eq_withDensity a ha T hT,withDensity_apply _ hB]

end PerronWright.BrownianPositiveKilledEndpoint
