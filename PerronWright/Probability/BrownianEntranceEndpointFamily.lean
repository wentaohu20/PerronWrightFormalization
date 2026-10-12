import PerronWright.Probability.BrownianEntranceProjectiveFamily

/-! # A genuine zero-endpoint projective family

The interior entrance law is extended by deterministic zero coordinates at
0 and T (and outside the horizon). Its actual approximating source is the
positive bridge with these deterministic coordinates replaced by zero.
This is deliberately not a claim of setwise convergence of Dirac(a) to
Dirac(0) at the unmodified positive-bridge endpoints.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceEndpointFamily

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianEntranceProjectiveFamily

def insideTimes (T : ℝ≥0) (J : Finset ℝ≥0) : Finset (InteriorTime T) :=
  J.subtype (fun t ↦ 0 < t ∧ t < T)

def pad (T : ℝ≥0) (J : Finset ℝ≥0) (v : insideTimes T J → ℝ) : J → ℝ :=
  fun j ↦ if h : 0 < j.val ∧ j.val < T then
    v ⟨⟨j.val,h⟩,Finset.mem_subtype.mpr j.property⟩ else 0

theorem measurable_pad (T : ℝ≥0) (J : Finset ℝ≥0) : Measurable (pad T J) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : 0 < j.val ∧ j.val < T
  · simp only [pad,dif_pos h]
    exact measurable_pi_apply _
  · simp only [pad,dif_neg h]
    exact measurable_const

def finiteLaw (T : ℝ≥0) (J : Finset ℝ≥0) : Measure (J → ℝ) :=
  (BrownianEntranceProjectiveFamily.finiteLaw T (insideTimes T J)).map (pad T J)

theorem finiteLaw_empty (T : ℝ≥0) (hT : 0 < T) : finiteLaw T ∅ = Measure.dirac 0 := by
  let := BrownianEntranceProjectiveFamily.finiteLaw_isProbability T hT (insideTimes T ∅)
  have hp : pad T ∅ = (fun _ ↦ (0 : (∅ : Finset ℝ≥0) → ℝ)) :=
    funext (fun _ ↦ Subsingleton.elim _ _)
  unfold finiteLaw
  rw [hp,Measure.map_const,measure_univ,one_smul]

theorem finiteLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0) :
    IsProbabilityMeasure (finiteLaw T J) := by
  let := BrownianEntranceProjectiveFamily.finiteLaw_isProbability T hT (insideTimes T J)
  exact Measure.isProbabilityMeasure_map (measurable_pad T J).aemeasurable

def paddedFiniteEval (T : ℝ≥0) (J : Finset ℝ≥0) (f : Path) : J → ℝ :=
  fun j ↦ if 0 < j.val ∧ j.val < T then f j.val else 0

theorem measurable_paddedFiniteEval (T : ℝ≥0) (J : Finset ℝ≥0) :
    Measurable (paddedFiniteEval T J) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : 0 < j.val ∧ j.val < T
  · simp only [paddedFiniteEval,if_pos h]
    exact (continuous_eval_const _).measurable
  · simp only [paddedFiniteEval,if_neg h]
    exact measurable_const

theorem pad_finiteEval (T : ℝ≥0) (J : Finset ℝ≥0) (f : Path) :
    pad T J (BrownianEntranceProjectiveFamily.finiteEval T (insideTimes T J) f) =
      paddedFiniteEval T J f := by
  funext j
  by_cases h : 0 < j.val ∧ j.val < T <;>
    simp [pad,paddedFiniteEval,h,BrownianEntranceProjectiveFamily.finiteEval]

theorem actual_padded_bounded_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (J : Finset ℝ≥0) (C : ℝ) (Ψ : (J → ℝ) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hb : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, Ψ (paddedFiniteEval T J f) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ v, Ψ v ∂finiteLaw T J)) := by
  have he := actual_finite_bounded_test_tendsto T hT (insideTimes T J) C
    (fun v ↦ Ψ (pad T J v)) (hΨ.comp (measurable_pad T J)) (fun _v ↦ hb _)
  simp only [pad_finiteEval] at he
  rw [finiteLaw,lintegral_map hΨ (measurable_pad T J)]
  exact he

theorem actual_padded_borel_probability_tendsto (T : ℝ≥0) (hT : 0 < T)
    (J : Finset ℝ≥0) {B : Set (J → ℝ)} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a T).map (paddedFiniteEval T J)) B)
      (𝓝[>] 0) (𝓝 (finiteLaw T J B)) := by
  have he := actual_padded_bounded_test_tendsto T hT J 1
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
    (fun v ↦ by by_cases hv : v ∈ B <;> simp [hv])
  have h1 : (fun _ : J → ℝ ↦ (1 : ℝ≥0∞)) = (1 : (J → ℝ) → ℝ≥0∞) := rfl
  have hl : (∫⁻ v, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂finiteLaw T J) = finiteLaw T J B := by
    rw [h1]; exact lintegral_indicator_one hB
  rw [hl] at he
  apply he.congr
  intro a
  rw [← lintegral_map (measurable_const.indicator hB) (measurable_paddedFiniteEval T J),
    h1,lintegral_indicator_one hB]

theorem finiteLaw_projective (T : ℝ≥0) (hT : 0 < T) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 ↦ ℝ) (finiteLaw T) := by
  intro I J hJI
  have hm : Measurable (Finset.restrict₂ (π := fun _ : ℝ≥0 ↦ ℝ) hJI) :=
    Finset.measurable_restrict₂ hJI
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB]
  have hsmall := actual_padded_borel_probability_tendsto T hT J hB
  have hbig := actual_padded_borel_probability_tendsto T hT I (hm hB)
  apply tendsto_nhds_unique hsmall
  apply hbig.congr
  intro a
  rw [Measure.map_apply (measurable_paddedFiniteEval T J) hB,
    Measure.map_apply (measurable_paddedFiniteEval T I) (hm hB)]
  rfl

theorem ae_finiteLaw_boundary_zero (T : ℝ≥0) (J : Finset ℝ≥0) (j : J)
    (h : ¬ (0 < j.val ∧ j.val < T)) : ∀ᵐ v ∂finiteLaw T J, v j = 0 := by
  unfold finiteLaw
  apply (ae_map_iff (measurable_pad T J).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)).mpr
  exact Eventually.of_forall (fun v ↦ by simp only [pad,dif_neg h])

theorem ae_finiteLaw_initial_zero (T : ℝ≥0) (J : Finset ℝ≥0) (h0 : 0 ∈ J) :
    ∀ᵐ v ∂finiteLaw T J, v ⟨0,h0⟩ = 0 :=
  ae_finiteLaw_boundary_zero T J ⟨0,h0⟩ (by simp)

theorem ae_finiteLaw_terminal_zero (T : ℝ≥0) (J : Finset ℝ≥0) (hT : T ∈ J) :
    ∀ᵐ v ∂finiteLaw T J, v ⟨T,hT⟩ = 0 :=
  ae_finiteLaw_boundary_zero T J ⟨T,hT⟩ (by simp)

end PerronWright.BrownianEntranceEndpointFamily
