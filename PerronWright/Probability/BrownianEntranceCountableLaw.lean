import PerronWright.Probability.BrownianEntranceEndpointFamily
import PerronWright.Probability.CountableRealProjectiveLaw

/-! # A constructed countable entrance process law

For any countable deterministic sampling times, including repetitions and
the endpoints, this file constructs a genuine probability measure on real
sequences. Its finite laws are the proved entrance laws. Actual source Borel
limits discharge consistency before the conditional-distribution / trajectory
construction is used. No path-limit or continuous-realization premise occurs.
-/

open MeasureTheory ProbabilityTheory Preorder Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceCountableLaw

open BrownianPathLaw BrownianPositiveBridgeConditioning
open CountableRealProjectiveLaw

def sampleTimes (σ : ℕ → ℝ≥0) (J : Finset ℕ) : Finset ℝ≥0 := J.image σ

def sampleFromFinite (σ : ℕ → ℝ≥0) (J : Finset ℕ)
    (v : sampleTimes σ J → ℝ) : J → ℝ :=
  fun j ↦ v ⟨σ j.val,Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩

theorem measurable_sampleFromFinite (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    Measurable (sampleFromFinite σ J) := measurable_pi_lambda _ (fun _j ↦ measurable_pi_apply _)

def sampleLaw (T : ℝ≥0) (σ : ℕ → ℝ≥0) (J : Finset ℕ) : Measure (J → ℝ) :=
  (BrownianEntranceEndpointFamily.finiteLaw T (sampleTimes σ J)).map (sampleFromFinite σ J)

theorem sampleLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    IsProbabilityMeasure (sampleLaw T σ J) := by
  let := BrownianEntranceEndpointFamily.finiteLaw_isProbability T hT (sampleTimes σ J)
  exact Measure.isProbabilityMeasure_map (measurable_sampleFromFinite σ J).aemeasurable

def sampleEval (T : ℝ≥0) (σ : ℕ → ℝ≥0) (J : Finset ℕ) (f : Path) : J → ℝ :=
  fun j ↦ if 0 < σ j.val ∧ σ j.val < T then f (σ j.val) else 0

theorem measurable_sampleEval (T : ℝ≥0) (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    Measurable (sampleEval T σ J) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : 0 < σ j.val ∧ σ j.val < T
  · simp only [sampleEval,if_pos h]
    exact (continuous_eval_const _).measurable
  · simp only [sampleEval,if_neg h]
    exact measurable_const

theorem actual_sample_bounded_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) (C : ℝ) (Ψ : (J → ℝ) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hb : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, Ψ (sampleEval T σ J f) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ v, Ψ v ∂sampleLaw T σ J)) := by
  have he := BrownianEntranceEndpointFamily.actual_padded_bounded_test_tendsto T hT
    (sampleTimes σ J) C (fun v ↦ Ψ (sampleFromFinite σ J v))
    (hΨ.comp (measurable_sampleFromFinite σ J)) (fun _v ↦ hb _)
  rw [sampleLaw,lintegral_map hΨ (measurable_sampleFromFinite σ J)]
  exact he

theorem actual_sample_borel_probability_tendsto (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) {B : Set (J → ℝ)} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a T).map (sampleEval T σ J)) B)
      (𝓝[>] 0) (𝓝 (sampleLaw T σ J B)) := by
  have he := actual_sample_bounded_test_tendsto T hT σ J 1
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
    (fun v ↦ by by_cases hv : v ∈ B <;> simp [hv])
  have h1 : (fun _ : J → ℝ ↦ (1 : ℝ≥0∞)) = (1 : (J → ℝ) → ℝ≥0∞) := rfl
  have hl : (∫⁻ v, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂sampleLaw T σ J) = sampleLaw T σ J B := by
    rw [h1]; exact lintegral_indicator_one hB
  rw [hl] at he
  apply he.congr
  intro a
  rw [← lintegral_map (measurable_const.indicator hB) (measurable_sampleEval T σ J),
    h1,lintegral_indicator_one hB]

theorem sampleLaw_projective (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ ℝ) (sampleLaw T σ) := by
  intro I J hJI
  have hm : Measurable (Finset.restrict₂ (π := fun _ : ℕ ↦ ℝ) hJI) := Finset.measurable_restrict₂ hJI
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB]
  have hsmall := actual_sample_borel_probability_tendsto T hT σ J hB
  have hbig := actual_sample_borel_probability_tendsto T hT σ I (hm hB)
  apply tendsto_nhds_unique hsmall
  apply hbig.congr
  intro a
  rw [Measure.map_apply (measurable_sampleEval T σ J) hB,
    Measure.map_apply (measurable_sampleEval T σ I) (hm hB)]
  rfl

def prefixLaw (T : ℝ≥0) (σ : ℕ → ℝ≥0) (n : ℕ) : Measure (Prefix n) :=
  sampleLaw T σ (Finset.Iic n)

theorem prefixLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (prefixLaw T σ n) := sampleLaw_isProbability T hT σ (Finset.Iic n)

theorem prefixLaw_consistent (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0)
    (a b : ℕ) (hab : a ≤ b) :
    (prefixLaw T σ b).map (frestrictLe₂ (π := fun _ : ℕ ↦ ℝ) hab) = prefixLaw T σ a :=
  (sampleLaw_projective T hT σ (Finset.Iic b) (Finset.Iic a) (Finset.Iic_subset_Iic.mpr hab)).symm

/-- Constructed probability law, not an existence assumption. -/
def law (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) : Measure (ℕ → ℝ) := by
  letI : ∀ n, IsProbabilityMeasure (prefixLaw T σ n) := fun n ↦ prefixLaw_isProbability T hT σ n
  exact CountableRealProjectiveLaw.law (prefixLaw T σ)

theorem law_isProbability (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    IsProbabilityMeasure (law T hT σ) := by
  unfold law
  infer_instance

theorem law_prefix (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) (n : ℕ) :
    (law T hT σ).map (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) = prefixLaw T σ n := by
  let : ∀ j, IsProbabilityMeasure (prefixLaw T σ j) := fun j ↦ prefixLaw_isProbability T hT σ j
  unfold law
  exact CountableRealProjectiveLaw.law_prefix (prefixLaw T σ) (prefixLaw_consistent T hT σ) n

/-- All finite-set marginals of the constructed law are the actual-source
entrance marginals, including repeated sampling times and both endpoints. -/
theorem law_projectiveLimit (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    IsProjectiveLimit (α := fun _ : ℕ ↦ ℝ) (law T hT σ) (sampleLaw T σ) := by
  intro J
  let n := J.sup id
  have hJ : J ⊆ Finset.Iic n := by
    intro j hj
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hj)
  have hm : Measurable (Finset.restrict₂ (π := fun _ : ℕ ↦ ℝ) hJ) := Finset.measurable_restrict₂ hJ
  have he : (J.restrict (π := fun _ : ℕ ↦ ℝ)) =
      Finset.restrict₂ (π := fun _ : ℕ ↦ ℝ) hJ ∘ frestrictLe (π := fun _ : ℕ ↦ ℝ) n := by
    funext v j
    rfl
  rw [he,← Measure.map_map hm (measurable_frestrictLe (X := fun _ : ℕ ↦ ℝ) n),law_prefix]
  exact (sampleLaw_projective T hT σ (Finset.Iic n) J hJ).symm

theorem law_unique (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) (μ : Measure (ℕ → ℝ))
    (hμ : IsProjectiveLimit (α := fun _ : ℕ ↦ ℝ) μ (sampleLaw T σ)) : μ = law T hT σ := by
  let : ∀ J, IsProbabilityMeasure (sampleLaw T σ J) := fun J ↦ sampleLaw_isProbability T hT σ J
  exact hμ.unique (law_projectiveLimit T hT σ)

theorem exists_unique_projectiveLimit (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    ∃! μ : Measure (ℕ → ℝ), IsProjectiveLimit (α := fun _ : ℕ ↦ ℝ) μ (sampleLaw T σ) := by
  exact ⟨law T hT σ,law_projectiveLimit T hT σ,fun μ hμ ↦ law_unique T hT σ μ hμ⟩

theorem actual_law_finite_borel_probability_tendsto (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) {B : Set (J → ℝ)} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a T).map (sampleEval T σ J)) B)
      (𝓝[>] 0) (𝓝 (((law T hT σ).map (J.restrict (π := fun _ : ℕ ↦ ℝ))) B)) := by
  rw [law_projectiveLimit T hT σ J]
  exact actual_sample_borel_probability_tendsto T hT σ J hB

theorem actual_law_finite_bounded_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) (C : ℝ) (Ψ : (J → ℝ) → ℝ≥0∞)
    (hΨ : Measurable Ψ) (hb : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, Ψ (sampleEval T σ J f) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ v, Ψ (J.restrict v) ∂law T hT σ)) := by
  have he := actual_sample_bounded_test_tendsto T hT σ J C Ψ hΨ hb
  rw [← law_projectiveLimit T hT σ J,lintegral_map hΨ (Finset.measurable_restrict J)] at he
  exact he

theorem ae_sampleLaw_boundary_zero (T : ℝ≥0) (σ : ℕ → ℝ≥0) (J : Finset ℕ) (j : J)
    (h : ¬ (0 < σ j.val ∧ σ j.val < T)) : ∀ᵐ v ∂sampleLaw T σ J, v j = 0 := by
  unfold sampleLaw
  apply (ae_map_iff (measurable_sampleFromFinite σ J).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)).mpr
  exact BrownianEntranceEndpointFamily.ae_finiteLaw_boundary_zero T (sampleTimes σ J)
    ⟨σ j.val,Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩ h

theorem ae_law_boundary_zero (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    ∀ᵐ v ∂law T hT σ, ∀ n, ¬ (0 < σ n ∧ σ n < T) → v n = 0 := by
  rw [ae_all_iff]
  intro n
  by_cases h : 0 < σ n ∧ σ n < T
  · exact Eventually.of_forall (fun _v hn ↦ (hn h).elim)
  · have he := ae_sampleLaw_boundary_zero T σ (Finset.Iic n) ⟨n,Finset.mem_Iic.mpr le_rfl⟩ h
    change ∀ᵐ v ∂prefixLaw T σ n, v ⟨n,Finset.mem_Iic.mpr le_rfl⟩ = 0 at he
    rw [← law_prefix T hT σ n] at he
    have hm : Measurable (frestrictLe (π := fun _ : ℕ ↦ ℝ) n) := measurable_frestrictLe n
    have hp := (ae_map_iff hm.aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply ⟨n,Finset.mem_Iic.mpr le_rfl⟩) measurable_const)).mp he
    filter_upwards [hp] with v hv
    exact fun _hn ↦ hv

end PerronWright.BrownianEntranceCountableLaw
