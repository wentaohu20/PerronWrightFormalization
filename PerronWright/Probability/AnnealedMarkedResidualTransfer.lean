import PerronWright.Probability.AnnealedMarkedResidualLaw

/-! # Exact L1 transfer estimates for genuine residual densities -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedResidualTransfer

open AnnealedMarkedResidualLaw ProfileSquareMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A genuine marginal measure controls preimages even for nonmeasurable
sets, by passing to its canonical measurable superset. -/
theorem measurePreserving_real_preimage_le {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure ν] {f : Ω → Ω'}
    (hf : MeasurePreserving f μ ν) (s : Set Ω') : μ.real (f ⁻¹' s) ≤ ν.real s := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  calc
    _ ≤ μ (f ⁻¹' toMeasurable ν s) := measure_mono (Set.preimage_mono (subset_toMeasurable ν s))
    _ = ν (toMeasurable ν s) := hf.measure_preimage (measurableSet_toMeasurable ν s).nullMeasurableSet
    _ = _ := measure_toMeasurable s

theorem densityMeasure_univ_real (μ : Measure Ω) (F : Ω → ℝ)
    (hF : Integrable F μ) (hn : ∀ ω, 0 ≤ F ω) :
    (μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω))).real Set.univ = ∫ ω, F ω ∂μ := by
  rw [measureReal_def,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]

/-- Every bad-set weighted mass is bounded by its true unweighted mass
plus the actual L1 density error.  No measurability of the set is needed. -/
theorem densityMeasure_real_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ)
    (s : Set Ω) :
    (μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω))).real s ≤ μ.real s + ∫ ω, |F ω-1| ∂μ := by
  let ν := μ.withDensity (fun ω ↦ ENNReal.ofReal |F ω-1|)
  have hAi : Integrable (fun ω ↦ |F ω-1|) μ := (hF.sub (integrable_const 1)).abs
  have hν : IsFiniteMeasure ν := densityMeasure_isFinite μ _ hAi (fun _ ↦ abs_nonneg _)
  let : IsFiniteMeasure ν := hν
  have hupper : μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω)) ≤ μ + ν := by
    have hh : μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω)) ≤
        μ.withDensity ((1 : Ω → ENNReal) + fun ω ↦ ENNReal.ofReal |F ω-1|) := by
      apply withDensity_mono
      apply Eventually.of_forall
      intro ω
      change ENNReal.ofReal (F ω) ≤ 1 + ENNReal.ofReal |F ω-1|
      rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [le_abs_self (F ω-1)])
    have hs := withDensity_add_left (μ := μ) (f := (1 : Ω → ENNReal))
      measurable_const (fun ω ↦ ENNReal.ofReal |F ω-1|)
    rw [hs,withDensity_one] at hh
    exact hh
  have hm : (μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω))).real s ≤ (μ+ν).real s :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hupper s)
  rw [measureReal_add_apply] at hm
  have ht : ν.real Set.univ = ∫ ω, |F ω-1| ∂μ :=
    densityMeasure_univ_real μ _ hAi (fun _ ↦ abs_nonneg _)
  have hνs : ν.real s ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ s)
  rw [ht] at hνs
  linarith only [hm,hνs]

/-- Dividing a nonnegative density by its genuine expectation introduces
only its L1 error and its actual total-mass error. -/
theorem integral_abs_normalized_density_sub_one_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ) {Z : ℝ} (hZ : 0 < Z) :
    (∫ ω, |F ω/Z-1| ∂μ) ≤ ((∫ ω, |F ω-1| ∂μ) + |Z-1|)/Z := by
  have hi : Integrable (fun ω ↦ |F ω/Z-1|) μ := ((hF.div_const Z).sub (integrable_const 1)).abs
  have hAi : Integrable (fun ω ↦ |F ω-1|) μ := (hF.sub (integrable_const 1)).abs
  have hUi : Integrable (fun ω ↦ (|F ω-1|+|Z-1|)/Z) μ := (hAi.add (integrable_const _)).div_const Z
  have hh := integral_mono hi hUi (fun ω ↦ by
    have he : F ω/Z-1 = ((F ω-1)-(Z-1))/Z := by field_simp; ring
    rw [he,abs_div,abs_of_pos hZ]
    exact div_le_div_of_nonneg_right (abs_sub _ _) hZ.le)
  rw [integral_div,integral_add hAi (integrable_const _),integral_const] at hh
  simpa only [probReal_univ,smul_eq_mul,one_mul] using hh

theorem integral_weighted_test_sub_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Measurable G)
    {B : ℝ} (hbound : ∀ ω, |G ω| ≤ B) :
    |(∫ ω, F ω*G ω ∂μ) - ∫ ω, G ω ∂μ| ≤ B * ∫ ω, |F ω-1| ∂μ := by
  have hGb : ∀ᵐ ω ∂μ, ‖G ω‖ ≤ B := Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hbound ω)
  have hGi := integrable_of_measurable_abs_le μ hG hbound
  have hFG := hF.mul_bdd hG.aestronglyMeasurable hGb
  have hFi := (hF.sub (integrable_const 1)).abs
  rw [← integral_sub hFG hGi]
  have he : (fun ω ↦ F ω*G ω-G ω) = (fun ω ↦ (F ω-1)*G ω) := by funext ω; ring
  rw [he]
  calc
    _ ≤ ∫ ω, |(F ω-1)*G ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, B*|F ω-1| ∂μ := by
      apply integral_mono (((hF.sub (integrable_const 1)).mul_bdd hG.aestronglyMeasurable hGb).abs) (hFi.const_mul B)
      intro ω
      change |(F ω-1)*G ω| ≤ B*|F ω-1|
      rw [abs_mul,mul_comm B]
      exact mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end PerronWright.AnnealedMarkedResidualTransfer
