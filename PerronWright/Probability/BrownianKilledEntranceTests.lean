import PerronWright.Probability.BrownianKilledBoundaryEntrance

/-! # Actual killed Brownian small-start limits for bounded Borel tests

All positive starts share an explicit integrable bound on each compact
interval. Dominated convergence therefore proves a limit for integrals
under the literal killed Brownian endpoint measure. The entrance measure
is obtained from actual laws, not assumed as a process or excursion law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledEntranceTests

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance

theorem normalized_law_test_eq_density (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    {B : Set ℝ} (hB : MeasurableSet B) (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ y in B, Ψ y ∂law a T)/ENNReal.ofReal a =
      ∫⁻ y in B, Ψ y*ENNReal.ofReal (densityReal a T y/a) := by
  rw [law_eq_withDensity a ha T hT,
    setLIntegral_withDensity_eq_setLIntegral_mul volume (measurable_density a T) hΨ hB,
    div_eq_mul_inv,← lintegral_mul_const _ ((measurable_density a T).mul hΨ)]
  apply lintegral_congr
  intro y
  change (ENNReal.ofReal (densityReal a T y)*Ψ y)*(ENNReal.ofReal a)⁻¹ =
    Ψ y*ENNReal.ofReal (densityReal a T y/a)
  rw [ENNReal.ofReal_div_of_pos ha,div_eq_mul_inv]
  ac_rfl

theorem normalized_law_bounded_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (b C : ℝ) (hb : 0 ≤ b) (_hC : 0 ≤ C) (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ y, Ψ y ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ (∫⁻ y in Icc 0 b, Ψ y ∂law a T)/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (∫⁻ y in Icc 0 b, Ψ y*entrance T y)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 b)
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (Icc (0 : ℝ) b)) univ < ∞
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let D : ℝ := (2*b/(T : ℝ))*(Real.sqrt (2*Real.pi*(T : ℝ)))⁻¹
  let bound : ℝ≥0∞ := ENNReal.ofReal C*ENNReal.ofReal D
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Measurable (fun y ↦ Ψ y*ENNReal.ofReal (densityReal a T y/a)) :=
    Eventually.of_forall (fun a ↦ hΨ.mul ((measurable_densityReal a T).div_const a).ennreal_ofReal)
  have hbnd : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ y ∂μ,
      Ψ y*ENNReal.ofReal (densityReal a T y/a) ≤ bound := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_le_mul' (hbound y) (ENNReal.ofReal_le_ofReal
      (densityReal_div_start_le_window a ha T hT b y hb hy.2))
  have hfin : (∫⁻ _y, bound ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (measure_ne_top μ univ)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun a : ℝ ↦ Ψ y*ENNReal.ofReal (densityReal a T y/a))
      (𝓝[>] 0) (𝓝 (Ψ y*entrance T y)) := by
    exact Eventually.of_forall (fun y ↦ ENNReal.Tendsto.const_mul
      (density_div_start_tendsto T hT y)
      (Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound y))))
  have he := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _y ↦ bound) hm hbnd hfin hlim
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (normalized_law_test_eq_density a ha T hT measurableSet_Icc Ψ hΨ).symm

theorem normalized_law_window_probability_tendsto (T : ℝ≥0) (hT : 0 < T) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun a : ℝ ↦ law a T (Icc 0 b)/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (∫⁻ y in Icc 0 b, entrance T y)) := by
  simpa only [lintegral_one,Measure.restrict_apply_univ,one_mul] using
    normalized_law_bounded_test_tendsto T hT b 1 hb (by norm_num) (fun _ ↦ 1)
      measurable_const (fun _ ↦ by simp)

end PerronWright.BrownianKilledEntranceTests
