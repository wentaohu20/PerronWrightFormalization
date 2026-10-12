import PerronWright.Probability.BrownianPassageWeightedScaling
import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds

/-! # Genuine weighted passage contraction against a killed boundary

One bound holds for every positive depth, not merely for a small
endpoint. It supplies actual dominated convergence after square-root
scaling, giving the literal half-entrance boundary factor.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPassageBoundaryContraction

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeGaussianBounds BrownianPassageWeightedScaling

def boundaryBound (t : ℝ≥0) : ℝ :=
  envelopeSup t t+(Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹

theorem boundaryBound_nonneg (t : ℝ≥0) : 0 ≤ boundaryBound t := by
  unfold boundaryBound envelopeSup
  exact add_nonneg (mul_nonneg (envelopeCoefficient_nonneg t) (by positivity)) (by positivity)

theorem densityReal_div_start_le_uniform (a : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ht : 0 < t) (y : ℝ) :
    densityReal a t y/a ≤ boundaryBound t := by
  by_cases ha1 : a ≤ 1
  · exact (densityReal_div_start_le_envelope a ha ha1 t t t ht le_rfl le_rfl y).trans
      ((envelopeReal_le_sup t t ht y).trans
        (le_add_of_nonneg_right (by positivity)))
  · have hgauss : densityReal a t y ≤ (Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹ := by
      by_cases hy : 0 < y
      · rw [densityReal,indicator_of_mem (show y ∈ Ioi 0 from hy)]
        exact (sub_le_self _ (gaussianPDFReal_nonneg (-a) t y)).trans
          (gaussianPDFReal_le_prefactor a t ht y)
      · simp only [densityReal,indicator_of_notMem (show y ∉ Ioi 0 from hy)]
        positivity
    have hnorm : densityReal a t y/a ≤ (Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹ := by
      apply (div_le_iff₀ ha).mpr
      exact hgauss.trans (le_mul_of_one_le_right (by positivity) (lt_of_not_ge ha1).le)
    exact hnorm.trans (le_add_of_nonneg_left (by
      unfold envelopeSup
      exact mul_nonneg (envelopeCoefficient_nonneg t) (by positivity)))

theorem normalized_density_le_uniform (a : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ht : 0 < t) (y : ℝ) :
    density a t y/ENNReal.ofReal a ≤ ENNReal.ofReal (boundaryBound t) := by
  rw [density,← ENNReal.ofReal_div_of_pos ha]
  exact ENNReal.ofReal_le_ofReal (densityReal_div_start_le_uniform a ha t ht y)

theorem measurable_normalized_density (t : ℝ≥0) (y : ℝ) :
    Measurable (fun a : ℝ ↦ density a t y/ENNReal.ofReal a) := by
  unfold density densityReal
  by_cases hy : 0 < y
  · simp only [indicator_of_mem (show y ∈ Ioi 0 from hy)]
    unfold gaussianPDFReal
    fun_prop
  · simp only [indicator_of_notMem (show y ∉ Ioi 0 from hy),
      ENNReal.ofReal_zero,ENNReal.zero_div]
    exact measurable_const

theorem normalized_density_sqrt_tendsto (t : ℝ≥0) (ht : 0 < t)
    (y x : ℝ) (hx : 0 < x) :
    Tendsto (fun s : ℝ ↦ density (Real.sqrt s*x) t y/ENNReal.ofReal (Real.sqrt s*x))
      (𝓝[>] 0) (𝓝 (entrance t y)) := by
  have hs : Tendsto (fun s : ℝ ↦ Real.sqrt s*x) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero,zero_mul] using
        ((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const x
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos (Real.sqrt_pos.mpr hs) hx
  have h := (density_div_start_tendsto t ht y).comp hs
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ENNReal.ofReal_div_of_pos (mul_pos (Real.sqrt_pos.mpr hs) hx)

theorem actual_weighted_boundary_contraction (t : ℝ≥0) (ht : 0 < t) (y : ℝ)
    (Φ : (ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun s : ℝ ↦ ∫⁻ a, (density a t y/ENNReal.ofReal a)*
      ENNReal.ofReal (Φ (s,a)) ∂weightedLaw s) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (1/2 : ℝ)*entrance t y*ENNReal.ofReal (Φ (0,0)))) := by
  let F (s x : ℝ) : ℝ≥0∞ :=
    (density (Real.sqrt s*x) t y/ENNReal.ofReal (Real.sqrt s*x))*
      ENNReal.ofReal (Φ (s,Real.sqrt s*x))
  let C : ℝ≥0∞ := ENNReal.ofReal (boundaryBound t)*ENNReal.ofReal ‖Φ‖
  have hm (s : ℝ) : Measurable (F s) :=
    ((measurable_normalized_density t y).comp (measurable_const.mul measurable_id)).mul (by fun_prop)
  have hbase : ∀ᵐ x ∂weightedLaw 1, 0 < x := by
    rw [weightedLaw,ae_withDensity_iff (measurable_weight 1)]
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun _ hx _ ↦ hx)
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ᵐ x ∂weightedLaw 1, F s x ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [hbase] with x hx
    exact mul_le_mul' (normalized_density_le_uniform _ (mul_pos (Real.sqrt_pos.mpr hs) hx) t ht y)
      (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (s,Real.sqrt s*x))))
  have hfin : (∫⁻ _x, C ∂weightedLaw 1) ≠ ⊤ := by
    rw [lintegral_const,weightedLaw_mass 1 (by norm_num)]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ x ∂weightedLaw 1, Tendsto (fun s : ℝ ↦ F s x) (𝓝[>] 0)
      (𝓝 (entrance t y*ENNReal.ofReal (Φ (0,0)))) := by
    filter_upwards [hbase] with x hx
    have hΦ : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (Φ (s,Real.sqrt s*x))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (Φ (0,0)))) := by
      apply ENNReal.tendsto_ofReal
      apply Φ.continuous.continuousAt.tendsto.comp
      have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [id_eq,Real.sqrt_zero,zero_mul] using
        (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds (hs.mul_const x)
    exact ENNReal.Tendsto.mul (normalized_density_sqrt_tendsto t ht y x hx)
      (Or.inr ENNReal.ofReal_ne_top) hΦ (Or.inr ENNReal.ofReal_ne_top)
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := weightedLaw 1)
    (fun _x ↦ C) (Eventually.of_forall hm) hb hfin hlim
  simp only [lintegral_const,weightedLaw_mass 1 (by norm_num)] at h
  have he : (fun s : ℝ ↦ ∫⁻ a, (density a t y/ENNReal.ofReal a)*
      ENNReal.ofReal (Φ (s,a)) ∂weightedLaw s) =ᶠ[𝓝[>] 0]
      (fun s : ℝ ↦ ∫⁻ x, F s x ∂weightedLaw 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact weightedLaw_sqrt_lintegral s hs _ ((measurable_normalized_density t y).mul (by fun_prop))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h.congr' he.symm

end PerronWright.BrownianPassageBoundaryContraction
