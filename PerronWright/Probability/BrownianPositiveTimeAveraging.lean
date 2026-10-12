import PerronWright.Probability.BrownianBridgeUniformSmallTime
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Genuine normalized positive-time averaging at zero

The average is literal normalized Lebesgue measure on (0,epsilon].
Its right-limit theorem follows from the proved uniform-time scaling
and dominated convergence; no interchange of limits is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveTimeAveraging

open BrownianCircleUniformTime BrownianBridgeUniformSmallTime

theorem ae_unitInterval : ∀ᵐ x ∂intervalUniform 1, x ∈ Ioc (0 : ℝ) 1 := by
  simpa only [intervalUniform,ENNReal.ofReal_one,inv_one,one_smul] using
    ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc

theorem scaled_uniform_lintegral (ε : ℝ) (hε : 0 < ε)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂intervalUniform ε) = ∫⁻ x, F (ε*x) ∂intervalUniform 1 := by
  rw [← intervalUniform_one_map_mul ε hε]
  exact lintegral_map hF (measurable_const_mul ε)

theorem uniform_lintegral_right_tendsto (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (L : ℝ≥0∞) (hL : L ≠ ⊤) (hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun ε : ℝ ↦ ∫⁻ s, F s ∂intervalUniform ε) (𝓝[>] 0) (𝓝 L) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, F s < L+1 :=
    hlim.eventually_lt_const (ENNReal.lt_add_right hL one_ne_zero)
  obtain ⟨δ,hδ,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂intervalUniform 1, F (ε*x) ≤ L+1 := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    filter_upwards [ae_unitInterval] with x hx
    have hmem : ε*x ∈ Ioo (0 : ℝ) δ :=
      ⟨mul_pos hε.1 hx.1,(mul_le_mul_of_nonneg_left hx.2 hε.1.le).trans_lt
        (by simpa only [mul_one] using hε.2)⟩
    exact (hbound hmem).le
  have hpoint : ∀ᵐ x ∂intervalUniform 1,
      Tendsto (fun ε : ℝ ↦ F (ε*x)) (𝓝[>] 0) (𝓝 L) := by
    filter_upwards [ae_unitInterval] with x hx
    apply hlim.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq,zero_mul] using
        ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝[>] 0)).mono_right
          nhdsWithin_le_nhds).mul_const x
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hε hx.1
  have hfin : (∫⁻ _x, L+1 ∂intervalUniform 1) ≠ ⊤ := by
    rw [lintegral_const,measure_univ,mul_one]
    exact ENNReal.add_ne_top.mpr ⟨hL,by norm_num⟩
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := intervalUniform 1)
    (fun _x ↦ L+1) (Eventually.of_forall (fun ε ↦ hF.comp (measurable_const_mul ε)))
      hb hfin hpoint
  simp only [lintegral_const,measure_univ,mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (scaled_uniform_lintegral ε hε F hF).symm

theorem normalized_positive_lintegral_right_tendsto
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun ε : ℝ ↦ (ENNReal.ofReal ε)⁻¹*∫⁻ s in Ioc (0 : ℝ) ε, F s)
      (𝓝[>] 0) (𝓝 L) := by
  have h := uniform_lintegral_right_tendsto F hF L hL hlim
  simpa only [intervalUniform,lintegral_smul_measure,smul_eq_mul] using h

end PerronWright.BrownianPositiveTimeAveraging
