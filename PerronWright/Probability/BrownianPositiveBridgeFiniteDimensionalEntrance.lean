import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalLaw

/-! # Entrance--exit limit of the actual positive bridge one-point density

The limit concerns the real conditioned pinned bridge constructed in the
preceding files. It is not a definition or identification of an excursion.
The exact normalization vanishes quadratically, while the genuine entrance
and exit kernels each vanish linearly at the positive endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeFiniteDimensionalEntrance

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalLaw

theorem gaussianPDFReal_exchange (x y : ℝ) (T : ℝ≥0) :
    gaussianPDFReal x T y = gaussianPDFReal y T x := by
  unfold gaussianPDFReal
  rw [show (y-x)^2 = (x-y)^2 by ring]

theorem density_symm (x y : ℝ) (T : ℝ≥0) (hT : 0 < T) : density x T y = density y T x := by
  rcases lt_or_ge 0 x with hx | hx
  · rcases lt_or_ge 0 y with hy | hy
    · simp only [density,densityReal,Set.indicator,mem_Ioi,if_pos hx,if_pos hy]
      rw [gaussianPDFReal_exchange x y T]
      congr 2
      unfold gaussianPDFReal
      rw [sub_neg_eq_add,sub_neg_eq_add,add_comm x y]
    · rw [density_eq_zero_of_nonpos y hy T hT]
      simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg (not_lt.mpr hy),ENNReal.ofReal_zero,Pi.zero_apply]
  · rw [density_eq_zero_of_nonpos x hx T hT]
    simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg (not_lt.mpr hx),ENNReal.ofReal_zero,Pi.zero_apply]

theorem normalizationReal_pos (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    0 < 1-Real.exp (-2*a^2/(T : ℝ)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos ha]) (show (0 : ℝ) < T from hT)

theorem normalization_div_sq_tendsto (T : ℝ≥0) (_hT : 0 < T) :
    Tendsto (fun a : ℝ ↦ (1-Real.exp (-2*a^2/(T : ℝ)))/a^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (2/(T : ℝ))) := by
  have hd : HasDerivAt (fun v : ℝ ↦ 1-Real.exp ((-2/(T : ℝ))*v)) (2/(T : ℝ)) 0 := by
    apply ((hasDerivAt_const (0 : ℝ) 1).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (-2/(T : ℝ))).exp).congr_deriv
    simp only [id_eq,mul_zero,Real.exp_zero,one_mul]
    ring
  have hs := hd.tendsto_slope_zero_right
  have hp : Tendsto (fun a : ℝ ↦ a^2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (id : ℝ → ℝ) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [id_eq,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hi.pow 2
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact sq_pos_of_pos (show 0 < a from ha)
  have h := hs.comp hp
  apply h.congr
  intro a
  simp only [Function.comp_def,zero_add,mul_zero,Real.exp_zero,sub_self,sub_zero,smul_eq_mul]
  rw [show (-2/(T : ℝ))*a^2 = -2*a^2/(T : ℝ) by ring]
  simp only [div_eq_mul_inv]
  ring

def scaledDensityReal (a : ℝ) (s t : ℝ≥0) (x : ℝ) : ℝ :=
  ((densityReal a s x/a)*(densityReal a t x/a))/
    (((1-Real.exp (-2*a^2/(s+t : ℝ≥0)))/a^2)*gaussianPDFReal 0 (s+t) 0)

def entranceExitReal (s t : ℝ≥0) (x : ℝ) : ℝ :=
  (entranceReal s x*entranceReal t x)/((2/(s+t : ℝ≥0))*gaussianPDFReal 0 (s+t) 0)

def entranceExit (s t : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (entranceExitReal s t x)

theorem scaledDensityReal_tendsto (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    Tendsto (fun a : ℝ ↦ scaledDensityReal a s t x) (𝓝[>] (0 : ℝ)) (𝓝 (entranceExitReal s t x)) := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hden : (2/(s+t : ℝ≥0))*gaussianPDFReal 0 (s+t) 0 ≠ 0 := by
    have hp := gaussianPDFReal_pos 0 (s+t) 0 (ne_of_gt hT)
    positivity
  exact ((densityReal_div_start_tendsto s hs x).mul (densityReal_div_start_tendsto t ht x)).div
    ((normalization_div_sq_tendsto (s+t) hT).mul_const (gaussianPDFReal 0 (s+t) 0)) hden

theorem onePointDensity_eq_scaled (a : ℝ) (ha : 0 < a) (s t : ℝ≥0)
    (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    onePointDensity a s t x = ENNReal.ofReal (scaledDensityReal a s t x) := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hn := normalizationReal_pos a ha (s+t) hT
  have hp := gaussianPDFReal_pos 0 (s+t) 0 (ne_of_gt hT)
  have hsx := densityReal_nonneg a ha s hs x
  have htx := densityReal_nonneg a ha t ht x
  have he : scaledDensityReal a s t x =
      (densityReal a s x*densityReal a t x)/
        ((1-Real.exp (-2*a^2/(s+t : ℝ≥0)))*gaussianPDFReal 0 (s+t) 0) := by
    unfold scaledDensityReal
    field_simp [ne_of_gt ha,ne_of_gt hn,ne_of_gt hp]
  rw [he,ENNReal.ofReal_div_of_pos (mul_pos hn hp),ENNReal.ofReal_mul hsx,
    ENNReal.ofReal_mul hn.le]
  rw [onePointDensity,density_symm x a t ht]
  have hi : (ENNReal.ofReal (1-Real.exp (-2*a^2/(s+t : ℝ≥0)))*
      ENNReal.ofReal (gaussianPDFReal 0 (s+t) 0))⁻¹ =
      (ENNReal.ofReal (1-Real.exp (-2*a^2/(s+t : ℝ≥0))))⁻¹*
        (ENNReal.ofReal (gaussianPDFReal 0 (s+t) 0))⁻¹ :=
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)
  simp only [normalization,density,gaussianPDF,div_eq_mul_inv]
  simp only [div_eq_mul_inv] at hi
  rw [hi]
  exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

theorem onePointDensity_tendsto (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    Tendsto (fun a : ℝ ↦ onePointDensity a s t x) (𝓝[>] (0 : ℝ)) (𝓝 (entranceExit s t x)) := by
  apply (ENNReal.tendsto_ofReal (scaledDensityReal_tendsto s t hs ht x)).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (onePointDensity_eq_scaled a ha s t hs ht x).symm

end PerronWright.BrownianPositiveBridgeFiniteDimensionalEntrance
