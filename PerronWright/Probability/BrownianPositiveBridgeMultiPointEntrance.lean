import PerronWright.Probability.BrownianKilledDensityConvolution
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalEntrance

/-! # Literal finite entrance--interior--exit density limit

There are n+1 genuine free interior coordinates. The numerator is the
already proved Gaussian product density of the actual killed Brownian
tuple followed by its actual final killed transition. Only the two
boundary factors and the quadratic survival normalization vary with a.
No conditioned-path convergence or positive-excursion law is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointEntrance

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledDensityConvolution

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def internalDensity (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ∏ i : Fin n, density (v i.castSucc) (gaps (i.val+1)) (v i.succ)

theorem measurable_internalDensity (n : ℕ) (gaps : ℕ → ℝ≥0) : Measurable (internalDensity n gaps) := by
  unfold internalDensity
  apply Finset.measurable_prod
  intro i _
  have hp : Measurable (fun v : FreeVector (n+1) ↦ (v i.castSucc,v i.succ)) :=
    (measurable_pi_apply i.castSucc).prodMk (measurable_pi_apply i.succ)
  have hm := (measurable_joint_density (gaps (i.val+1))).comp
    hp
  simpa only [Function.comp_def] using hm

theorem internalDensity_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) :
    internalDensity n gaps v ≠ ∞ := by
  unfold internalDensity
  exact ENNReal.prod_ne_top (fun i _ ↦ ENNReal.ofReal_ne_top)

theorem jointDensity_first_factor (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) :
    jointDensity (n+1) a gaps v = density a (gaps 0) (v 0)*internalDensity n gaps v := by
  simp only [jointDensity,Fin.prod_univ_succ,prependInitial,Fin.castSucc_zero,Fin.cons_zero,Fin.val_zero,
    internalDensity,Fin.val_succ,Fin.castSucc_succ,Fin.cons_succ]

theorem lastState_succ (n : ℕ) (a : ℝ) (v : FreeVector (n+1)) :
    lastState (n+1) a v = v (Fin.last n) := by
  change (Fin.cons a v : Fin (n+2) → ℝ) (Fin.last (n+1)) = v (Fin.last n)
  rw [show Fin.last (n+1) = (Fin.last n).succ by rfl,Fin.cons_succ]

def rawMultiDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  (normalization a (sampleTime gaps (n+2)))⁻¹*
    (jointDensity (n+1) a gaps v*density (lastState (n+1) a v) (gaps (n+1)) a)/
      gaussianPDF 0 (sampleTime gaps (n+2)) 0

theorem measurable_rawMultiDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) :
    Measurable (rawMultiDensity n a gaps) := by
  have hm : Measurable (fun v : FreeVector (n+1) ↦ density (lastState (n+1) a v) (gaps (n+1)) a) := by
    have hp : Measurable (fun v : FreeVector (n+1) ↦ (lastState (n+1) a v,a)) :=
      ((continuous_lastState (n+1) a).measurable).prodMk measurable_const
    have he := (measurable_joint_density (gaps (n+1))).comp
      hp
    simpa only [Function.comp_def] using he
  exact measurable_const.mul ((measurable_jointDensity (n+1) a gaps).mul hm) |>.div_const _

def boundaryScaledReal (a : ℝ) (s t T : ℝ≥0) (x y : ℝ) : ℝ :=
  ((densityReal a s x/a)*(densityReal a t y/a))/
    (((1-Real.exp (-2*a^2/(T : ℝ)))/a^2)*gaussianPDFReal 0 T 0)

def boundaryLimitReal (s t T : ℝ≥0) (x y : ℝ) : ℝ :=
  (entranceReal s x*entranceReal t y)/((2/(T : ℝ))*gaussianPDFReal 0 T 0)

def entranceProduct (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ENNReal.ofReal (boundaryLimitReal (gaps 0) (gaps (n+1)) (sampleTime gaps (n+2))
    (v 0) (v (Fin.last n)))*internalDensity n gaps v

theorem boundaryScaledReal_tendsto (s t T : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (hT : 0 < T) (x y : ℝ) :
    Tendsto (fun a ↦ boundaryScaledReal a s t T x y) (𝓝[>] (0 : ℝ))
      (𝓝 (boundaryLimitReal s t T x y)) := by
  have hden : (2/(T : ℝ))*gaussianPDFReal 0 T 0 ≠ 0 := by
    have hp := gaussianPDFReal_pos 0 T 0 (ne_of_gt hT)
    positivity
  exact ((densityReal_div_start_tendsto s hs x).mul (densityReal_div_start_tendsto t ht y)).div
    ((normalization_div_sq_tendsto T hT).mul_const (gaussianPDFReal 0 T 0)) hden

theorem rawMultiDensity_eq_scaled (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hs : 0 < gaps 0) (ht : 0 < gaps (n+1)) (hT : 0 < sampleTime gaps (n+2))
    (v : FreeVector (n+1)) :
    rawMultiDensity n a gaps v = ENNReal.ofReal (boundaryScaledReal a (gaps 0) (gaps (n+1))
      (sampleTime gaps (n+2)) (v 0) (v (Fin.last n)))*internalDensity n gaps v := by
  let T := sampleTime gaps (n+2)
  have hn := normalizationReal_pos a ha T hT
  have hp := gaussianPDFReal_pos 0 T 0 (ne_of_gt hT)
  have hx := densityReal_nonneg a ha (gaps 0) hs (v 0)
  have hy := densityReal_nonneg a ha (gaps (n+1)) ht (v (Fin.last n))
  have he : boundaryScaledReal a (gaps 0) (gaps (n+1)) T (v 0) (v (Fin.last n)) =
      (densityReal a (gaps 0) (v 0)*densityReal a (gaps (n+1)) (v (Fin.last n)))/
        ((1-Real.exp (-2*a^2/(T : ℝ)))*gaussianPDFReal 0 T 0) := by
    unfold boundaryScaledReal
    field_simp [ne_of_gt ha,ne_of_gt hn,ne_of_gt hp]
  change rawMultiDensity n a gaps v = ENNReal.ofReal
    (boundaryScaledReal a (gaps 0) (gaps (n+1)) T (v 0) (v (Fin.last n)))*_
  rw [he,ENNReal.ofReal_div_of_pos (mul_pos hn hp),ENNReal.ofReal_mul hx,
    ENNReal.ofReal_mul hn.le]
  rw [rawMultiDensity,jointDensity_first_factor,lastState_succ,
    density_symm (v (Fin.last n)) a (gaps (n+1)) ht]
  change _ = (density a (gaps 0) (v 0)*density a (gaps (n+1)) (v (Fin.last n)))/
    (normalization a T*gaussianPDF 0 T 0)*internalDensity n gaps v
  simp only [div_eq_mul_inv]
  have hi : (normalization a T*gaussianPDF 0 T 0)⁻¹ =
      (normalization a T)⁻¹*(gaussianPDF 0 T 0)⁻¹ :=
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)
  rw [hi]
  ac_rfl

theorem rawMultiDensity_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hs : 0 < gaps 0) (ht : 0 < gaps (n+1)) (hT : 0 < sampleTime gaps (n+2))
    (v : FreeVector (n+1)) :
    Tendsto (fun a ↦ rawMultiDensity n a gaps v) (𝓝[>] (0 : ℝ)) (𝓝 (entranceProduct n gaps v)) := by
  have he := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_ofReal (boundaryScaledReal_tendsto (gaps 0) (gaps (n+1))
      (sampleTime gaps (n+2)) hs ht hT (v 0) (v (Fin.last n))))
    (Or.inr (internalDensity_ne_top n gaps v))
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (rawMultiDensity_eq_scaled n a ha gaps hs ht hT v).symm

theorem rawMultiDensity_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : (∫⁻ v, rawMultiDensity n a gaps v) = 1 := by
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (Nat.lt_succ_self _)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hn := normalizationReal_pos a ha (sampleTime gaps (n+2)) hT
  have hp := gaussianPDFReal_pos 0 (sampleTime gaps (n+2)) 0 (ne_of_gt hT)
  have hm : Measurable (fun v : FreeVector (n+1) ↦ jointDensity (n+1) a gaps v*
      density (lastState (n+1) a v) (gaps (n+1)) a) := by
    have hpair : Measurable (fun v : FreeVector (n+1) ↦ (lastState (n+1) a v,a)) :=
      ((continuous_lastState (n+1) a).measurable).prodMk measurable_const
    have hd := (measurable_joint_density (gaps (n+1))).comp
      hpair
    have hd' : Measurable (fun v : FreeVector (n+1) ↦ density (lastState (n+1) a v) (gaps (n+1)) a) := by
      simpa only [Function.comp_def] using hd
    exact (measurable_jointDensity (n+1) a gaps).mul hd'
  simp only [rawMultiDensity,div_eq_mul_inv]
  rw [lintegral_mul_const,lintegral_const_mul,
    jointDensity_exit_integral (n+1) a ha gaps hgaps a]
  simp only [density]
  rw [densityReal_eq_factor a (sampleTime gaps (n+2)) hT a ha]
  have hpdf : gaussianPDFReal a (sampleTime gaps (n+2)) a = gaussianPDFReal 0 (sampleTime gaps (n+2)) 0 := by
    simp only [gaussianPDFReal,sub_self]
  simp only [hpdf,show -2*a*a/(sampleTime gaps (n+2) : ℝ) =
      -2*a^2/(sampleTime gaps (n+2) : ℝ) by ring,
    ENNReal.ofReal_mul (le_of_lt hp)]
  change (normalization a (sampleTime gaps (n+2)))⁻¹*
    (gaussianPDF 0 (sampleTime gaps (n+2)) 0*normalization a (sampleTime gaps (n+2)))*
    (gaussianPDF 0 (sampleTime gaps (n+2)) 0)⁻¹ = 1
  have hn0 : normalization a (sampleTime gaps (n+2)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hn
  have hp0 : gaussianPDF 0 (sampleTime gaps (n+2)) 0 ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  rw [mul_left_comm,ENNReal.inv_mul_cancel hn0 ENNReal.ofReal_ne_top,mul_one,
    ENNReal.mul_inv_cancel hp0 ENNReal.ofReal_ne_top]
  all_goals first | exact hm | exact measurable_const.mul hm

theorem entranceProduct_eq_factors (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hT : 0 < sampleTime gaps (n+2)) (v : FreeVector (n+1)) :
    entranceProduct n gaps v = entrance (gaps 0) (v 0)*internalDensity n gaps v*
      entrance (gaps (n+1)) (v (Fin.last n))/
        ENNReal.ofReal ((2/(sampleTime gaps (n+2) : ℝ))*gaussianPDFReal 0 (sampleTime gaps (n+2)) 0) := by
  have hp := gaussianPDFReal_pos 0 (sampleTime gaps (n+2)) 0 (ne_of_gt hT)
  have hden : 0 < (2/(sampleTime gaps (n+2) : ℝ))*gaussianPDFReal 0 (sampleTime gaps (n+2)) 0 := by positivity
  rw [entranceProduct,boundaryLimitReal,ENNReal.ofReal_div_of_pos hden,
    ENNReal.ofReal_mul (entranceReal_nonneg _ _)]
  simp only [entrance,div_eq_mul_inv]
  ac_rfl

theorem measurable_entranceProduct (n : ℕ) (gaps : ℕ → ℝ≥0) :
    Measurable (entranceProduct n gaps) := by
  have hx : Measurable (fun v : FreeVector (n+1) ↦ entranceReal (gaps 0) (v 0)) :=
    (measurable_entranceReal _).comp (measurable_pi_apply 0)
  have hy : Measurable (fun v : FreeVector (n+1) ↦ entranceReal (gaps (n+1)) (v (Fin.last n))) :=
    (measurable_entranceReal _).comp (measurable_pi_apply _)
  exact ((hx.mul hy).div_const _).ennreal_ofReal.mul (measurable_internalDensity n gaps)

theorem density_pos (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) (y : ℝ) (hy : 0 < y) :
    0 < density a T y := by
  apply ENNReal.ofReal_pos.mpr
  rw [densityReal_eq_factor a T hT y hy]
  apply mul_pos (gaussianPDFReal_pos a T y (ne_of_gt hT))
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by nlinarith [mul_pos ha hy]) (show (0 : ℝ) < T from hT)

theorem entrance_pos (T : ℝ≥0) (hT : 0 < T) (y : ℝ) (hy : 0 < y) : 0 < entrance T y := by
  apply ENNReal.ofReal_pos.mpr
  simp only [entranceReal,Set.indicator,mem_Ioi,if_pos hy]
  exact mul_pos (div_pos (mul_pos (by norm_num) hy) hT) (gaussianPDFReal_pos 0 T y (ne_of_gt hT))

theorem entranceProduct_pos (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (v : FreeVector (n+1)) (hv : ∀ i, 0 < v i) :
    0 < entranceProduct n gaps v := by
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hi : 0 < internalDensity n gaps v := by
    apply bot_lt_iff_ne_bot.mpr
    unfold internalDensity
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ne_of_gt (density_pos _ (hv i.castSucc) _ (hgaps (i.val+1) (by omega)) _ (hv i.succ))
  rw [entranceProduct_eq_factors n gaps hT v]
  have hs := entrance_pos (gaps 0) (hgaps 0 (by omega)) (v 0) (hv 0)
  have ht := entrance_pos (gaps (n+1)) (hgaps (n+1) (by omega)) _ (hv (Fin.last n))
  exact ENNReal.div_pos_iff.mpr ⟨
    mul_ne_zero (mul_ne_zero (ne_of_gt hs) (ne_of_gt hi)) (ne_of_gt ht),ENNReal.ofReal_ne_top⟩

theorem entranceProduct_integral_le_one (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : (∫⁻ v, entranceProduct n gaps v) ≤ 1 := by
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hlim (v : FreeVector (n+1)) := rawMultiDensity_tendsto n gaps
    (hgaps 0 (by omega)) (hgaps (n+1) (by omega)) hT v
  have hm : Tendsto (fun a : ℝ ↦ ∫⁻ v, rawMultiDensity n a gaps v)
      (𝓝[>] 0) (𝓝 (1 : ℝ≥0∞)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (rawMultiDensity_integral n a ha gaps hgaps).symm
  calc
    _ = ∫⁻ v, liminf (fun a : ℝ ↦ rawMultiDensity n a gaps v) (𝓝[>] 0) :=
      lintegral_congr (fun v ↦ (hlim v).liminf_eq.symm)
    _ ≤ liminf (fun a : ℝ ↦ ∫⁻ v, rawMultiDensity n a gaps v) (𝓝[>] 0) :=
      lintegral_liminf_le (fun a ↦ measurable_rawMultiDensity n a gaps)
    _ = 1 := hm.liminf_eq

theorem entranceProduct_integral_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : (∫⁻ v, entranceProduct n gaps v) ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (entranceProduct_integral_le_one n gaps hgaps)

end PerronWright.BrownianPositiveBridgeMultiPointEntrance
