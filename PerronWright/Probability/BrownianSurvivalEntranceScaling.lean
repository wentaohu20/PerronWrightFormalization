import PerronWright.Probability.BrownianKilledAreaScalingGeometry
import PerronWright.Probability.BrownianKilledFreeEntranceNonnegativeTests

/-! # Actual survival entrance scaling and relative-time tests

The finite measures are literal normalized restrictions of Brownian path
law. Whole-path scaling is proved before taking any entrance limit. Thus
relative-time observations have the already proved genuine free entrance
limit, without a meander law or a path convergence premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianSurvivalEntranceScaling

open BrownianPathLaw BrownianPathDilationLaw ContinuousPathFirstPassage
open BrownianKilledAreaScalingGeometry BrownianKilledFreeEntranceTests
open BrownianKilledFreeEntranceNonnegativeTests
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalDensityCoordinates

def normalizedSurvivalLaw (delta : ℝ) (T : ℝ≥0) : Measure Path :=
  (ENNReal.ofReal delta)⁻¹ • pathLaw.restrict (survival (-delta) T)

theorem actual_survival_dilation (c T : ℝ≥0) (hc : 0 < c) (delta : ℝ) :
    (pathLaw.restrict (survival (-(delta/Real.sqrt (c : ℝ))) T)).map (brownianDilation c) =
      pathLaw.restrict (survival (-delta) (c*T)) := by
  have hs : (brownianDilation c) ⁻¹' survival (-delta) (c*T) =
      survival (-(delta/Real.sqrt (c : ℝ))) T := by
    ext f
    have h := survival_dilatePath_scaled_duration (-(delta/Real.sqrt (c : ℝ))) c T hc
      (Real.sqrt (c : ℝ)) (Real.sqrt_pos.mpr hc) f
    have he : Real.sqrt (c : ℝ)*(-(delta/Real.sqrt (c : ℝ))) = -delta := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hc)]
    simpa only [he,brownianDilation,mem_preimage] using h
  rw [← hs,← Measure.restrict_map (measurable_brownianDilation c)
    (measurableSet_survival (-delta) (c*T)),pathLaw_brownianDilation c hc]

theorem actual_survival_scaled_lintegral (c T : ℝ≥0) (hc : 0 < c) (delta : ℝ)
    {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f in survival (-delta) (c*T), F f ∂pathLaw) =
      ∫⁻ g in survival (-(delta/Real.sqrt (c : ℝ))) T, F (brownianDilation c g) ∂pathLaw := by
  rw [← actual_survival_dilation c T hc delta,
    lintegral_map hF (measurable_brownianDilation c)]

theorem normalizedSurvivalLaw_duration_scaling (c T : ℝ≥0) (hc : 0 < c) (delta : ℝ) :
    normalizedSurvivalLaw delta (c*T) = (ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹ •
      (normalizedSurvivalLaw (delta/Real.sqrt (c : ℝ)) T).map (brownianDilation c) := by
  rw [normalizedSurvivalLaw,normalizedSurvivalLaw,Measure.map_smul,
    actual_survival_dilation c T hc delta,smul_smul]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (x := delta) (y := Real.sqrt (c : ℝ)) (Real.sqrt_pos.mpr hc)]
  rw [ENNReal.inv_div (a := ENNReal.ofReal delta) (b := ENNReal.ofReal (Real.sqrt (c : ℝ)))
    (Or.inl ENNReal.ofReal_ne_top)
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hc)))]
  simp only [div_eq_mul_inv]
  rw [← mul_assoc,ENNReal.inv_mul_cancel (a := ENNReal.ofReal (Real.sqrt (c : ℝ)))
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hc)) ENNReal.ofReal_ne_top,one_mul]

theorem positive_scale_parameter_tendsto (c : ℝ≥0) (hc : 0 < c) :
    Tendsto (fun delta : ℝ ↦ delta/Real.sqrt (c : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div,id_eq] using
    (show Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) from
      tendsto_id.mono_left nhdsWithin_le_nhds).div_const (Real.sqrt (c : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with delta hd
    exact div_pos hd (Real.sqrt_pos.mpr hc)

theorem actual_relative_ordered_test_tendsto (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (c : ℝ≥0) (hc : 0 < c) (G : FreeVector (n+1) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    Tendsto (fun delta : ℝ ↦
      (∫⁻ f in survival (-delta) (c*times (Fin.last (n+1))),
        ENNReal.ofReal (G (fun i : Fin (n+1) ↦
          f (c*times i.succ)/Real.sqrt (c : ℝ))) ∂pathLaw)/ENNReal.ofReal delta)
      (𝓝[>] 0)
      (𝓝 ((ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹ *
        ∫⁻ v, ENNReal.ofReal (G v)
          ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  let GG : (ℝ × FreeVector (n+1)) →ᵇ ℝ :=
    G.compContinuous ⟨Prod.snd,continuous_snd⟩
  have hbase := actual_unshifted_ordered_nonnegative_test_tendsto
    n times hstrict hzero GG (fun p ↦ hG p.2)
  have ht := ENNReal.Tendsto.const_mul
    (a := (ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹)
    (hbase.comp (positive_scale_parameter_tendsto c hc))
    (Or.inr (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hc))))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hd
  have hm : Measurable (fun f : Path ↦ ENNReal.ofReal (G (fun i : Fin (n+1) ↦
      f (c*times i.succ)/Real.sqrt (c : ℝ)))) :=
    (G.continuous.measurable.comp (measurable_pi_lambda _
      (fun i ↦ (continuous_eval (c*times i.succ)).measurable.div_const _))).ennreal_ofReal
  have he : (fun f : Path ↦ ENNReal.ofReal (G (fun i : Fin (n+1) ↦
      brownianDilation c f (c*times i.succ)/Real.sqrt (c : ℝ)))) =
      fun f ↦ ENNReal.ofReal (G (fun i : Fin (n+1) ↦ f (times i.succ))) := by
    funext f
    congr 1
    congr 1
    funext i
    rw [brownianDilation,dilatePath_eval_scaled_duration c _ hc]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.mpr hc))
  rw [actual_survival_scaled_lintegral c _ hc delta hm,he]
  simp only [GG,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,Function.comp_def]
  rw [ENNReal.ofReal_div_of_pos (x := delta) (y := Real.sqrt (c : ℝ)) (Real.sqrt_pos.mpr hc)]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (a := ENNReal.ofReal delta)
    (b := (ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹)
    (Or.inr (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hc))))
    (Or.inl ENNReal.ofReal_ne_top)]
  simp only [inv_inv]
  have hcancel := ENNReal.inv_mul_cancel (a := ENNReal.ofReal (Real.sqrt (c : ℝ)))
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hc)) ENNReal.ofReal_ne_top
  calc
    _ = ((ENNReal.ofReal (Real.sqrt (c : ℝ)))⁻¹ * ENNReal.ofReal (Real.sqrt (c : ℝ))) *
        ((∫⁻ f in survival (-(delta*(Real.sqrt (c : ℝ))⁻¹)) (times (Fin.last (n+1))),
          ENNReal.ofReal (G (fun i : Fin (n+1) ↦ f (times i.succ))) ∂pathLaw) *
            (ENNReal.ofReal delta)⁻¹) := by ac_rfl
    _ = _ := by rw [hcancel,one_mul]

end PerronWright.BrownianSurvivalEntranceScaling
