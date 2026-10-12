import PerronWright.Probability.BrownianMinimumTuplePinningGeometry
import PerronWright.Probability.BrownianMinimumTupleEndpointContinuity
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Actual endpoint-zero bridge original-coordinate density

The last free coordinate is the literal endpoint height above the minimum.
Appending that coordinate, translating it by the minimum depth, and
Tonelli give equality of all Borel endpoint-weighted densities. Genuine
continuity at endpoint zero identifies the actual pinned bridge law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTuplePinningLaw

open BrownianPathLaw BrownianFirstPassageBridgeLaw BrownianMinimumTuplePinningGeometry
open BrownianMinimumTupleEndpointGeometry BrownianMinimumTupleEndpointContinuity
open BrownianKilledFreeEntranceGeometry BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianMinimumFutureCoordinateMeasure BrownianMinimumEndpointPinningGeometry

private def base (n : ℕ) (times : Fin (n+2) → ℝ≥0) :
    Measure ((ℝ × ℝ) × FreeVector (n+1)) :=
  ((volume.restrict (Ioo (0 : ℝ) (times (Fin.last (n+1)) : ℝ))).prod
    (volume.restrict (Ioi (0 : ℝ)))).prod volume

private instance base_sFinite (n : ℕ) (times : Fin (n+2) → ℝ≥0) : SFinite (base n times) := by
  unfold base
  infer_instance

private def integrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ)
    (p : (ℝ × ℝ) × FreeVector (n+1)) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.1.2 p.1.1*
    (entranceJoint (n+1) (BrownianMinimumTupleEndpointGeometry.residualGaps n times p.1.1)
      (Fin.snoc p.2 (p.1.2+z))*
        ENNReal.ofReal (Φ (Real.toNNReal p.1.1,-p.1.2,Fin.snoc p.2 (p.1.2+z))))

private theorem measurable_integrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦ integrand n times Φ q.1 q.2) :=
  BrownianMinimumTupleEndpointGeometry.measurable_joint_integrand n times Φ

private theorem candidate_eq_base (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ) :
    candidate n times Φ z = ∫⁻ p, integrand n times Φ z p ∂base n times := by
  have hm : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦ integrand n times Φ z p) := by
    simpa only [Function.comp_def] using (measurable_integrand n times Φ).comp
      (measurable_const.prodMk measurable_id : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦ (z,p)))
  unfold candidate base
  rw [lintegral_prod _ hm.aemeasurable]
  rw [lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro a
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

theorem measurable_candidate (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) : Measurable (candidate n times Φ) := by
  have h := (measurable_integrand n times Φ).lintegral_prod_right' (ν := base n times)
  simpa only [← candidate_eq_base] using h

theorem translate_endpoint_original_density (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ s in Ioo 0 (times (Fin.last (n+1)) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+2),
        entranceJoint (n+1) (BrownianMinimumFutureCoordinateMeasure.residualGaps (n+1) times s) v*
          H (v (Fin.last (n+1))-a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))) =
      ∫⁻ z, H z*candidate n times Φ z := by
  have hm : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
      H q.1*integrand n times Φ q.1 q.2) :=
    (hH.comp measurable_fst).mul (measurable_integrand n times Φ)
  calc
    _ = ∫⁻ s in Ioo 0 (times (Fin.last (n+1)) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        ∫⁻ v : FreeVector (n+1), ∫⁻ z, H z*integrand n times Φ z ((s,a),v) := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro a
      have hF : Measurable (fun v : FreeVector (n+2) ↦
          entranceJoint (n+1) (BrownianMinimumFutureCoordinateMeasure.residualGaps (n+1) times s) v*
            H (v (Fin.last (n+1))-a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))) :=
        ((measurable_entranceJoint _ _).mul
          (hH.comp ((measurable_pi_apply _).sub_const _))).mul
          (Φ.continuous.measurable.comp
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal
      rw [lintegral_volume_freeAppend (n+1) hF]
      rw [← lintegral_const_mul' _ _ (show
        BrownianFirstPassageDensityGeometry.density a s ≠ ∞ from ENNReal.ofReal_ne_top)]
      apply lintegral_congr
      intro v
      have he := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ ↦ entranceJoint (n+1)
          (BrownianMinimumFutureCoordinateMeasure.residualGaps (n+1) times s) (Fin.snoc v y)*
            H (y-a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v y))) a
      simp only [freeAppend,Fin.snoc_last]
      rw [← he,← lintegral_const_mul' _ _ (show
        BrownianFirstPassageDensityGeometry.density a s ≠ ∞ from ENNReal.ofReal_ne_top)]
      apply lintegral_congr
      intro z
      simp only [integrand,add_comm z a,add_sub_cancel_left,
        BrownianMinimumFutureCoordinateMeasure.residualGaps,BrownianMinimumTupleEndpointGeometry.residualGaps]
      ac_rfl
    _ = ∫⁻ p, (∫⁻ z, H z*integrand n times Φ z p) ∂base n times := by
      unfold base
      rw [lintegral_prod _ hm.lintegral_prod_left'.aemeasurable]
      rw [lintegral_prod _ hm.lintegral_prod_left'.lintegral_prod_right'.aemeasurable]
    _ = ∫⁻ z, ∫⁻ p, H z*integrand n times Φ z p ∂base n times :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [candidate_eq_base]
      have hmz : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦ integrand n times Φ z p) := by
        simpa only [Function.comp_def] using (measurable_integrand n times Φ).comp
          (measurable_const.prodMk measurable_id : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦ (z,p)))
      exact lintegral_const_mul (H z) hmz

theorem volume_endpoint_weighted_original_density (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last (n+1)))
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, times 0 ≤ t → κ t = 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z*(gaussianPDF 0 (times (Fin.last (n+1))) z*
      BrownianMinimumTuplePinningGeometry.pinnedTest (n+1) times (weightedTest (n+1) κ Φ) z)) =
      ∫⁻ z, H z*candidate n times (weightedTest (n+1) κ Φ) z := by
  have he := actual_endpoint_weighted_original_density (n+1) times hstrict hT κ hκ hcut Φ H hH
  have hmH : Measurable (fun z : ℝ ↦ H z*
      BrownianMinimumTuplePinningGeometry.pinnedTest (n+1) times (weightedTest (n+1) κ Φ) z) :=
    hH.mul (BrownianMinimumTuplePinningGeometry.measurable_pinnedTest _ _ _)
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt hT),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hmH] at he
  have hleft : (∫⁻ z, gaussianPDF 0 (times (Fin.last (n+1))) z*
      (H z*BrownianMinimumTuplePinningGeometry.pinnedTest (n+1) times (weightedTest (n+1) κ Φ) z)) =
      ∫⁻ z, H z*(gaussianPDF 0 (times (Fin.last (n+1))) z*
        BrownianMinimumTuplePinningGeometry.pinnedTest (n+1) times (weightedTest (n+1) κ Φ) z) := by
    apply lintegral_congr
    intro z
    ac_rfl
  exact hleft.symm.trans (he.trans (translate_endpoint_original_density n times _ H hH))

private theorem lintegral_indicator_one_mul {B : Set ℝ} (hB : MeasurableSet B)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) z*F z) = ∫⁻ z in B, F z := by
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ B <;> simp [hz]

theorem ae_gaussian_pinnedTest_eq_candidate (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last (n+1)))
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, times 0 ≤ t → κ t = 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    (fun z ↦ gaussianPDF 0 (times (Fin.last (n+1))) z*
      BrownianMinimumTuplePinningGeometry.pinnedTest (n+1) times (weightedTest (n+1) κ Φ) z)
      =ᵐ[volume] candidate n times (weightedTest (n+1) κ Φ) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    ((measurable_gaussianPDF _ _).mul (BrownianMinimumTuplePinningGeometry.measurable_pinnedTest _ _ _))
    (measurable_candidate n times _)
  intro B hB _
  have he := volume_endpoint_weighted_original_density n times hstrict hT κ hκ hcut Φ
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
  simpa only [lintegral_indicator_one_mul hB,Pi.mul_apply] using he

theorem actual_pinned_original_coordinate_density (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0)
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, b ≤ t → κ t = 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    gaussianPDF 0 (times (Fin.last (n+1))) 0*
      (∫⁻ g, ENNReal.ofReal (weightedTest (n+1) κ Φ (originalTriple (n+1) times g))
        ∂pinnedLaw (times (Fin.last (n+1)))) =
      candidate n times (weightedTest (n+1) κ Φ) 0 := by
  let W := weightedTest (n+1) κ Φ
  have hW : ∀ p, 0 ≤ W p := weightedTest_nonneg (n+1) κ hκ Φ hΦ
  have hc : ∀ t, times 0 ≤ t → κ t = 0 := fun t ht ↦ hcut t (hb.le.trans ht)
  have hcW := weightedTest_timeCutoff (n+1) times κ hc Φ
  have hcWb : ∀ t : ℝ≥0, b ≤ t → ∀ a v, W (t,a,v) = 0 := by
    intro t ht a v
    change κ t*Φ (t,a,v) = 0
    rw [hcut t ht,zero_mul]
  have hT : 0 < times (Fin.last (n+1)) := (show 0 ≤ b from zero_le).trans_lt
    (hb.trans_le (hstrict.monotone (Fin.zero_le _)))
  have hfin : (∫⁻ g, ENNReal.ofReal (W (originalTriple (n+1) times g))
      ∂pinnedLaw (times (Fin.last (n+1)))) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖W‖))
    calc
      _ ≤ ∫⁻ _g : Path, ENNReal.ofReal ‖W‖ ∂pinnedLaw (times (Fin.last (n+1))) :=
        lintegral_mono (fun g ↦ ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (W.norm_coe_le_norm _)))
      _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
  have hd : Tendsto (gaussianPDF 0 (times (Fin.last (n+1)))) (𝓝 0)
      (𝓝 (gaussianPDF 0 (times (Fin.last (n+1))) 0)) := by
    exact (ENNReal.continuous_ofReal.comp (show Continuous (gaussianPDFReal 0 (times (Fin.last (n+1)))) from by
      unfold gaussianPDFReal
      fun_prop)).tendsto 0
  have hl := ENNReal.Tendsto.mul hd (Or.inr hfin)
    (BrownianMinimumTuplePinningGeometry.pinnedTest_tendsto (n+1) times hstrict hT W hW hcW)
    (Or.inr gaussianPDF_ne_top)
  exact eq_at_zero_of_ae_eq_of_tendsto hl (candidate_tendsto n times hstrict b hb W hcWb 0)
    (ae_gaussian_pinnedTest_eq_candidate n times hstrict hT κ hκ hc Φ)

end PerronWright.BrownianMinimumTuplePinningLaw
