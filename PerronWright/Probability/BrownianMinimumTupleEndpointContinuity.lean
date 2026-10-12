import PerronWright.Probability.BrownianMinimumTupleEndpointGeometry

/-! # Genuine endpoint continuity for finite entrance tuples

The varying first entrance edge has a uniform integrable Gaussian
envelope before the fixed cutoff. The earlier actual killed chain has
mass at most one, while the final killed edge is uniformly bounded.
Together with the true passage-level source, these give an integrable
majorant and an actual endpoint limit for the full coupled tuple test.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTupleEndpointContinuity

open BrownianMinimumTupleEndpointGeometry BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFreeEntranceGeometry BrownianPositiveBridgeMultiPointEntrance
open BrownianKilledBoundaryEntrance BrownianPositiveBridgeGaussianBounds
open BrownianKilledGlobalEntranceTests BrownianMinimumWindowSurvivalBounds
open BrownianPositiveBridgeFiniteDimensionalDensity

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem passage_source_lintegral_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s) ≠ ⊤ := by
  have hfinite : (ENNReal.ofReal (Real.sqrt (T : ℝ)/Real.sqrt (2*Real.pi))*
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (timeMajorant T s)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)
  apply ne_top_of_le_ne_top hfinite
  rw [← lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [passage_level_mass s hs.1,← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs.1
  have hrem : 0 < Real.sqrt ((T : ℝ)-s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
  have hpi : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have he : 1/(Real.sqrt (2*Real.pi)*Real.sqrt s) =
      (Real.sqrt ((T : ℝ)-s)/Real.sqrt (2*Real.pi))*timeMajorant T s := by
    unfold timeMajorant
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (timeMajorant_nonneg T s)
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hs.1])) hpi.le

def stateEnvelope (n : ℕ) (times : Fin (n+2) → ℝ≥0) (b : ℝ≥0)
    (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ENNReal.ofReal (envelopeReal (times 0-b) (times (Fin.last (n+1))) (v 0))*
    internalDensity n (fixedGaps n times) v

theorem measurable_stateEnvelope (n : ℕ) (times : Fin (n+2) → ℝ≥0) (b : ℝ≥0) :
    Measurable (stateEnvelope n times b) :=
  (((measurable_envelopeReal _ _).comp (measurable_pi_apply 0)).ennreal_ofReal).mul
    (measurable_internalDensity n (fixedGaps n times))

theorem stateEnvelope_lintegral_ne_top (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0) :
    (∫⁻ v, stateEnvelope n times b v) ≠ ⊤ := by
  have hfirst : 0 < times 0 := (show 0 ≤ b from zero_le).trans_lt hb
  have hT : 0 < times (Fin.last (n+1)) :=
    hfirst.trans_le (hstrict.monotone (Fin.zero_le _))
  have he := (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (envelopeReal_nonneg (times 0-b) (times (Fin.last (n+1)))))).mp
      (integrable_envelopeReal _ _ hT).hasFiniteIntegral
  apply ne_top_of_le_ne_top he.ne
  rw [lintegral_volume_freeCons n (measurable_stateEnvelope n times b)]
  apply lintegral_mono
  intro y
  simp only [stateEnvelope,freeCons,Fin.cons_zero]
  simp_rw [show (Fin.cons y · : FreeVector n → FreeVector (n+1)) =
      (fun v ↦ freeCons n (y,v)) by rfl,internalDensity_freeCons]
  rw [lintegral_const_mul _ (BrownianKilledFiniteDimensionalDensityCoordinates.measurable_jointDensity
    n y (fun j ↦ fixedGaps n times (j+1)))]
  exact (mul_le_mul' le_rfl (jointDensity_lintegral_le_one n y _
    (fun j hj ↦ fixedGaps_positive n times hstrict hfirst (j+1) (by omega)))).trans_eq (mul_one _)

private def sourceBase (T : ℝ≥0) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) (T : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

private def sourceDensity (p : ℝ × ℝ) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.2 p.1

private theorem measurable_sourceDensity : Measurable sourceDensity :=
  BrownianHeatResolvent.measurable_joint_passageDensity.comp measurable_swap

private def fullIntegrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ)
    (q : (ℝ × ℝ) × FreeVector (n+1)) : ℝ≥0∞ :=
  sourceDensity q.1*(entranceJoint (n+1) (residualGaps n times q.1.1) (Fin.snoc q.2 (q.1.2+z))*
    ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.1.2,Fin.snoc q.2 (q.1.2+z))))

private theorem measurable_fullIntegrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ) :
    Measurable (fullIntegrand n times Φ z) := by
  change Measurable (fun q : (ℝ × ℝ) × FreeVector (n+1) ↦
    BrownianFirstPassageDensityGeometry.density q.1.2 q.1.1*
      (entranceJoint (n+1) (residualGaps n times q.1.1) (Fin.snoc q.2 (q.1.2+z))*
        ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.1.2,Fin.snoc q.2 (q.1.2+z)))))
  simpa only [Function.comp_def] using (measurable_joint_integrand n times Φ).comp
    (measurable_const.prodMk measurable_id :
      Measurable (fun q : (ℝ × ℝ) × FreeVector (n+1) ↦ (z,q)))

private theorem candidate_eq_reference (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ) :
    candidate n times Φ z = ∫⁻ q, fullIntegrand n times Φ z q
      ∂(sourceBase (times (Fin.last (n+1)))).prod volume := by
  rw [lintegral_prod _ (measurable_fullIntegrand n times Φ z).aemeasurable]
  have hi : Measurable (fun p : ℝ × ℝ ↦ ∫⁻ v, fullIntegrand n times Φ z (p,v)) :=
    (measurable_fullIntegrand n times Φ z).lintegral_prod_right'
  rw [sourceBase,lintegral_prod _ hi.aemeasurable]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro a
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

private def majorant (n : ℕ) (times : Fin (n+2) → ℝ≥0) (b : ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (q : (ℝ × ℝ) × FreeVector (n+1)) : ℝ≥0∞ :=
  sourceDensity q.1*stateEnvelope n times b q.2*
    (ENNReal.ofReal ((Real.sqrt (2*Real.pi*(fixedGaps n times (n+1) : ℝ)))⁻¹)*ENNReal.ofReal ‖Φ‖)

private theorem majorant_lintegral_ne_top (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    (∫⁻ q, majorant n times b Φ q
      ∂(sourceBase (times (Fin.last (n+1)))).prod volume) ≠ ⊤ := by
  have hstate := stateEnvelope_lintegral_ne_top n times hstrict b hb
  have hT : 0 < times (Fin.last (n+1)) :=
    ((show 0 ≤ b from zero_le).trans_lt hb).trans_le (hstrict.monotone (Fin.zero_le _))
  have hsource : (∫⁻ p, sourceDensity p ∂sourceBase (times (Fin.last (n+1)))) ≠ ⊤ := by
    rw [sourceBase,lintegral_prod _ measurable_sourceDensity.aemeasurable]
    exact passage_source_lintegral_ne_top _ hT
  let C : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2*Real.pi*(fixedGaps n times (n+1) : ℝ)))⁻¹)*
    ENNReal.ofReal ‖Φ‖
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hm : Measurable (fun q : (ℝ × ℝ) × FreeVector (n+1) ↦
      sourceDensity q.1*stateEnvelope n times b q.2*C) :=
    ((measurable_sourceDensity.comp measurable_fst).mul
      ((measurable_stateEnvelope n times b).comp measurable_snd)).mul_const C
  change (∫⁻ q, sourceDensity q.1*stateEnvelope n times b q.2*C
    ∂(sourceBase (times (Fin.last (n+1)))).prod volume) ≠ ⊤
  rw [lintegral_prod _ hm.aemeasurable]
  have he (p : ℝ × ℝ) : (∫⁻ v, sourceDensity p*stateEnvelope n times b v*C) =
      sourceDensity p*((∫⁻ v, stateEnvelope n times b v)*C) := by
    have hp : sourceDensity p ≠ ⊤ := ENNReal.ofReal_ne_top
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ hp,lintegral_mul_const' _ _ hC]
  simp_rw [he]
  rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hstate hC)]
  exact ENNReal.mul_ne_top hsource (ENNReal.mul_ne_top hstate hC)

private theorem fullIntegrand_bound (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m v, Φ (t,m,v) = 0)
    (z : ℝ) (q : (ℝ × ℝ) × FreeVector (n+1)) :
    fullIntegrand n times Φ z q ≤ majorant n times b Φ q := by
  by_cases hs : b ≤ Real.toNNReal q.1.1
  · simp only [fullIntegrand,hcut _ hs,ENNReal.ofReal_zero,mul_zero,zero_le]
  · have hsbelow : Real.toNNReal q.1.1 < b := lt_of_not_ge hs
    have hbefore := hsbelow.trans hb
    have hδ : 0 < times 0-b := tsub_pos_iff_lt.mpr hb
    have hδt : times 0-b ≤ residualGaps n times q.1.1 0 := by
      rw [residualGaps_zero]
      exact tsub_le_tsub_left hsbelow.le _
    have htT : residualGaps n times q.1.1 0 ≤ times (Fin.last (n+1)) := by
      rw [residualGaps_zero]
      exact tsub_le_self.trans (hstrict.monotone (Fin.zero_le _))
    have he : entrance (residualGaps n times q.1.1 0) (q.2 0) ≤
        ENNReal.ofReal (envelopeReal (times 0-b) (times (Fin.last (n+1))) (q.2 0)) := by
      apply ENNReal.ofReal_le_ofReal
      apply le_of_tendsto (densityReal_div_start_tendsto _ (hδ.trans_le hδt) (q.2 0))
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
        with a ha ha1
      exact densityReal_div_start_le_envelope a ha ha1.le _ _ _ hδ hδt htT _
    have hexit := residualGaps_internal n times hstrict q.1.1 hbefore (Fin.last n)
    simp only [Fin.val_last] at hexit
    have hnorm := Φ.norm_coe_le_norm (Real.toNNReal q.1.1,-q.1.2,Fin.snoc q.2 (q.1.2+z))
    rw [Real.norm_eq_abs] at hnorm
    have hΦ : ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.1.2,Fin.snoc q.2 (q.1.2+z))) ≤
        ENNReal.ofReal ‖Φ‖ := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hnorm)
    unfold fullIntegrand majorant
    rw [entranceJoint_append,entranceJoint,internalDensity_residual n times hstrict _ hbefore,hexit]
    have hD := density_le_prefactor (q.2 (Fin.last n)) (fixedGaps n times (n+1))
      (fixedGaps_positive n times hstrict ((show 0 ≤ b from zero_le).trans_lt hb) (n+1) (by omega))
        (q.1.2+z)
    calc
      _ ≤ sourceDensity q.1*((ENNReal.ofReal (envelopeReal (times 0-b)
          (times (Fin.last (n+1))) (q.2 0))*internalDensity n (fixedGaps n times) q.2)*
          ENNReal.ofReal ((Real.sqrt (2*Real.pi*(fixedGaps n times (n+1) : ℝ)))⁻¹)*ENNReal.ofReal ‖Φ‖) :=
        mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' (mul_le_mul' he le_rfl) hD) hΦ)
      _ = _ := by unfold stateEnvelope; ac_rfl

private theorem fullIntegrand_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z₀ : ℝ)
    (q : (ℝ × ℝ) × FreeVector (n+1)) :
    Tendsto (fun z : ℝ ↦ fullIntegrand n times Φ z q) (𝓝 z₀)
      (𝓝 (fullIntegrand n times Φ z₀ q)) := by
  have hD := (continuous_density_exit (q.2 (Fin.last n)) (residualGaps n times q.1.1 (n+1))).tendsto
    (q.1.2+z₀) |>.comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ q.1.2) (𝓝 z₀) (𝓝 q.1.2)).add tendsto_id)
  have hsnoc : Continuous (fun z : ℝ ↦ (Fin.snoc q.2 (q.1.2+z) : FreeVector (n+2))) := by
    simpa only [Function.comp_def,freeAppend] using
      (continuous_freeAppend (n+1)).comp
        (by fun_prop : Continuous (fun z : ℝ ↦ (q.2,q.1.2+z)))
  have hV : Continuous (fun z : ℝ ↦ (Real.toNNReal q.1.1,-q.1.2,
      (Fin.snoc q.2 (q.1.2+z) : FreeVector (n+2)))) :=
    continuous_const.prodMk (continuous_const.prodMk hsnoc)
  have hΦ := ENNReal.tendsto_ofReal (Φ.continuous.tendsto _ |>.comp (hV.tendsto z₀))
  have hJ := ENNReal.Tendsto.const_mul (a := entranceJoint n (residualGaps n times q.1.1) q.2) hD
    (Or.inr (entranceJoint_ne_top n _ _))
  have hprod := ENNReal.Tendsto.mul hJ (Or.inr ENNReal.ofReal_ne_top) hΦ
    (Or.inr (ENNReal.mul_ne_top (entranceJoint_ne_top n _ _) ENNReal.ofReal_ne_top))
  have h := ENNReal.Tendsto.const_mul (a := sourceDensity q.1) hprod (Or.inr ENNReal.ofReal_ne_top)
  simpa only [fullIntegrand,entranceJoint_append,Function.comp_def,id_eq] using h

theorem candidate_ne_top (n : ℕ) (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times)
    (b : ℝ≥0) (hb : b < times 0) (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m v, Φ (t,m,v) = 0) (z : ℝ) :
    candidate n times Φ z ≠ ⊤ := by
  rw [candidate_eq_reference]
  exact ne_top_of_le_ne_top (majorant_lintegral_ne_top n times hstrict b hb Φ)
    (lintegral_mono (fullIntegrand_bound n times hstrict b hb Φ hcut z))

theorem candidate_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times)
    (b : ℝ≥0) (hb : b < times 0) (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m v, Φ (t,m,v) = 0) (z₀ : ℝ) :
    Tendsto (candidate n times Φ) (𝓝 z₀) (𝓝 (candidate n times Φ z₀)) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (majorant n times b Φ) (Eventually.of_forall (measurable_fullIntegrand n times Φ))
      (Eventually.of_forall (fun z ↦ Eventually.of_forall
        (fullIntegrand_bound n times hstrict b hb Φ hcut z)))
          (majorant_lintegral_ne_top n times hstrict b hb Φ)
            (Eventually.of_forall (fullIntegrand_tendsto n times Φ z₀))
  simpa only [← candidate_eq_reference] using h

end PerronWright.BrownianMinimumTupleEndpointContinuity
