import PerronWright.Probability.BrownianMinimumTupleEndpointContinuity
import PerronWright.Probability.BrownianEntranceKernelContinuity
import PerronWright.Probability.BrownianPassageBoundaryContraction

/-! # Genuine small-minimum-time finite-dimensional density limit

Symmetry of the actual final killed edge rewrites the true passage source
as the level-weighted passage law. Its proved boundary contraction gives
one half of the final entrance edge. A uniform first entrance envelope
and the actual earlier killed chain then justify the finite-state DCT.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTupleSmallTime

open BrownianMinimumTupleEndpointGeometry BrownianMinimumTupleEndpointContinuity
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFreeEntranceGeometry
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianKilledBoundaryEntrance BrownianEntranceKernelContinuity BrownianEntranceProductGeometry
open BrownianPassageWeightedScaling BrownianPassageBoundaryContraction
open BrownianPositiveKilledEndpoint

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private def pulledTest (n : ℕ) (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (v : FreeVector (n+1)) : (ℝ × ℝ) →ᵇ ℝ :=
  Φ.compContinuous ⟨fun q ↦ (Real.toNNReal q.1,-q.2,Fin.snoc v q.2),
    continuous_real_toNNReal.comp continuous_fst |>.prodMk
      (continuous_snd.neg.prodMk ((continuous_freeAppend (n+1)).comp
        (continuous_const.prodMk continuous_snd)))⟩

private def boundaryIntegral (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), weight s a*
    ((density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
      ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)))

private theorem boundaryIntegral_eq_weightedLaw (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) (v : FreeVector (n+1)) :
    boundaryIntegral n times Φ s v = ∫⁻ a,
      (density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
        ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) ∂weightedLaw s := by
  have hp : Measurable (fun a : ℝ ↦
      (density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
        ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a))) := by
    have hΦ : Measurable (fun a : ℝ ↦ ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a))) := by
      simpa only [pulledTest,BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk,Function.comp_def] using
        (((pulledTest n Φ v).continuous.measurable.comp
          (measurable_const.prodMk measurable_id : Measurable (fun a : ℝ ↦ (s,a)))).ennreal_ofReal)
    exact (measurable_normalized_density (fixedGaps n times (n+1)) (v (Fin.last n))).mul hΦ
  exact (lintegral_weightedLaw s _ hp).symm

private theorem measurable_joint_boundaryIntegral (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Measurable (fun q : ℝ × FreeVector (n+1) ↦ boundaryIntegral n times Φ q.1 q.2) := by
  have hv : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦
      (Fin.snoc q.1.2 q.2 : FreeVector (n+2))) := by
    simpa only [Function.comp_def,freeAppend] using
      (continuous_freeAppend (n+1)).measurable.comp
        (measurable_fst.snd.prodMk measurable_snd)
  have hΦ : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦
      ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.2,Fin.snoc q.1.2 q.2))) :=
    (Φ.continuous.measurable.comp
      (measurable_fst.fst.real_toNNReal.prodMk (measurable_snd.neg.prodMk hv))).ennreal_ofReal
  have hD : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦
      density q.2 (fixedGaps n times (n+1)) (q.1.2 (Fin.last n))) := by
    have hmap : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦
        (q.2,q.1.2 (Fin.last n))) := by fun_prop
    simpa only [Function.comp_def] using
      (BrownianPositiveKilledKernel.measurable_joint_density (fixedGaps n times (n+1))).comp hmap
  have hw : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦ weight q.1.1 q.2) := by
    have hmap : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦ (q.2,q.1.1)) := by fun_prop
    have hpass : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦
        BrownianFirstPassageDensityGeometry.density q.2 q.1.1) := by
      simpa only [Function.comp_def] using BrownianHeatResolvent.measurable_joint_passageDensity.comp hmap
    unfold weight
    exact (measurable_snd : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦ q.2)).ennreal_ofReal.mul
      hpass
  have hm : Measurable (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦ weight q.1.1 q.2*
      ((density q.2 (fixedGaps n times (n+1)) (q.1.2 (Fin.last n))/ENNReal.ofReal q.2)*
        ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.2,Fin.snoc q.1.2 q.2)))) :=
    hw.mul ((hD.div (measurable_snd : Measurable
      (fun q : (ℝ × FreeVector (n+1)) × ℝ ↦ q.2)).ennreal_ofReal).mul hΦ)
  exact hm.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

private theorem boundaryIntegral_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (v : FreeVector (n+1)) :
    Tendsto (fun s : ℝ ↦ boundaryIntegral n times Φ s v) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (1/2 : ℝ)*entrance (fixedGaps n times (n+1)) (v (Fin.last n))*
        ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) := by
  have h := actual_weighted_boundary_contraction (fixedGaps n times (n+1))
    (fixedGaps_positive n times hstrict hfirst (n+1) (by omega)) (v (Fin.last n)) (pulledTest n Φ v)
  have h' : Tendsto (fun s : ℝ ↦ ∫⁻ a,
      (density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
        ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) ∂weightedLaw s) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (1/2 : ℝ)*entrance (fixedGaps n times (n+1)) (v (Fin.last n))*
        ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) := by
    simpa only [pulledTest,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,Real.toNNReal_zero,neg_zero] using h
  exact h'.congr (fun s ↦ (boundaryIntegral_eq_weightedLaw n times Φ s v).symm)

private theorem boundaryIntegral_bound (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) (hs : 0 < s)
    (v : FreeVector (n+1)) :
    boundaryIntegral n times Φ s v ≤
      ENNReal.ofReal (boundaryBound (fixedGaps n times (n+1)))*ENNReal.ofReal ‖Φ‖*
        ENNReal.ofReal (1/2 : ℝ) := by
  rw [boundaryIntegral_eq_weightedLaw]
  have hbase : ∀ᵐ a ∂weightedLaw s, 0 < a := by
    rw [weightedLaw,ae_withDensity_iff (measurable_weight s)]
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun _ ha _ ↦ ha)
  have hb : ∀ᵐ a ∂weightedLaw s,
      (density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
        ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) ≤
          ENNReal.ofReal (boundaryBound (fixedGaps n times (n+1)))*ENNReal.ofReal ‖Φ‖ := by
    filter_upwards [hbase] with a ha
    have hn := Φ.norm_coe_le_norm (Real.toNNReal s,-a,Fin.snoc v a)
    rw [Real.norm_eq_abs] at hn
    exact mul_le_mul' (normalized_density_le_uniform a ha _
      (fixedGaps_positive n times hstrict hfirst (n+1) (by omega)) _)
        (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hn))
  exact (lintegral_mono_ae hb).trans_eq (by rw [lintegral_const,weightedLaw_mass s hs])

private def stateIntegrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  entrance (residualGaps n times s 0) (v 0)*internalDensity n (fixedGaps n times) v*
    boundaryIntegral n times Φ s v

private theorem measurable_joint_stateIntegrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Measurable (fun q : ℝ × FreeVector (n+1) ↦ stateIntegrand n times Φ q.1 q.2) :=
  (((measurable_joint_entranceNN.comp
    (((measurable_pi_apply 0).comp ((measurable_residualGaps n times).comp measurable_fst)).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))).mul
        ((measurable_internalDensity n (fixedGaps n times)).comp measurable_snd)).mul
          (measurable_joint_boundaryIntegral n times Φ))

def levelDensity (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+1),
    entranceJoint (n+1) (residualGaps n times s) (Fin.snoc v a)*
      ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a))

theorem measurable_levelDensity (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) : Measurable (levelDensity n times Φ) := by
  have hm := (BrownianMinimumTupleEndpointGeometry.measurable_joint_integrand n times Φ).comp
    (measurable_const.prodMk measurable_id :
      Measurable (fun q : (ℝ × ℝ) × FreeVector (n+1) ↦ ((0 : ℝ),q)))
  have hi := hm.lintegral_prod_right' (ν := (volume : Measure (FreeVector (n+1))))
  have h := hi.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  convert h using 1
  funext s
  apply lintegral_congr
  intro a
  simp only [Function.comp_def,add_zero]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

theorem levelDensity_eq_state_integral (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ)
    (hs : Real.toNNReal s < times 0) :
    levelDensity n times Φ s = ∫⁻ v : FreeVector (n+1),
      entrance (residualGaps n times s 0) (v 0)*internalDensity n (fixedGaps n times) v*
        (∫⁻ a, (density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) ∂weightedLaw s) := by
  simp_rw [← boundaryIntegral_eq_weightedLaw]
  change levelDensity n times Φ s = ∫⁻ v, stateIntegrand n times Φ s v
  have ht := fixedGaps_positive n times hstrict hfirst (n+1) (by omega)
  have hexit := residualGaps_internal n times hstrict s hs (Fin.last n)
  simp only [Fin.val_last] at hexit
  have hm : Measurable (fun p : ℝ × FreeVector (n+1) ↦
      BrownianFirstPassageDensityGeometry.density p.1 s*
        (entranceJoint (n+1) (residualGaps n times s) (Fin.snoc p.2 p.1)*
          ENNReal.ofReal (Φ (Real.toNNReal s,-p.1,Fin.snoc p.2 p.1)))) := by
    simpa only [Function.comp_def,add_zero] using
      (BrownianMinimumTupleEndpointGeometry.measurable_joint_integrand n times Φ).comp
        (by fun_prop : Measurable (fun p : ℝ × FreeVector (n+1) ↦
          ((0 : ℝ),((s,p.1),p.2))))
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ v : FreeVector (n+1),
        BrownianFirstPassageDensityGeometry.density a s*
          (entranceJoint (n+1) (residualGaps n times s) (Fin.snoc v a)*
            ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a))) := by
      apply lintegral_congr
      intro a
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ v : FreeVector (n+1), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          (entranceJoint (n+1) (residualGaps n times s) (Fin.snoc v a)*
            ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a))) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      unfold stateIntegrand
      rw [boundaryIntegral_eq_weightedLaw]
      rw [lintegral_weightedLaw]
      · have hcoef : entrance (residualGaps n times s 0) (v 0)*
            internalDensity n (fixedGaps n times) v ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (internalDensity_ne_top n _ v)
        rw [← lintegral_const_mul' _ _ hcoef]
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro a ha
        dsimp only
        rw [entranceJoint_append,entranceJoint,internalDensity_residual n times hstrict s hs,hexit,
          density_symm _ a _ ht]
        unfold weight
        have hc := ENNReal.div_mul_cancel (b := density a (fixedGaps n times (n+1)) (v (Fin.last n)))
          (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
        calc
          _ = (entrance (residualGaps n times s 0) (v 0)*internalDensity n (fixedGaps n times) v)*
              BrownianFirstPassageDensityGeometry.density a s*
                ((density a (fixedGaps n times (n+1)) (v (Fin.last n))/ENNReal.ofReal a)*
                  ENNReal.ofReal a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) := by rw [hc]; ac_rfl
          _ = _ := by ac_rfl
      · exact (measurable_normalized_density _ _).mul
          ((pulledTest n Φ v).continuous.measurable.comp
            (measurable_const.prodMk measurable_id)).ennreal_ofReal

private theorem stateIntegrand_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (v : FreeVector (n+1)) :
    Tendsto (fun s : ℝ ↦ stateIntegrand n times Φ s v) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (1/2 : ℝ)*entranceJoint n (fixedGaps n times) v*
        entrance (fixedGaps n times (n+1)) (v (Fin.last n))*ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) := by
  have hV : Tendsto (fun s : ℝ ↦ (times 0-Real.toNNReal s,v 0)) (𝓝[>] 0) (𝓝 (times 0,v 0)) := by
    have h := (by fun_prop : Continuous (fun s : ℝ ↦ (times 0-Real.toNNReal s,v 0))).tendsto 0
    simpa only [Real.toNNReal_zero,tsub_zero] using h.mono_left nhdsWithin_le_nhds
  have he := (continuousAt_joint_entrance (times 0,v 0) hfirst).tendsto.comp hV
  have hi := ENNReal.Tendsto.mul_const (b := internalDensity n (fixedGaps n times) v) he
    (Or.inr (internalDensity_ne_top n _ v))
  have h := ENNReal.Tendsto.mul hi
    (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top)) (boundaryIntegral_tendsto n times hstrict hfirst Φ v)
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (internalDensity_ne_top n _ v)))
  have h0 : fixedGaps n times 0 = times 0 := by
    unfold fixedGaps BrownianKilledFiniteDimensionalOrderedTimes.orderedGaps
      BrownianKilledFiniteDimensionalOrderedTimes.finiteTimeExtension
    simp
  simpa only [stateIntegrand,residualGaps_zero,entranceJoint,h0,Function.comp_def,entrance,
    mul_assoc,mul_comm,mul_left_comm] using h

private theorem stateIntegrand_bound (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (s : ℝ) (hs : 0 < s)
    (hshalf : Real.toNNReal s < times 0/2) (v : FreeVector (n+1)) :
    stateIntegrand n times Φ s v ≤ stateEnvelope n times (times 0/2) v*
      (ENNReal.ofReal (boundaryBound (fixedGaps n times (n+1)))*ENNReal.ofReal ‖Φ‖*
        ENNReal.ofReal (1/2 : ℝ)) := by
  have hhalf : times 0/2 < times 0 := by simpa using div_lt_self hfirst (by norm_num : (1 : ℝ≥0) < 2)
  have hδ : 0 < times 0-times 0/2 := tsub_pos_iff_lt.mpr hhalf
  have he := entrance_le_envelope (times 0-times 0/2) (times 0-Real.toNNReal s)
    (times (Fin.last (n+1))) hδ (tsub_le_tsub_left hshalf.le _)
      (tsub_le_self.trans (hstrict.monotone (Fin.zero_le _))) (v 0)
  unfold stateIntegrand stateEnvelope
  rw [residualGaps_zero]
  exact mul_le_mul' (mul_le_mul' he le_rfl) (boundaryIntegral_bound n times hstrict hfirst Φ s hs v)

theorem levelDensity_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Tendsto (levelDensity n times Φ) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (1/2 : ℝ)*∫⁻ v : FreeVector (n+1),
        entranceJoint n (fixedGaps n times) v*entrance (fixedGaps n times (n+1)) (v (Fin.last n))*
          ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) := by
  let C := ENNReal.ofReal (boundaryBound (fixedGaps n times (n+1)))*ENNReal.ofReal ‖Φ‖*
    ENNReal.ofReal (1/2 : ℝ)
  have hhalf : times 0/2 < times 0 := div_lt_self hfirst (by norm_num)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, Real.toNNReal s < times 0/2 := by
    have h : Tendsto Real.toNNReal (𝓝[>] (0 : ℝ)) (𝓝 (Real.toNNReal 0)) :=
      (continuous_real_toNNReal.tendsto 0).mono_left nhdsWithin_le_nhds
    exact h.eventually (eventually_lt_nhds (by simp only [Real.toNNReal_zero]; positivity))
  have hm (s : ℝ) : Measurable (stateIntegrand n times Φ s) := by
    simpa only [Function.comp_def] using (measurable_joint_stateIntegrand n times Φ).comp
      (measurable_const.prodMk measurable_id : Measurable (fun v : FreeVector (n+1) ↦ (s,v)))
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ᵐ v : FreeVector (n+1),
      stateIntegrand n times Φ s v ≤ stateEnvelope n times (times 0/2) v*C := by
    filter_upwards [self_mem_nhdsWithin,hsmall] with s hs hshalf
    exact Eventually.of_forall (stateIntegrand_bound n times hstrict hfirst Φ s hs hshalf)
  have hf : (∫⁻ v, stateEnvelope n times (times 0/2) v*C) ≠ ⊤ := by
    rw [lintegral_mul_const' _ _ hC]
    exact ENNReal.mul_ne_top (stateEnvelope_lintegral_ne_top n times hstrict _ hhalf) hC
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := (volume : Measure (FreeVector (n+1))))
    _ (Eventually.of_forall hm) hb hf
    (Eventually.of_forall (stateIntegrand_tendsto n times hstrict hfirst Φ))
  simp_rw [mul_assoc] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  apply (show Tendsto _ _ (𝓝 (ENNReal.ofReal (1/2 : ℝ)*∫⁻ v : FreeVector (n+1),
      entranceJoint n (fixedGaps n times) v*entrance (fixedGaps n times (n+1)) (v (Fin.last n))*
        ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) from by simpa only [mul_assoc] using h).congr'
  filter_upwards [hsmall] with s hs
  simpa only [stateIntegrand,boundaryIntegral_eq_weightedLaw] using
    (levelDensity_eq_state_integral n times hstrict hfirst Φ s (hs.trans hhalf)).symm

theorem levelDensity_limit_ne_top (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    (ENNReal.ofReal (1/2 : ℝ)*∫⁻ v : FreeVector (n+1),
      entranceJoint n (fixedGaps n times) v*entrance (fixedGaps n times (n+1)) (v (Fin.last n))*
        ENNReal.ofReal (Φ (0,0,Fin.snoc v 0))) ≠ ⊤ := by
  let C := ENNReal.ofReal (boundaryBound (fixedGaps n times (n+1)))*ENNReal.ofReal ‖Φ‖*
    ENNReal.ofReal (1/2 : ℝ)
  have hhalf : times 0/2 < times 0 := div_lt_self hfirst (by norm_num)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, Real.toNNReal s < times 0/2 := by
    have h : Tendsto Real.toNNReal (𝓝[>] (0 : ℝ)) (𝓝 (Real.toNNReal 0)) :=
      (continuous_real_toNNReal.tendsto 0).mono_left nhdsWithin_le_nhds
    exact h.eventually (eventually_lt_nhds (by simp only [Real.toNNReal_zero]; positivity))
  have hbound (v : FreeVector (n+1)) :
      ENNReal.ofReal (1/2 : ℝ)*entranceJoint n (fixedGaps n times) v*
        entrance (fixedGaps n times (n+1)) (v (Fin.last n))*ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)) ≤
          stateEnvelope n times (times 0/2) v*C := by
    apply le_of_tendsto (stateIntegrand_tendsto n times hstrict hfirst Φ v)
    filter_upwards [self_mem_nhdsWithin,hsmall] with s hs hshalf
    exact stateIntegrand_bound n times hstrict hfirst Φ s hs hshalf v
  have hf : (∫⁻ v, stateEnvelope n times (times 0/2) v*C) ≠ ⊤ := by
    rw [lintegral_mul_const' _ _ hC]
    exact ENNReal.mul_ne_top (stateEnvelope_lintegral_ne_top n times hstrict _ hhalf) hC
  have h := lintegral_mono (μ := (volume : Measure (FreeVector (n+1)))) hbound
  simp_rw [mul_assoc] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact ne_top_of_le_ne_top hf (by simpa only [mul_assoc] using h)

end PerronWright.BrownianMinimumTupleSmallTime
