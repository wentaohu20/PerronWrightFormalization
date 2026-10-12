import PerronWright.Probability.BrownianMinimumFutureCoordinateMeasure
import PerronWright.Probability.BrownianMinimumEndpointPinningGeometry

/-! # Actual bridge endpoint disintegration for original minimum coordinates

A literal continuous cutoff before the first observation determines the
actual weighted coordinate law. The independent bridge--Gaussian endpoint
representation and the proved minimum continuity give genuine endpoint
test disintegration and endpoint-zero continuity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTuplePinningGeometry

open BrownianPathLaw ContinuousPathLeastMinimum BrownianMinimumFutureCoordinates
open BrownianMinimumFutureCoordinateDensity BrownianMinimumFutureCoordinateMeasure
open BrownianFirstPassageBridgeLaw BrownianBridgeMinimumEndpointContinuity
open BrownianMinimumEndpointPinningGeometry BrownianKilledFreeEntranceGeometry
open BrownianKilledFiniteDimensionalDensityCoordinates ContinuousPathMinimumFutureBandAverage

def weightedTest (n : ℕ) (κ : ℝ≥0 →ᵇ ℝ)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ :=
  (κ.compContinuous ⟨Prod.fst,continuous_fst⟩)*Φ

theorem weightedTest_nonneg (n : ℕ) (κ : ℝ≥0 →ᵇ ℝ)
    (hκ : ∀ t, 0 ≤ κ t) (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ)
    (hΦ : ∀ p, 0 ≤ Φ p) : ∀ p, 0 ≤ weightedTest n κ Φ p :=
  fun p ↦ mul_nonneg (hκ p.1) (hΦ p)

theorem weightedTest_timeCutoff (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (κ : ℝ≥0 →ᵇ ℝ) (hcut : ∀ t, times 0 ≤ t → κ t = 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) :
    ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, weightedTest n κ Φ (t,a,v) = 0 := by
  intro t ht a v
  change κ t*Φ (t,a,v) = 0
  rw [hcut t ht,zero_mul]

theorem originalTriple_stoppedPath (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (f : Path) :
    originalTriple n times (BrownianEndpointDriftTilt.stoppedPath (times (Fin.last n)) f) =
      originalTriple n times f := by
  have he := minimumTriple_stoppedPath (times (Fin.last n)) f
  have ht := congrArg Prod.fst he
  have hv := congrArg (fun p : ℝ≥0 × ℝ × ℝ ↦ p.2.1) he
  change ContinuousPathLeastMinimum.leastMinimizer _ _ = _ at ht
  change ContinuousPathLeastMinimum.minimumValue _ _ = _ at hv
  unfold originalTriple
  rw [ht,hv]
  congr 2
  funext i
  rw [BrownianEndpointDriftTilt.stoppedPath_eval,min_eq_left
    (hstrict.monotone (Fin.le_last i))]
  rfl

def pinnedTest (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (Φ (originalTriple n times
    (reconstruct (times (Fin.last n)) (g,z)))) ∂pinnedLaw (times (Fin.last n))

theorem measurable_pinnedTest (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) : Measurable (pinnedTest n times Φ) := by
  have hm : Measurable (fun p : ℝ × Path ↦ ENNReal.ofReal (Φ (originalTriple n times
      (reconstruct (times (Fin.last n)) (p.2,p.1))))) :=
    (Φ.continuous.measurable.comp ((measurable_originalTriple n times).comp
      ((measurable_reconstruct _).comp measurable_swap))).ennreal_ofReal
  exact hm.lintegral_prod_right'

private theorem integral_pinnedTest (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) (z : ℝ) :
    ENNReal.ofReal (∫ g, Φ (originalTriple n times
      (reconstruct (times (Fin.last n)) (g,z))) ∂pinnedLaw (times (Fin.last n))) =
      pinnedTest n times Φ z := by
  have hm : AEStronglyMeasurable (fun g : Path ↦ Φ (originalTriple n times
      (reconstruct (times (Fin.last n)) (g,z)))) (pinnedLaw (times (Fin.last n))) :=
    (Φ.continuous.measurable.comp ((measurable_originalTriple n times).comp
      ((measurable_reconstruct _).comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
  exact ofReal_integral_eq_lintegral_ofReal
    ((integrable_const ‖Φ‖).mono' hm (Eventually.of_forall (fun g ↦ Φ.norm_coe_le_norm _)))
    (Eventually.of_forall (fun g ↦ hΦ _))

theorem pinnedTest_tendsto (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n))
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) :
    Tendsto (pinnedTest n times Φ) (𝓝 0)
      (𝓝 (∫⁻ g, ENNReal.ofReal (Φ (originalTriple n times g))
        ∂pinnedLaw (times (Fin.last n)))) := by
  have ht := pinned_minimum_test_tendsto (times (Fin.last n)) hT (coordinateTest n times Φ)
  simp_rw [coordinateTest_minimumPoint_of_support n times hstrict _ Φ hcut] at ht
  have he : ENNReal.ofReal (∫ g, Φ (originalTriple n times g) ∂pinnedLaw (times (Fin.last n))) =
      ∫⁻ g, ENNReal.ofReal (Φ (originalTriple n times g)) ∂pinnedLaw (times (Fin.last n)) := by
    exact ofReal_integral_eq_lintegral_ofReal
      ((integrable_const ‖Φ‖).mono'
        (Φ.continuous.measurable.comp (measurable_originalTriple n times)).aestronglyMeasurable
        (Eventually.of_forall (fun g ↦ Φ.norm_coe_le_norm _)))
      (Eventually.of_forall (fun g ↦ hΦ _))
  have h := ENNReal.continuous_ofReal.tendsto _ |>.comp ht
  change Tendsto (fun z ↦ ENNReal.ofReal (∫ g, Φ (originalTriple n times
    (reconstruct (times (Fin.last n)) (g,z))) ∂pinnedLaw (times (Fin.last n)))) _
      (𝓝 (ENNReal.ofReal (∫ g, Φ (originalTriple n times g) ∂pinnedLaw (times (Fin.last n))))) at h
  rw [he] at h
  exact h.congr (integral_pinnedTest n times Φ hΦ)

theorem actual_endpoint_weighted_original_density (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n))
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, times 0 ≤ t → κ t = 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z*pinnedTest n times (weightedTest n κ Φ) z
      ∂gaussianReal 0 (times (Fin.last n))) =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*∫⁻ v,
          entranceJoint n (residualGaps n times s) v*H (v (Fin.last n)-a)*
            ENNReal.ofReal (weightedTest n κ Φ (Real.toNNReal s,-a,v)) := by
  let T := times (Fin.last n)
  let W := weightedTest n κ Φ
  let Ψ : (ℝ≥0 × ℝ × FreeVector (n+1)) → ℝ≥0∞ :=
    fun p ↦ H (p.2.1+p.2.2 (Fin.last n))*ENNReal.ofReal (Φ p)
  have hΨ : Measurable Ψ :=
    (hH.comp (measurable_snd.fst.add ((measurable_pi_apply (Fin.last n)).comp
      measurable_snd.snd))).mul Φ.continuous.measurable.ennreal_ofReal
  have hp : Measurable (fun p : Path × ℝ ↦ H p.2*
      ENNReal.ofReal (W (originalTriple n times (reconstruct T p)))) :=
    (hH.comp measurable_snd).mul (W.continuous.measurable.comp
      ((measurable_originalTriple n times).comp (measurable_reconstruct T))).ennreal_ofReal
  have hj : Measurable (fun f : Path ↦ (BrownianBridgeAreaTiltPathLaw.stoppedBridgePath T f,f T)) :=
    (BrownianBridgeAreaTiltPathLaw.measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  calc
    _ = ∫⁻ z, ∫⁻ g, H z*ENNReal.ofReal (W (originalTriple n times (reconstruct T (g,z))))
        ∂pinnedLaw T ∂gaussianReal 0 T := by
      apply lintegral_congr
      intro z
      exact (lintegral_const_mul _ (W.continuous.measurable.comp
        ((measurable_originalTriple n times).comp ((measurable_reconstruct T).comp
          (measurable_id.prodMk measurable_const)))).ennreal_ofReal).symm
    _ = ∫⁻ p, H p.2*ENNReal.ofReal (W (originalTriple n times (reconstruct T p)))
        ∂(pinnedLaw T).prod (gaussianReal 0 T) := (lintegral_prod_symm _ hp.aemeasurable).symm
    _ = ∫⁻ f, H (f T)*ENNReal.ofReal (W (originalTriple n times f)) ∂pathLaw := by
      rw [← bridge_endpoint_jointLaw T hT,lintegral_map hp hj]
      apply lintegral_congr
      intro f
      rw [reconstruct_bridge_endpoint,originalTriple_stoppedPath n times hstrict]
    _ = ∫⁻ f, ENNReal.ofReal (κ (leastMinimizer T f))*Ψ (originalTriple n times f) ∂pathLaw := by
      apply lintegral_congr
      intro f
      simp only [Ψ,W,weightedTest,BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,originalTriple]
      rw [show minimumValue T f+(f T-minimumValue T f) = f T by ring,
        ENNReal.ofReal_mul (hκ _)]
      ac_rfl
    _ = _ := by
      rw [actual_weighted_borel_density n times hstrict hT κ hκ hcut Ψ hΨ]
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro a
      congr 1
      apply lintegral_congr
      intro v
      simp only [Ψ,neg_add_eq_sub,weightedTest,BoundedContinuousFunction.mul_apply,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,ENNReal.ofReal_mul (hκ _)]
      ac_rfl

end PerronWright.BrownianMinimumTuplePinningGeometry
