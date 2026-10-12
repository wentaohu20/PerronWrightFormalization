import PerronWright.Probability.BrownianMinimumTuplePinningLaw
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Actual pinned original-coordinate law for all Borel tests

Equality of the genuine supported continuous tests determines a finite
weighted bridge measure. This extends endpoint-zero pinning to arbitrary
nonnegative Borel tests, including literal small minimum-time events.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTuplePinningMeasure

open BrownianPathLaw ContinuousPathLeastMinimum BrownianFirstPassageBridgeLaw
open BrownianMinimumTuplePinningGeometry BrownianMinimumTuplePinningLaw
open BrownianMinimumFutureCoordinateMeasure BrownianMinimumTupleEndpointGeometry
open BrownianKilledFreeEntranceGeometry BrownianKilledFiniteDimensionalDensityCoordinates

def actualLaw (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measure (ℝ≥0 × ℝ × FreeVector (n+2)) :=
  ((pinnedLaw (times (Fin.last (n+1)))).withDensity (fun g ↦
    gaussianPDF 0 (times (Fin.last (n+1))) 0*
      ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g)))).map
        (originalTriple (n+1) times)

instance actualLaw_isFinite (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    IsFiniteMeasure (actualLaw n times κ) := by
  have hfin : (∫⁻ g, gaussianPDF 0 (times (Fin.last (n+1))) 0*
      ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g))
      ∂pinnedLaw (times (Fin.last (n+1)))) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (show
      gaussianPDF 0 (times (Fin.last (n+1))) 0 ≠ ∞ from gaussianPDF_ne_top)
      (ENNReal.ofReal_ne_top (r := ‖κ‖)))
    calc
      _ ≤ ∫⁻ _g : Path, gaussianPDF 0 (times (Fin.last (n+1))) 0*ENNReal.ofReal ‖κ‖
          ∂pinnedLaw (times (Fin.last (n+1))) := lintegral_mono (fun g ↦ mul_le_mul' le_rfl
            (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (κ.norm_coe_le_norm _))))
      _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
  let := isFiniteMeasure_withDensity hfin
  unfold actualLaw
  infer_instance

def referenceMeasure (n : ℕ) (times : Fin (n+2) → ℝ≥0) :
    Measure ((ℝ × ℝ) × FreeVector (n+1)) :=
  ((volume.restrict (Ioo (0 : ℝ) (times (Fin.last (n+1)) : ℝ))).prod
    (volume.restrict (Ioi (0 : ℝ)))).prod volume

def encode (n : ℕ) (p : (ℝ × ℝ) × FreeVector (n+1)) : ℝ≥0 × ℝ × FreeVector (n+2) :=
  (Real.toNNReal p.1.1,-p.1.2,Fin.snoc p.2 p.1.2)

theorem measurable_encode (n : ℕ) : Measurable (encode n) := by
  have hv : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦
      (Fin.snoc p.2 p.1.2 : FreeVector (n+2))) := by
    simpa only [Function.comp_def,freeAppend] using (continuous_freeAppend (n+1)).measurable.comp
      (measurable_snd.prodMk measurable_fst.snd)
  exact measurable_fst.fst.real_toNNReal.prodMk (measurable_fst.snd.neg.prodMk hv)

def jointDensity (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ)
    (p : (ℝ × ℝ) × FreeVector (n+1)) : ℝ≥0∞ :=
  BrownianFirstPassageDensityGeometry.density p.1.2 p.1.1*
    entranceJoint (n+1) (BrownianMinimumTupleEndpointGeometry.residualGaps n times p.1.1)
      (Fin.snoc p.2 p.1.2)*ENNReal.ofReal (κ (Real.toNNReal p.1.1))

theorem measurable_jointDensity (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measurable (jointDensity n times κ) := by
  have hv : Measurable (fun p : (ℝ × ℝ) × FreeVector (n+1) ↦
      (Fin.snoc p.2 p.1.2 : FreeVector (n+2))) := by
    simpa only [Function.comp_def,freeAppend] using (continuous_freeAppend (n+1)).measurable.comp
      (measurable_snd.prodMk measurable_fst.snd)
  exact ((BrownianHeatResolvent.measurable_joint_passageDensity.comp
    (measurable_fst.snd.prodMk measurable_fst.fst)).mul
      ((BrownianMinimumTupleEndpointGeometry.measurable_joint_entranceJoint (n+1)).comp
        (((BrownianMinimumTupleEndpointGeometry.measurable_residualGaps n times).comp
          measurable_fst.fst).prodMk hv))).mul
      (κ.continuous.measurable.comp measurable_fst.fst.real_toNNReal).ennreal_ofReal

def candidateLaw (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ) :
    Measure (ℝ≥0 × ℝ × FreeVector (n+2)) :=
  ((referenceMeasure n times).withDensity (jointDensity n times κ)).map (encode n)

theorem lintegral_candidateLaw (n : ℕ) (times : Fin (n+2) → ℝ≥0) (κ : ℝ≥0 →ᵇ ℝ)
    (Ψ : (ℝ≥0 × ℝ × FreeVector (n+2)) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ q, Ψ q ∂candidateLaw n times κ) =
      ∫⁻ s in Ioo 0 (times (Fin.last (n+1)) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+1),
          entranceJoint (n+1) (BrownianMinimumTupleEndpointGeometry.residualGaps n times s)
            (Fin.snoc v a)*ENNReal.ofReal (κ (Real.toNNReal s))*Ψ (Real.toNNReal s,-a,Fin.snoc v a) := by
  have hm := (measurable_jointDensity n times κ).mul (hΨ.comp (measurable_encode n))
  rw [candidateLaw,lintegral_map hΨ (measurable_encode n)]
  change (∫⁻ p, (Ψ ∘ encode n) p ∂(referenceMeasure n times).withDensity (jointDensity n times κ)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_jointDensity n times κ)
    (hΨ.comp (measurable_encode n)),referenceMeasure,lintegral_prod _ hm.aemeasurable,
    lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro a
  simp only [jointDensity,encode,Pi.mul_apply,Function.comp_apply,mul_assoc]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

theorem actualLaw_eq_candidateLaw (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0)
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, b ≤ t → κ t = 0) :
    actualLaw n times κ = candidateLaw n times κ := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let F : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ :=
    ⟨⟨fun p ↦ (f p : ℝ),NNReal.continuous_coe.comp f.continuous⟩,f.map_bounded'⟩
  have hF : ∀ p, 0 ≤ F p := fun p ↦ (f p).coe_nonneg
  have he := actual_pinned_original_coordinate_density n times hstrict b hb κ hκ hcut F hF
  have hd : Measurable (fun g : Path ↦ gaussianPDF 0 (times (Fin.last (n+1))) 0*
      ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g))) :=
    measurable_const.mul (κ.continuous.measurable.comp (measurable_leastMinimizer _)).ennreal_ofReal
  rw [actualLaw,lintegral_map f.continuous.measurable.coe_nnreal_ennreal
    (measurable_originalTriple (n+1) times)]
  change (∫⁻ g, ((fun q ↦ (f q : ℝ≥0∞)) ∘ originalTriple (n+1) times) g
    ∂(pinnedLaw (times (Fin.last (n+1)))).withDensity
      (fun g ↦ gaussianPDF 0 (times (Fin.last (n+1))) 0*
        ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g)))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hd
    (f.continuous.measurable.coe_nnreal_ennreal.comp (measurable_originalTriple (n+1) times))]
  simp only [Pi.mul_apply,Function.comp_apply,mul_assoc]
  rw [lintegral_const_mul' _ _ gaussianPDF_ne_top,
    lintegral_candidateLaw n times κ _ f.continuous.measurable.coe_nnreal_ennreal]
  simpa only [F,weightedTest,BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.compContinuous_apply,BoundedContinuousFunction.coe_mk,
    ContinuousMap.coe_mk,originalTriple,ENNReal.ofReal_mul (hκ _),ENNReal.ofReal_coe_nnreal,
    candidate,add_zero,mul_assoc] using he

theorem actual_pinned_weighted_borel_density (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (b : ℝ≥0) (hb : b < times 0)
    (κ : ℝ≥0 →ᵇ ℝ) (hκ : ∀ t, 0 ≤ κ t) (hcut : ∀ t, b ≤ t → κ t = 0)
    (Ψ : (ℝ≥0 × ℝ × FreeVector (n+2)) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    gaussianPDF 0 (times (Fin.last (n+1))) 0*
      (∫⁻ g, ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g))*
        Ψ (originalTriple (n+1) times g) ∂pinnedLaw (times (Fin.last (n+1)))) =
      ∫⁻ s in Ioo 0 (times (Fin.last (n+1)) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+1),
          entranceJoint (n+1) (BrownianMinimumTupleEndpointGeometry.residualGaps n times s)
            (Fin.snoc v a)*ENNReal.ofReal (κ (Real.toNNReal s))*Ψ (Real.toNNReal s,-a,Fin.snoc v a) := by
  have hd : Measurable (fun g : Path ↦ gaussianPDF 0 (times (Fin.last (n+1))) 0*
      ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g))) :=
    measurable_const.mul (κ.continuous.measurable.comp (measurable_leastMinimizer _)).ennreal_ofReal
  rw [← lintegral_const_mul' _ _ gaussianPDF_ne_top]
  simp only [← mul_assoc]
  change (∫⁻ g, ((fun g ↦ gaussianPDF 0 (times (Fin.last (n+1))) 0*
      ENNReal.ofReal (κ (leastMinimizer (times (Fin.last (n+1))) g)))*
        (Ψ ∘ originalTriple (n+1) times)) g ∂pinnedLaw (times (Fin.last (n+1)))) = _
  rw [← lintegral_withDensity_eq_lintegral_mul _ hd
    (hΨ.comp (measurable_originalTriple (n+1) times))]
  simp only [Function.comp_apply]
  rw [← lintegral_map hΨ (measurable_originalTriple (n+1) times)]
  change (∫⁻ p, Ψ p ∂actualLaw n times κ) = _
  rw [actualLaw_eq_candidateLaw n times hstrict b hb κ hκ hcut,
    lintegral_candidateLaw n times κ Ψ hΨ]

end PerronWright.BrownianMinimumTuplePinningMeasure
