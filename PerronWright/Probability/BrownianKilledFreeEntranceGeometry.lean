import PerronWright.Probability.BrownianPositiveBridgeMultiPointEntrance
import PerronWright.Probability.BrownianEntranceConvolution

/-! # One-boundary entrance geometry of actual killed free tuples

The first killed transition is the only factor depending on the small
positive start. All remaining factors are the actual killed transitions.
The finite-coordinate reference measure is product Lebesgue measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFreeEntranceGeometry

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledSemigroup
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeMultiPointEntrance

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def freeCons (n : ℕ) (p : ℝ × FreeVector n) : FreeVector (n+1) := Fin.cons p.1 p.2

theorem continuous_freeCons (n : ℕ) : Continuous (freeCons n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [freeCons,Fin.cons_zero] using continuous_fst
  · simpa only [freeCons,Fin.cons_succ,Function.comp_def] using (continuous_apply j).comp continuous_snd

theorem volume_preserving_freeCons (n : ℕ) :
    MeasurePreserving (freeCons n)
      ((volume : Measure ℝ).prod (volume : Measure (FreeVector n))) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) 0).symm
  change MeasurePreserving (fun p : ℝ × FreeVector n ↦ (Fin.cons p.1 p.2 : FreeVector (n+1)))
    ((volume : Measure ℝ).prod (volume : Measure (FreeVector n))) volume
  simpa only [Measure.volume_eq_prod,volume_pi,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero',Equiv.coe_fn_mk,freeCons] using h

theorem lintegral_volume_freeCons (n : ℕ) {F : FreeVector (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ y : ℝ, ∫⁻ v : FreeVector n, F (freeCons n (y,v)) := by
  rw [← (volume_preserving_freeCons n).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (continuous_freeCons n).measurable).aemeasurable

theorem internalDensity_freeCons (n : ℕ) (gaps : ℕ → ℝ≥0) (y : ℝ) (v : FreeVector n) :
    internalDensity n gaps (freeCons n (y,v)) = jointDensity n y (fun j ↦ gaps (j+1)) v := by
  simp only [internalDensity,jointDensity,prependInitial,freeCons,Fin.cons_succ]

theorem jointDensity_lintegral_le_one (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n, 0 < gaps j) : (∫⁻ v, jointDensity n a gaps v) ≤ 1 := by
  cases n with
  | zero => simp only [jointDensity_zero,lintegral_one,volume_pi,Measure.pi_empty_univ,le_refl]
  | succ n =>
    have he : (∫⁻ v, jointDensity (n+1) a gaps v) = freeTupleLaw a gaps (n+1) univ := by
      rw [freeTupleLaw_eq_withDensity_all (n+1) (by omega) a gaps hgaps,
        withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [he,freeTupleLaw_eq_source]
    have hm : Measurable (fun f : Path ↦ fun i : Fin (n+1) ↦ a+f (sampleTime gaps (i.val+1))) :=
      measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)
    rw [Measure.map_apply hm MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : pathLaw univ = 1)

def entranceJoint (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  entrance (gaps 0) (v 0)*internalDensity n gaps v

theorem measurable_entranceJoint (n : ℕ) (gaps : ℕ → ℝ≥0) :
    Measurable (entranceJoint n gaps) :=
  ((measurable_entrance _).comp (measurable_pi_apply 0)).mul (measurable_internalDensity n gaps)

theorem entranceJoint_ne_top (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) :
    entranceJoint n gaps v ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (internalDensity_ne_top n gaps v)

theorem normalized_jointDensity_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hfirst : 0 < gaps 0) (v : FreeVector (n+1)) :
    Tendsto (fun a : ℝ ↦ jointDensity (n+1) a gaps v/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (entranceJoint n gaps v)) := by
  have h := ENNReal.Tendsto.mul_const
    (BrownianEntranceConvolution.normalized_density_tendsto (gaps 0) hfirst (v 0))
    (Or.inr (internalDensity_ne_top n gaps v))
  apply h.congr
  intro a
  rw [jointDensity_first_factor]
  simp only [div_eq_mul_inv]
  ring

end PerronWright.BrownianKilledFreeEntranceGeometry
