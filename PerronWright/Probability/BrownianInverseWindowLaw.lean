import PerronWright.Probability.BrownianArbitraryWindowLaw
import PerronWright.Probability.BrownianInverseSizeLaw
import PerronWright.Probability.InverseWindowSizeRescaling

/-! # Actual inverse-dilated Brownian windows and global test laws

Both laws are literal pushforwards of the actual full Brownian process.
Compact-support test vectors agree exactly with the transported closed
window law. No graph convergence or Brownian identification is assumed.
-/

open MeasureTheory Set
open scoped Classical CompactlySupported
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianInverseWindowLaw

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague GlobalPointSizeRescaling
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking
open CompactGlobalTestLawLimit BrownianInverseSizeLaw InverseWindowSizeRescaling

def law (lambda a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (ha : 0 < a) (hab : a ≤ b) : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  (BrownianArbitraryWindowLaw.law lambda (c*a) (c*b) R (mul_pos hc ha)
    (mul_le_mul_of_nonneg_left hab hc.le)).map
    (continuous_mapPoint (inverseWindowScaleMap a b R hc)
      (continuous_inverseWindowScaleMap a b R hc)).measurable.aemeasurable

private theorem support_inverse_pullback (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (f : C_c(PositiveSizeSurplus, ℝ)) (hf : tsupport f ⊆ positiveWindowSet a b R) :
    tsupport (ProperLocalPointMap.pullbackTest (positiveSizeScale (inv_pos.mpr hc))
      (positiveSizeScale (inv_pos.mpr hc)).isProperMap f) ⊆ positiveWindowSet (c*a) (c*b) R := by
  change tsupport (f ∘ positiveSizeScale (inv_pos.mpr hc)) ⊆ _
  rw [tsupport_comp_eq_preimage f (positiveSizeScale (inv_pos.mpr hc))]
  intro z hz
  have ht := hf hz
  change (a ≤ c⁻¹*z.1.val ∧ c⁻¹*z.1.val ≤ b) ∧ z.2 ≤ R at ht
  change (c*a ≤ z.1.val ∧ z.1.val ≤ c*b) ∧ z.2 ≤ R
  rw [← div_eq_inv_mul,le_div_iff₀ hc,div_le_iff₀ hc] at ht
  simpa only [mul_comm] using ht

theorem globalTestLaw_eq_window_map {D : Type*} [Fintype D]
    (lambda a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (f : D → C_c(PositiveSizeSurplus, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ positiveWindowSet a b R) :
    (inverseScaledLaw lambda hc).map (continuous_testVector f).measurable.aemeasurable =
      (law lambda a b R hc ha hab).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  let e := positiveSizeScale (inv_pos.mpr hc)
  let Ψ (i : D) := ProperLocalPointMap.pullbackTest e e.isProperMap (f i)
  have hpoint (p : BrownianExcursionWindowPointMeasure.Input) (i : D) :
      testVector f (scalePoint (inv_pos.mpr hc) (BrownianExcursionAtomicMeasure.process lambda p)) i =
        windowTestVector a b R ha f (mapPoint (inverseWindowScaleMap a b R hc)
          (continuous_inverseWindowScaleMap a b R hc).measurable
          (BrownianArbitraryWindowLaw.pointMeasure lambda (c*a) (c*b) R (mul_pos hc ha) p)) i := by
    change (∫ z, f i z ∂(ProperLocalPointMap.mapPoint e e.isProperMap
      (BrownianExcursionAtomicMeasure.process lambda p) : Measure PositiveSizeSurplus)) = _
    rw [ProperLocalPointMap.mapPoint_integral]
    rw [BrownianArbitraryWindowLaw.actualmeasure_integral_eq_window lambda (c*a) (c*b) R
      (mul_pos hc ha) p (Ψ i) (support_inverse_pullback a b R hc (f i) (hf i))]
    change _ = ∫ z, f i (positiveWindowEmbedding a b R ha z)
      ∂(((mapPoint (inverseWindowScaleMap a b R hc)
        (continuous_inverseWindowScaleMap a b R hc).measurable
        (BrownianArbitraryWindowLaw.pointMeasure lambda (c*a) (c*b) R (mul_pos hc ha) p) :
          FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R)))
    rw [mapPoint_val,FiniteMeasure.toMeasure_map]
    have hmap := integral_map
      (μ := ((BrownianArbitraryWindowLaw.pointMeasure lambda (c*a) (c*b) R
        (mul_pos hc ha) p : FiniteMeasure (SurplusWindow (c*a) (c*b) R)) : Measure _))
      (φ := inverseWindowScaleMap a b R hc)
      (f := fun z : SurplusWindow a b R ↦ f i (positiveWindowEmbedding a b R ha z))
      (continuous_inverseWindowScaleMap a b R hc).measurable.aemeasurable
      (((f i).continuous.comp (continuous_positiveWindowEmbedding a b R ha)).measurable.aestronglyMeasurable)
    refine Eq.trans ?_ hmap.symm
    congr 1
    funext z
    apply congrArg (f i)
    apply Prod.ext
    · apply Subtype.ext
      change c⁻¹*z.1.val = z.1.val/c
      rw [div_eq_mul_inv,mul_comm]
    · rfl
  apply ProbabilityMeasure.toMeasure_injective
  simp only [inverseScaledLaw,law,ProbabilityMeasure.toMeasure_map,
    BrownianExcursionPointProcessLaw.law_toMeasure,BrownianArbitraryWindowLaw.law_eq_actual_map]
  rw [Measure.map_map (continuous_testVector f).measurable
    (continuous_scalePoint (inv_pos.mpr hc)).measurable,
    Measure.map_map ((continuous_testVector f).measurable.comp
      (continuous_scalePoint (inv_pos.mpr hc)).measurable)
      ((BrownianExcursionPointProcess.measurable_process lambda).comp
        BrownianExcursionPointProcessLaw.measurable_pathInput),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (continuous_mapPoint _ (continuous_inverseWindowScaleMap a b R hc)).measurable,
    Measure.map_map ((continuous_windowTestVector a b R ha f).measurable.comp
      (continuous_mapPoint _ (continuous_inverseWindowScaleMap a b R hc)).measurable)
      ((BrownianArbitraryWindowLaw.measurable_pointMeasure lambda (c*a) (c*b) R
        (mul_pos hc ha) (mul_le_mul_of_nonneg_left hab hc.le)).comp
          BrownianExcursionPointProcessLaw.measurable_pathInput)]
  congr 1
  funext p i
  exact hpoint (BrownianExcursionPointProcessLaw.pathInput p) i

end PerronWright.BrownianInverseWindowLaw
