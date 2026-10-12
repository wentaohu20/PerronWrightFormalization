import PerronWright.Probability.BrownianCompletedMinimumShapeSource

/-! # Joint Borel kernel and exact inverse-length normalization

The depth, arbitrary tagged stopped past, and physical duration are joint
variables. The complete-state test retains the actual dilated entrance
shape and the whole residual driver. Positive reciprocal length is finite,
so its exact passage through both integrals does not require a finite test
integral and remains valid for infinite nonnegative Borel tests.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedCampbellShapeKernel

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianPathDilationLaw BrownianMinimumFuturePostUnit
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicCompletedMinimumSource BrownianCompletedMinimumCampbellSource
open BrownianCompletedMinimumShapeSource BrownianParabolicFirstPassageStoppedTiltFull
open FullHorizonExcursionSection

def shapeKernel (lambda : ℝ) (Ψ : CompletedState → ℝ≥0∞)
    (q : (ℝ × (ℝ≥0 × Path)) × ℝ) : ℝ≥0∞ :=
  shapeFactor q.2*(∫⁻ e : Path,
    density (lambda-(q.1.2.1 : ℝ)) (Real.toNNReal q.2) (brownianDilation (Real.toNNReal q.2) e)*
      (∫⁻ h : Path,
        Ψ (q.1.2,-q.1.1,(Real.toNNReal q.2,brownianDilation (Real.toNNReal q.2) e),
          driftPath (lambda-(q.1.2.1 : ℝ)-(Real.toNNReal q.2 : ℝ)) h) ∂pathLaw)
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)

private def liftedState (lambda : ℝ)
    (z : (((ℝ × (ℝ≥0 × Path)) × ℝ) × Path) × Path) : CompletedState :=
  (z.1.1.1.2,-z.1.1.1.1,
    (Real.toNNReal z.1.1.2,brownianDilation (Real.toNNReal z.1.1.2) z.1.2),
    driftPath (lambda-(z.1.1.1.2.1 : ℝ)-(Real.toNNReal z.1.1.2 : ℝ)) z.2)

private theorem measurable_liftedState (lambda : ℝ) : Measurable (liftedState lambda) := by
  have hp : Measurable (fun z : (((ℝ × (ℝ≥0 × Path)) × ℝ) × Path) × Path ↦ z.1.1.1.2) :=
    measurable_fst.fst.fst.snd
  have ha : Measurable (fun z : (((ℝ × (ℝ≥0 × Path)) × ℝ) × Path) × Path ↦ z.1.1.1.1) :=
    measurable_fst.fst.fst.fst
  have hl : Measurable (fun z : (((ℝ × (ℝ≥0 × Path)) × ℝ) × Path) × Path ↦
      Real.toNNReal z.1.1.2) := measurable_fst.fst.snd.real_toNNReal
  have he := measurable_joint_brownianDilation.comp (hl.prodMk measurable_fst.snd)
  have hparameter : Measurable (fun z : (((ℝ × (ℝ≥0 × Path)) × ℝ) × Path) × Path ↦
      lambda-(z.1.1.1.2.1 : ℝ)-(Real.toNNReal z.1.1.2 : ℝ)) := (measurable_const.sub
    (NNReal.continuous_coe.measurable.comp hp.fst)).sub
      (NNReal.continuous_coe.measurable.comp hl)
  exact hp.prodMk (ha.neg.prodMk ((hl.prodMk he).prodMk
    (continuous_driftPath.measurable.comp (hparameter.prodMk measurable_snd))))

theorem measurable_shapeKernel (lambda : ℝ) (Ψ : CompletedState → ℝ≥0∞)
    (hΨ : Measurable Ψ) : Measurable (shapeKernel lambda Ψ) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  have hm : Measurable (fun z : ((ℝ × (ℝ≥0 × Path)) × ℝ) × Path ↦
      ∫⁻ h : Path, Ψ (liftedState lambda (z,h)) ∂pathLaw) :=
    (hΨ.comp (measurable_liftedState lambda)).lintegral_prod_right'
  have hl : Measurable (fun z : ((ℝ × (ℝ≥0 × Path)) × ℝ) × Path ↦
      Real.toNNReal z.1.2) := measurable_fst.snd.real_toNNReal
  have he := measurable_joint_brownianDilation.comp (hl.prodMk measurable_snd)
  have hparameter : Measurable (fun z : ((ℝ × (ℝ≥0 × Path)) × ℝ) × Path ↦
      lambda-(z.1.1.2.1 : ℝ)) := measurable_const.sub
    (NNReal.continuous_coe.measurable.comp measurable_fst.fst.snd.fst)
  have hd := measurable_joint_density.comp (hparameter.prodMk (hl.prodMk he))
  exact (measurable_shapeFactor.comp measurable_snd).mul
    (hd.mul hm).lintegral_prod_right'

private theorem nested_lintegral_div_const {E H : Type*} [MeasurableSpace E] [MeasurableSpace H]
    (μ : Measure E) (ν : Measure H) (c : ℝ≥0∞) (hc : c ≠ 0)
    (f : E → ℝ≥0∞) (g : E → H → ℝ≥0∞) :
    (∫⁻ e, f e*(∫⁻ h, g e h ∂ν) ∂μ)/c =
      ∫⁻ e, f e*(∫⁻ h, g e h/c ∂ν) ∂μ := by
  have hi : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hc
  simp only [div_eq_mul_inv]
  rw [← lintegral_mul_const' c⁻¹ (fun e ↦ f e*(∫⁻ h, g e h ∂ν)) hi]
  apply lintegral_congr
  intro e
  rw [lintegral_mul_const' c⁻¹ (g e) hi,mul_assoc]

theorem shapeKernel_div (lambda : ℝ) (Ψ : CompletedState → ℝ≥0∞)
    (a : ℝ) (p : ℝ≥0 × Path) (l : ℝ) (hl : 0 < l) :
    shapeKernel lambda Ψ ((a,p),l)/ENNReal.ofReal l =
      shapeFactor l*(∫⁻ e : Path,
        density (lambda-(p.1 : ℝ)) (Real.toNNReal l) (brownianDilation (Real.toNNReal l) e)*
          (∫⁻ h : Path,
            Ψ (p,-a,(Real.toNNReal l,brownianDilation (Real.toNNReal l) e),
              driftPath (lambda-(p.1 : ℝ)-(Real.toNNReal l : ℝ)) h)/
                (Real.toNNReal l : ℝ≥0∞) ∂pathLaw)
                  ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  unfold shapeKernel
  rw [mul_div_assoc]
  congr 1
  exact nested_lintegral_div_const _ _ (ENNReal.ofReal l)
    (ENNReal.ofReal_ne_zero_iff.mpr hl) _ _

theorem actual_completed_campbell_normalized_shape_lintegral (lambda : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        Ψ (componentState lambda (q : ℝ) f) else 0 ∂pathLaw) =
      ∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
        ∫⁻ p in {p : ℝ≥0 × Path | p.1 < Real.toNNReal t},
          (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
            shapeKernel lambda Ψ ((a,p),l)/ENNReal.ofReal l)
              ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  rw [actual_completed_campbell_shape_source_lintegral lambda Ψ hΨ]
  apply lintegral_congr
  intro t
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro p
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  exact (shapeKernel_div lambda Ψ a p l ((Real.toNNReal t-p.1).coe_nonneg.trans_lt hl)).symm

end PerronWright.BrownianCompletedCampbellShapeKernel
