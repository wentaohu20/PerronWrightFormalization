import PerronWright.Probability.BrownianCompletedCampbellShapeKernel
import PerronWright.Probability.BrownianCompletedExcursionPassageShapeMeasurability
import PerronWright.Probability.BrownianMarkedDeletedDepthExchange
import PerronWright.Probability.BrownianCompletedMarkedEntranceAmplitude

/-! # Actual marked complete-shape source at a fixed physical length

Tonelli retains the depth-dependent genuine driver-passage law. The
complete endpoint-zero entrance shape permits the actual depth exchange;
the full-area Poisson integral then gives exactly the literal size density.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace PerronWright.BrownianMarkedCompletedShapeCollapse

open BrownianPathLaw BrownianPathDilationLaw BrownianPathIndependentIncrements
open BrownianPathReflectionLaw BrownianParabolicDriftTiltGeometry
open BrownianParabolicFirstPassageStoppedTiltFull BrownianParabolicCompletedMinimumSource
open BrownianCompletedExcursionPassageShapeMeasurability
open BrownianCompletedCampbellShapeKernel BrownianCompletedMinimumShapeSource
open BrownianMarkedDeletedCampbellTest BrownianMarkedDeletedDepthExchange
open BrownianCompletedMarkedEntranceAmplitude FactorialDensity

private theorem measurable_pastMap (lambda : ℝ) :
    Measurable (fun z : ℝ × Path ↦ (z.1,actualDriverPassagePast lambda (-z.1) z.2)) :=
  measurable_fst.prodMk (measurable_joint_actualDriverPassagePast.comp
    ((measurable_const.prodMk measurable_fst.neg).prodMk measurable_snd))

private theorem source_map (lambda : ℝ)
    (F : ℝ × (ℝ≥0 × Path) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p, F (a,p) ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ∫⁻ z : ℝ × Path, F (z.1,actualDriverPassagePast lambda (-z.1) z.2)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod pathLaw := by
  have hm : Measurable (fun z : ℝ × Path ↦
      F (z.1,actualDriverPassagePast lambda (-z.1) z.2)) := by
    simpa only [Function.comp_def] using hF.comp (measurable_pastMap lambda)
  rw [lintegral_prod (fun z : ℝ × Path ↦
    F (z.1,actualDriverPassagePast lambda (-z.1) z.2)) hm.aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_map (hF.comp (measurable_const.prodMk measurable_id))
    (measurable_actualDriverPassagePast lambda (-a)))

private theorem measurable_fixed_test (lambda : ℝ) (T : ℝ≥0) (e : Path)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (fun q : ℝ × (ℝ≥0 × Path) ↦ density (lambda-(q.2.1 : ℝ)) T e *
      (∫⁻ h : Path, Ψ (q.2,-q.1,(T,e),
        driftPath (lambda-(q.2.1 : ℝ)-(T : ℝ)) h) ∂pathLaw)) := by
  have hparameter : Measurable (fun q : ℝ × (ℝ≥0 × Path) ↦ lambda-(q.2.1 : ℝ)) :=
    (measurable_const : Measurable (fun _ : ℝ × (ℝ≥0 × Path) ↦ lambda)).sub
      measurable_snd.fst.coe_nnreal_real
  have harg : Measurable (fun q : ℝ × (ℝ≥0 × Path) ↦ (lambda-(q.2.1 : ℝ),(T,e))) :=
    hparameter.prodMk measurable_const
  have hd : Measurable (fun q : ℝ × (ℝ≥0 × Path) ↦ density (lambda-(q.2.1 : ℝ)) T e) := by
    simpa only [Function.comp_def] using
      BrownianParabolicStoppedTiltGeometry.measurable_joint_density.comp harg
  have hp : Measurable (fun q : (ℝ × (ℝ≥0 × Path)) × Path ↦ q.1.2) := measurable_fst.snd
  have ha : Measurable (fun q : (ℝ × (ℝ≥0 × Path)) × Path ↦ -q.1.1) := measurable_fst.fst.neg
  have hpar : Measurable (fun q : (ℝ × (ℝ≥0 × Path)) × Path ↦
      lambda-(q.1.2.1 : ℝ)-(T : ℝ)) :=
    ((measurable_const : Measurable (fun _ : (ℝ × (ℝ≥0 × Path)) × Path ↦ lambda)).sub
      hp.fst.coe_nnreal_real).sub_const (T : ℝ)
  have hfuture := continuous_driftPath.measurable.comp (hpar.prodMk measurable_snd)
  have hstate : Measurable (fun q : (ℝ × (ℝ≥0 × Path)) × Path ↦
      (q.1.2,-q.1.1,(T,e),driftPath (lambda-(q.1.2.1 : ℝ)-(T : ℝ)) q.2)) := by
    simpa only [Function.comp_def,Pi.neg_apply,Pi.sub_apply] using
      hp.prodMk (ha.prodMk (measurable_const.prodMk hfuture))
  have hm : Measurable (fun q : (ℝ × (ℝ≥0 × Path)) × Path ↦
      Ψ (q.1.2,-q.1.1,(T,e),driftPath (lambda-(q.1.2.1 : ℝ)-(T : ℝ)) q.2)) := by
    simpa only [Function.comp_def] using hΨ.comp hstate
  exact hd.mul hm.lintegral_prod_right'

theorem actual_marked_shapeKernel_at_length (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (r : ℕ) (H : ℝ × Path → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p,
      shapeKernel lambda (markedDeletedTest lambda r H) ((a,p),(T : ℝ))
        ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda (T : ℝ))*sizeFactor 1 (T : ℝ) r) *
        (∫⁻ f : Path, H ((T : ℝ),f) ∂pathLaw) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  let Ψ := markedDeletedTest lambda r H
  have hΨ : Measurable Ψ := measurable_markedDeletedTest lambda r H hH
  let μ : Measure (ℝ × Path) := (volume.restrict (Ioi (0 : ℝ))).prod pathLaw
  let G : (ℝ × Path) × Path → ℝ≥0∞ := fun q ↦
    density (lambda-((actualDriverPassagePast lambda (-q.1.1) q.1.2).1 : ℝ)) T
      (brownianDilation T q.2) *
        (∫⁻ h : Path, Ψ (actualDriverPassagePast lambda (-q.1.1) q.1.2,-q.1.1,
          (T,brownianDilation T q.2),driftPath
            (lambda-((actualDriverPassagePast lambda (-q.1.1) q.1.2).1 : ℝ)-(T : ℝ)) h) ∂pathLaw)
  have hinput : Measurable (fun q : ((ℝ × Path) × Path) × Path ↦
      (lambda,((T : ℝ),(q.1.1,(q.1.2,q.2))))) :=
    measurable_const.prodMk (measurable_const.prodMk
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hm := ((measurable_joint_completedPassageDensity.comp hinput).mul
    (hΨ.comp (measurable_joint_completedPassageState.comp hinput))).lintegral_prod_right' (ν := pathLaw)
  have hG : Measurable G := by
    convert hm using 1
    funext q
    simp only [Function.comp_def,completedPassageDensity,completedPassageState,Real.toNNReal_coe]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  have hK : Measurable (fun q : ℝ × (ℝ≥0 × Path) ↦
      shapeKernel lambda Ψ (q,(T : ℝ))) :=
    (measurable_shapeKernel lambda Ψ hΨ).comp (measurable_id.prodMk measurable_const)
  calc
    _ = ∫⁻ z : ℝ × Path,
        shapeKernel lambda Ψ ((z.1,actualDriverPassagePast lambda (-z.1) z.2),(T : ℝ)) ∂μ :=
      source_map lambda _ hK
    _ = shapeFactor (T : ℝ)*(∫⁻ z : ℝ × Path,
        ∫⁻ e : Path, G (z,e) ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one ∂μ) := by
      rw [← lintegral_const_mul' (shapeFactor (T : ℝ)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      simp only [shapeKernel,Real.toNNReal_coe,G]
    _ = shapeFactor (T : ℝ)*(∫⁻ e : Path, ∫⁻ z : ℝ × Path, G (z,e) ∂μ
        ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
      rw [lintegral_lintegral_swap hG.aemeasurable]
    _ = shapeFactor (T : ℝ)*(∫⁻ e : Path,
        BrownianExcursionTuplePoissonWeights.poissonWeight
          (Real.toNNReal (BrownianBridgeCyclicArea.pathArea T (brownianDilation T e))) r *
            (ENNReal.ofReal (Real.exp (BrownianBridgeCyclicArea.pathArea T (brownianDilation T e)-energy lambda T/2)) *
              ((T : ℝ≥0∞)⁻¹*(∫⁻ f : Path, H ((T : ℝ),f) ∂pathLaw)))
                ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [BrownianEntranceContinuousRealization.ae_pathLaw_terminal_zero 1 zero_lt_one] with e he
      have hzero : brownianDilation T e T = 0 := by
        change Real.sqrt (T : ℝ)*e (T/T) = 0
        rw [div_self (ne_of_gt hT),he,mul_zero]
      have hf := measurable_fixed_test lambda T (brownianDilation T e) Ψ hΨ
      have hmap := source_map lambda _ hf
      change (∫⁻ z : ℝ × Path,
        density (lambda-((actualDriverPassagePast lambda (-z.1) z.2).1 : ℝ)) T (brownianDilation T e) *
          (∫⁻ h : Path, Ψ (actualDriverPassagePast lambda (-z.1) z.2,-z.1,(T,brownianDilation T e),
            driftPath (lambda-((actualDriverPassagePast lambda (-z.1) z.2).1 : ℝ)-(T : ℝ)) h) ∂pathLaw) ∂μ) = _
      rw [← hmap]
      exact markedDeletedTest_depth_lintegral lambda T hT (brownianDilation T e) hzero r H hH
    _ = _ := actual_complete_marked_entrance_amplitude lambda T hT r _

end PerronWright.BrownianMarkedCompletedShapeCollapse
