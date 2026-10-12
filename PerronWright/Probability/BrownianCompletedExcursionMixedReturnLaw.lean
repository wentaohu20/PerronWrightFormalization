import PerronWright.Probability.BrownianCompletedExcursionMixedSchedule
import PerronWright.Probability.BrownianMinimumFutureKilledPrefixReturnDensity

/-! # Actual mixed observations and completed lifetime identify the entrance shape

The genuine prefix/killed-future/final-first-hit integral is rearranged by
Tonelli and matched at each lifetime to the actual continuous entrance
law. No conditional-shape or weak-limit interface is a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionMixedReturnLaw

open BrownianPathLaw BrownianPathDilationLaw BrownianMinimumFutureEntranceSource
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnDensity BrownianMinimumFuturePostUnit
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFreeEntranceGeometry BrownianEntranceKilledChainConcatenation
open BrownianMinimumFutureKilledPrefixReturnDensity BrownianCompletedExcursionMixedSchedule

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private theorem jointDensity_finite (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector n) :
    jointDensity n a gaps v ≠ ⊤ := by
  unfold jointDensity
  exact ENNReal.prod_ne_top (fun i _ ↦ ENNReal.ofReal_ne_top)

private def mixedShape (k n : ℕ) (pre : Fin (k+2) → ℝ≥0) (post : Fin (n+2) → ℝ≥0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (ζ : ℝ) : ℝ≥0∞ :=
  returnDensity ζ * (∫⁻ e : Path,
    G ((fun i : Fin (k+1) ↦ brownianDilation (Real.toNNReal ζ) e (pre i.succ)),
      ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (1+post i.succ)),ζ))
        ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)

private theorem measurable_mixedShape (k n : ℕ) (pre : Fin (k+2) → ℝ≥0) (post : Fin (n+2) → ℝ≥0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    Measurable (mixedShape k n pre post G) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  have hp : Measurable (fun q : ℝ × Path ↦ brownianDilation (Real.toNNReal q.1) q.2) :=
    measurable_joint_brownianDilation.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hpre : Measurable (fun q : ℝ × Path ↦ fun i : Fin (k+1) ↦
      brownianDilation (Real.toNNReal q.1) q.2 (pre i.succ)) :=
    measurable_pi_lambda _ (fun _ ↦ (continuous_eval _).measurable.comp hp)
  have hpost : Measurable (fun q : ℝ × Path ↦ fun i : Fin (n+1) ↦
      brownianDilation (Real.toNNReal q.1) q.2 (1+post i.succ)) :=
    measurable_pi_lambda _ (fun _ ↦ (continuous_eval _).measurable.comp hp)
  have h := hG.comp (hpre.prodMk (hpost.prodMk measurable_fst))
  exact measurable_returnDensity.mul
    (h.lintegral_prod_right' (ν := BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem actual_mixed_return_shape_lintegral (k n : ℕ)
    (prefixTimes : Fin (k+2) → ℝ≥0) (hprefix : StrictMono prefixTimes)
    (hprefixzero : prefixTimes 0 = 0) (hprefixlast : prefixTimes (Fin.last (k+1)) = 1)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ g in {g : Path | ((1+times (Fin.last (n+1)) : ℝ≥0) : ℝ≥0∞) < firstReturnZero g},
      G ((fun i : Fin (k+1) ↦ g (prefixTimes i.succ)),
        ((fun i : Fin (n+1) ↦ g (1+times i.succ)),(firstReturnZero g).toReal)) ∂unitSourceLaw) =
      ∫⁻ ζ in Ioi (1+(times (Fin.last (n+1)) : ℝ)), returnDensity ζ *
        (∫⁻ e : Path,
          G ((fun i : Fin (k+1) ↦ brownianDilation (Real.toNNReal ζ) e (prefixTimes i.succ)),
            ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (1+times i.succ)),ζ))
              ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  let pre := orderedGaps (k+1) prefixTimes
  let post := orderedGaps (n+1) times
  let t : ℝ := times (Fin.last (n+1))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (2/Real.pi))
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  have hcinv : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  let J (u : FreeVector (k+1)) (v : FreeVector (n+1)) (s : ℝ) : ℝ≥0∞ :=
    ((entranceJoint k pre u*jointDensity (n+1) (u (Fin.last k)) post v)*
      BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (s-t)/c)*G (u,(v,1+s))
  have hchain : Measurable (fun q : FreeVector (k+1) × FreeVector (n+1) ↦
      entranceJoint k pre q.1*jointDensity (n+1) (q.1 (Fin.last k)) post q.2) := by
    have h := (measurable_entranceJoint (k+(n+1)) (concatenatedGaps k pre post)).comp
      (continuous_concatenatedHeights k (n+1)).measurable
    simpa only [Function.comp_def,entranceJoint_concatenated] using h
  have hm : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦ J q.1 q.2.1 q.2.2) := by
    have hpair : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦ (q.1,q.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hp : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
        (q.2.1 (Fin.last n),q.2.2-t)) :=
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_snd.comp measurable_snd).sub_const _)
    have hd : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
        BrownianFirstPassageDensityGeometry.density (q.2.1 (Fin.last n)) (q.2.2-t)) := by
      simpa only [Function.comp_def] using BrownianHeatResolvent.measurable_joint_passageDensity.comp hp
    have hg : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦ G (q.1,(q.2.1,1+q.2.2))) :=
      hG.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_const.add (measurable_snd.comp measurable_snd))))
    have hc : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
        entranceJoint k pre q.1*jointDensity (n+1) (q.1 (Fin.last k)) post q.2.1) := by
      simpa only [Function.comp_def] using hchain.comp hpair
    have hnum : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
        (entranceJoint k pre q.1*jointDensity (n+1) (q.1 (Fin.last k)) post q.2.1)*
          BrownianFirstPassageDensityGeometry.density (q.2.1 (Fin.last n)) (q.2.2-t)) := by
      simpa only [Function.comp_def] using measurable_mul.comp (hc.prodMk hd)
    have hnorm : Measurable (fun q : FreeVector (k+1) × (FreeVector (n+1) × ℝ) ↦
        ((entranceJoint k pre q.1*jointDensity (n+1) (q.1 (Fin.last k)) post q.2.1)*
          BrownianFirstPassageDensityGeometry.density (q.2.1 (Fin.last n)) (q.2.2-t))/c) := by
      simpa only [Function.comp_def] using measurable_div.comp (hnum.prodMk measurable_const)
    simpa only [J,Function.comp_def] using measurable_mul.comp (hnorm.prodMk hg)
  have hmus : Measurable (fun q : (FreeVector (k+1) × ℝ) × FreeVector (n+1) ↦ J q.1.1 q.2 q.1.2) := by
    have hp : Measurable (fun q : (FreeVector (k+1) × ℝ) × FreeVector (n+1) ↦
        (q.1.1,(q.2,q.1.2))) := (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    simpa only [Function.comp_def] using hm.comp hp
  rw [actual_mixed_ordered_return_lintegral k n prefixTimes hprefix hprefixzero hprefixlast times hstrict hzero G hG]
  calc
    _ = ∫⁻ u : FreeVector (k+1), ∫⁻ v : FreeVector (n+1), ∫⁻ s in Ioi t, J u v s := by
      rw [div_eq_mul_inv,← lintegral_mul_const' c⁻¹ _ hcinv]
      apply lintegral_congr
      intro u
      rw [← lintegral_const_mul' (entranceJoint k pre u) _ (entranceJoint_ne_top k pre u),
        ← lintegral_mul_const' c⁻¹ _ hcinv]
      apply lintegral_congr
      intro v
      rw [show entranceJoint k pre u*(jointDensity (n+1) (u (Fin.last k)) post v*
          (∫⁻ s in Ioi t, BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (s-t)*G (u,(v,1+s))))*c⁻¹ =
          (entranceJoint k pre u*jointDensity (n+1) (u (Fin.last k)) post v)*
            (∫⁻ s in Ioi t, BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (s-t)*G (u,(v,1+s)))*c⁻¹ by ac_rfl]
      rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (entranceJoint_ne_top k pre u)
        (jointDensity_finite (n+1) _ post v)),
        ← lintegral_mul_const' c⁻¹ _ hcinv]
      apply lintegral_congr
      intro s
      simp only [J,div_eq_mul_inv]
      ac_rfl
    _ = ∫⁻ u : FreeVector (k+1), ∫⁻ s in Ioi t, ∫⁻ v : FreeVector (n+1), J u v s := by
      apply lintegral_congr
      intro u
      have hv : Measurable (fun q : FreeVector (n+1) × ℝ ↦ J u q.1 q.2) := by
        simpa only [Function.comp_def,id_eq] using hm.comp
          (measurable_const.prodMk (measurable_id : Measurable (fun q : FreeVector (n+1) × ℝ ↦ q)))
      exact lintegral_lintegral_swap hv.aemeasurable
    _ = ∫⁻ s in Ioi t, ∫⁻ u : FreeVector (k+1), ∫⁻ v : FreeVector (n+1), J u v s :=
      lintegral_lintegral_swap (hmus.lintegral_prod_right' (ν := volume)).aemeasurable
    _ = ∫⁻ s in Ioi t, mixedShape k n prefixTimes times G (1+s) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hsn : 0 ≤ s := (show 0 ≤ t from NNReal.coe_nonneg _).trans (le_of_lt hs)
      let τ := Real.toNNReal s
      have heτ : (τ : ℝ) = s := Real.coe_toNNReal s hsn
      have hτ : times (Fin.last (n+1)) < τ := by exact_mod_cast (show t < (τ : ℝ) by rw [heτ]; exact hs)
      have h := mixed_terminal_chain_shape_lintegral k n prefixTimes hprefix hprefixzero hprefixlast
        times hstrict hzero τ hτ (fun q ↦ G (q.1,(q.2,1+s)))
        (hG.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
      have hscale : 1+τ = Real.toNNReal (1+s) := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add,NNReal.coe_one,heτ,Real.coe_toNNReal _ (by linarith)]
      rw [heτ,hscale] at h
      simpa only [J,pre,post,t,c,mixedShape] using h
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioi,← lintegral_indicator measurableSet_Ioi]
      have hk := (measurable_mixedShape k n prefixTimes times G hG).indicator
        (measurableSet_Ioi : MeasurableSet (Ioi (1+t)))
      have h := (measurePreserving_add_left (volume : Measure ℝ) 1).lintegral_comp hk
      convert h using 1
      · apply lintegral_congr
        intro s
        simp only [indicator_apply,mem_Ioi]
        simp only [add_lt_add_iff_left]
      · rfl

end PerronWright.BrownianCompletedExcursionMixedReturnLaw
