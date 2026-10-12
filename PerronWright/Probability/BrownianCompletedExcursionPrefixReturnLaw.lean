import PerronWright.Probability.BrownianCompletedExcursionCandidate
import PerronWright.Probability.BrownianCompletedExcursionTerminalDensity
import PerronWright.Probability.BrownianMinimumFuturePrefixTests

/-! # Actual prefix samples and completed lifetime have the entrance mixture

This is the zero-post-unit-sample case of the completed stopped-path law.
The actual source prefix/return mixture, its proved entrance prefix law,
and the actual terminal first-hit factor identify the conditional prefix
shape. No excursion shape identity is supplied as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionPrefixReturnLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn
open BrownianMinimumFutureReturnMixture BrownianMinimumFutureReturnDensity
open BrownianMinimumFuturePrefixTests BrownianMinimumFuturePostUnit
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFreeEntranceGeometry BrownianKilledFreeEntranceTests
open BrownianPositiveBridgeMultiPointEntrance BrownianEntranceFiniteDimensionalFamily
open BrownianCompletedExcursionTerminalDensity BrownianEntranceDurationScaling

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private theorem orderedGaps_snoc_before (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (τ : ℝ≥0) (j : ℕ) (hj : j < n) :
    orderedGaps (n+1) (Fin.snoc times τ) j = orderedGaps n times j := by
  unfold orderedGaps finiteTimeExtension
  simp only [Nat.min_eq_left (show j+1 ≤ n+1 by omega),
    Nat.min_eq_left (show j ≤ n+1 by omega),Nat.min_eq_left (show j+1 ≤ n by omega),
    Nat.min_eq_left (show j ≤ n by omega)]
  change (Fin.snoc times τ : Fin (n+2) → ℝ≥0) ((⟨j+1,by omega⟩ : Fin (n+1)).castSucc)-
    (Fin.snoc times τ : Fin (n+2) → ℝ≥0) ((⟨j,by omega⟩ : Fin (n+1)).castSucc) = _
  rw [Fin.snoc_castSucc,Fin.snoc_castSucc]

private theorem orderedGaps_snoc_last (n : ℕ) (times : Fin (n+1) → ℝ≥0) (τ : ℝ≥0) :
    orderedGaps (n+1) (Fin.snoc times τ) n = τ-times (Fin.last n) := by
  unfold orderedGaps finiteTimeExtension
  simp only [Nat.min_eq_left (show n+1 ≤ n+1 by omega),Nat.min_eq_left (show n ≤ n+1 by omega)]
  change (Fin.snoc times τ : Fin (n+2) → ℝ≥0) (Fin.last (n+1))-
    (Fin.snoc times τ : Fin (n+2) → ℝ≥0) (Fin.castSucc (Fin.last n)) = _
  rw [Fin.snoc_last,Fin.snoc_castSucc]

private theorem strictMono_snoc (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hs : StrictMono times) (τ : ℝ≥0) (hτ : times (Fin.last n) < τ) :
    StrictMono (Fin.snoc times τ) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last] using hτ
  · simpa only [Fin.snoc_castSucc,Fin.succ_castSucc] using
      hs (show j.castSucc < j.succ by exact Fin.castSucc_lt_succ)

private theorem entranceJoint_snoc (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (τ : ℝ≥0) (v : FreeVector (n+1)) :
    entranceJoint n (orderedGaps (n+2) (Fin.snoc times τ)) v =
      entranceJoint n (orderedGaps (n+1) times) v := by
  unfold entranceJoint internalDensity
  rw [orderedGaps_snoc_before (n+1) times τ 0 (by omega)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [orderedGaps_snoc_before (n+1) times τ (i.val+1) (by omega)]

private def passageKernel (n : ℕ) (H : FreeVector (n+1) × ℝ → ℝ≥0∞)
    (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s*H (v,1+s)

private theorem measurable_passageKernel (n : ℕ)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    Measurable (passageKernel n H) := by
  have hv : Measurable (fun v : FreeVector (n+1) ↦ v (Fin.last n)) := measurable_pi_apply _
  have hp : Measurable (fun q : FreeVector (n+1) × ℝ ↦ (q.1 (Fin.last n),q.2)) :=
    (hv.comp measurable_fst).prodMk measurable_snd
  have hd : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) q.2) := by
    simpa only [Function.comp_def] using BrownianHeatResolvent.measurable_joint_passageDensity.comp hp
  have ht : Measurable (fun q : FreeVector (n+1) × ℝ ↦ H (q.1,1+q.2)) :=
    hH.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))
  have hm : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) q.2*H (q.1,1+q.2)) := by
    simpa only [Function.comp_def] using measurable_mul.comp (hd.prodMk ht)
  exact hm.lintegral_prod_right' (ν := volume)

private theorem actual_prefix_return_numeric (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hs : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g, H ((fun i : Fin (n+1) ↦ g (times i.succ)),(firstReturnZero g).toReal) ∂unitSourceLaw) =
      (∫⁻ v, entranceJoint n (orderedGaps (n+1) times) v*passageKernel n H v)/
        ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  let coords : Path → FreeVector (n+1) := fun p ↦ fun i ↦ p (times i.succ)
  have hm : Measurable coords := measurable_pi_lambda _ (fun _ ↦ (continuous_eval _).measurable)
  have he (g : Path) : coords (pastPath 1 g) = coords g := by
    funext i
    have hi : times i.succ ≤ 1 := hlast ▸ hs.monotone (Fin.le_last i.succ)
    simp only [coords,pastPath_eval,min_eq_left hi]
  have hc (p : Path) : coords p (Fin.last n) = p 1 := by simp only [coords,Fin.succ_last,hlast]
  let Ψ : Path × ℝ → ℝ≥0∞ := fun q ↦ H (coords q.1,q.2)
  have hΨ : Measurable Ψ := hH.comp ((hm.comp measurable_fst).prodMk measurable_snd)
  have h := actual_firstReturn_prefix_lintegral hΨ
  simp only [Ψ,he] at h
  simp_rw [← hc] at h
  rw [h]
  have hk := measurable_passageKernel n H hH
  change (∫⁻ p, passageKernel n H (coords p) ∂unitSourceLaw.map (pastPath 1)) = _
  have hkp : Measurable (fun p : Path ↦ passageKernel n H (coords p)) := hk.comp hm
  rw [lintegral_map hkp (measurable_pastPath 1)]
  simp only [he]
  rw [unitSource_prefix_borel_test n times hs hzero hlast _ hk,
    freeEntranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceJoint n _) hk]
  rfl

private def shapeKernel (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (ζ : ℝ) : ℝ≥0∞ :=
  returnDensity ζ*(∫⁻ e : Path,
    H ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (times i.succ)),ζ)
      ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)

private theorem measurable_shapeKernel (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    Measurable (shapeKernel n times H) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  have hp : Measurable (fun q : ℝ × Path ↦ brownianDilation (Real.toNNReal q.1) q.2) :=
    measurable_joint_brownianDilation.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hc : Measurable (fun q : ℝ × Path ↦ fun i : Fin (n+1) ↦
      brownianDilation (Real.toNNReal q.1) q.2 (times i.succ)) :=
    measurable_pi_lambda _ (fun _ ↦ (continuous_eval _).measurable.comp hp)
  have hm : Measurable (fun q : ℝ × Path ↦
      H ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal q.1) q.2 (times i.succ)),q.1)) :=
    hH.comp (hc.prodMk measurable_fst)
  exact measurable_returnDensity.mul
    (hm.lintegral_prod_right' (ν := BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one))

private theorem numeric_shape_at (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hs : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) (s : ℝ) :
    (∫⁻ v : FreeVector (n+1),
      (entranceJoint n (orderedGaps (n+1) times) v*
        BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s/
          ENNReal.ofReal (Real.sqrt (2/Real.pi)))*H (v,1+s)) = shapeKernel n times H (1+s) := by
  by_cases hpos : 0 < s
  · let τ := Real.toNNReal (1+s)
    have heτ : (τ : ℝ) = 1+s := Real.coe_toNNReal _ (by linarith)
    have hτ : 1 < τ := by exact_mod_cast (show (1 : ℝ) < (τ : ℝ) by rw [heτ]; linarith)
    let ts : Fin (n+3) → ℝ≥0 := Fin.snoc times τ
    have ht : StrictMono ts := strictMono_snoc (n+1) times hs τ (hlast ▸ hτ)
    have ht0 : ts 0 = 0 := by
      change (Fin.snoc times τ : Fin (n+3) → ℝ≥0) ((0 : Fin (n+2)).castSucc) = 0
      rw [Fin.snoc_castSucc,hzero]
    have htlast : ts (Fin.last (n+2)) = τ := Fin.snoc_last _ _
    have h := ordered_terminal_hitting_lintegral τ hτ n ts ht ht0 htlast
      (fun v ↦ H (v,1+s)) (hH.comp (measurable_id.prodMk measurable_const))
    have hgap : (orderedGaps (n+2) ts (n+1) : ℝ) = s := by
      rw [orderedGaps_snoc_last (n+1) times τ,hlast,
        NNReal.coe_sub hτ.le,heτ]
      norm_num
    dsimp only [ts] at h hgap
    simp_rw [entranceJoint_snoc n times τ] at h
    rw [hgap] at h
    rw [lintegral_duration_scaling τ (lt_trans (by norm_num) hτ)
      (fun e ↦ H (orderedEval (n+1) ts e,1+s))
      (hH.comp ((continuous_orderedEval (n+1) ts).measurable.prodMk measurable_const))] at h
    have hcoords (e : Path) : orderedEval (n+1) (Fin.snoc times τ) (brownianDilation τ e) =
        fun i : Fin (n+1) ↦ brownianDilation τ e (times i.succ) := by
      funext i
      change brownianDilation τ e ((Fin.snoc times τ : Fin (n+3) → ℝ≥0) i.succ.castSucc) = _
      rw [Fin.snoc_castSucc]
    dsimp only [ts] at h
    simp_rw [hcoords] at h
    simpa only [heτ,shapeKernel,τ] using h
  · have hz (v : FreeVector (n+1)) : BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s = 0 := by
      rw [BrownianFirstPassageDensityGeometry.density,
        BrownianFirstPassageDensityGeometry.densityReal_eq_zero_of_nonpos _ s (le_of_not_gt hpos),
        ENNReal.ofReal_zero]
    have hr : returnDensity (1+s) = 0 := by
      simp only [returnDensity,indicator_of_notMem (show 1+s ∉ Ioi (1 : ℝ) by simpa using hpos),
        ENNReal.ofReal_zero]
    simp only [hz,mul_zero,ENNReal.zero_div,zero_mul,lintegral_zero,shapeKernel,hr]

theorem actual_prefix_return_shape_lintegral (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hs : StrictMono times) (hzero : times 0 = 0) (hlast : times (Fin.last (n+1)) = 1)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g, H ((fun i : Fin (n+1) ↦ g (times i.succ)),(firstReturnZero g).toReal) ∂unitSourceLaw) =
      ∫⁻ ζ : ℝ, returnDensity ζ*(∫⁻ e : Path,
        H ((fun i : Fin (n+1) ↦ brownianDilation (Real.toNNReal ζ) e (times i.succ)),ζ)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  rw [actual_prefix_return_numeric n times hs hzero hlast H hH]
  have hv : Measurable (fun v : FreeVector (n+1) ↦ v (Fin.last n)) := measurable_pi_apply _
  have hd : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) q.2) := by
    simpa only [Function.comp_def] using BrownianHeatResolvent.measurable_joint_passageDensity.comp
      ((hv.comp measurable_fst).prodMk measurable_snd)
  have ht : Measurable (fun q : FreeVector (n+1) × ℝ ↦ H (q.1,1+q.2)) :=
    hH.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))
  have he := measurable_entranceJoint n (orderedGaps (n+1) times)
  have hnum : Measurable (fun v : FreeVector (n+1) ↦
      entranceJoint n (orderedGaps (n+1) times) v*passageKernel n H v) :=
    he.mul (measurable_passageKernel n H hH)
  have hm : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      (entranceJoint n (orderedGaps (n+1) times) q.1*
        BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) q.2/
          ENNReal.ofReal (Real.sqrt (2/Real.pi)))*H (q.1,1+q.2)) :=
    (((he.comp measurable_fst).mul hd).div_const _).mul ht
  calc
    _ = ∫⁻ v : FreeVector (n+1), ∫⁻ s : ℝ,
        (entranceJoint n (orderedGaps (n+1) times) v*
          BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s/
            ENNReal.ofReal (Real.sqrt (2/Real.pi)))*H (v,1+s) := by
      rw [div_eq_mul_inv,← lintegral_mul_const _ hnum]
      apply lintegral_congr
      intro v
      have hp : Measurable (fun s : ℝ ↦ BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s*H (v,1+s)) :=
        (BrownianFirstPassageDensityGeometry.measurable_density _).mul
          (hH.comp (measurable_const.prodMk (measurable_const.add measurable_id)))
      rw [show entranceJoint n (orderedGaps (n+1) times) v*passageKernel n H v*
          (ENNReal.ofReal (Real.sqrt (2/Real.pi)))⁻¹ =
          (entranceJoint n (orderedGaps (n+1) times) v*(ENNReal.ofReal (Real.sqrt (2/Real.pi)))⁻¹)*
            passageKernel n H v by ac_rfl,passageKernel,← lintegral_const_mul _ hp]
      apply lintegral_congr
      intro s
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = ∫⁻ s : ℝ, ∫⁻ v : FreeVector (n+1),
        (entranceJoint n (orderedGaps (n+1) times) v*
          BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) s/
            ENNReal.ofReal (Real.sqrt (2/Real.pi)))*H (v,1+s) := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ s : ℝ, shapeKernel n times H (1+s) := lintegral_congr (numeric_shape_at n times hs hzero hlast H hH)
    _ = _ := (measurePreserving_add_left (volume : Measure ℝ) 1).lintegral_comp
      (measurable_shapeKernel n times H hH)

end PerronWright.BrownianCompletedExcursionPrefixReturnLaw
