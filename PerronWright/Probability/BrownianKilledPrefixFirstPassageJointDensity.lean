import PerronWright.Probability.BrownianNormalizedSurvivalWholeLaw
import PerronWright.Probability.BrownianKilledFiniteDimensionalOrderedDensity
import PerronWright.Probability.BrownianFirstPassageDensityLaw
import PerronWright.Probability.BrownianFirstPassageEndpointGeometry
import PerronWright.Probability.BrownianHeatResolvent

/-! # Actual killed prefix coordinates and the later first-passage time

The fixed-time Brownian past/future product and the literal first-passage
decomposition give a killed transition chain followed by the actual
first-hit density. No hitting-conditioned bridge law is an input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledPrefixFirstPassageJointDensity

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageUncappedLaw
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianNormalizedSurvivalWholeLaw

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private def coordinates (n : ℕ) (a : ℝ) (times : Fin (n+2) → ℝ≥0)
    (f : Path) : FreeVector (n+1) := fun i ↦ a+f (times i.succ)

private theorem measurable_coordinates (n : ℕ) (a : ℝ) (times : Fin (n+2) → ℝ≥0) :
    Measurable (coordinates n a times) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)

private theorem coordinates_past (n : ℕ) (a : ℝ) (times : Fin (n+2) → ℝ≥0)
    (hmono : Monotone times) (f : Path) :
    coordinates n a times (pastPath (times (Fin.last (n+1))) f) = coordinates n a times f := by
  funext i
  simp only [coordinates,pastPath_eval,min_eq_left (hmono (Fin.le_last i.succ))]

private theorem realTime_after_survival (a : ℝ) (T : ℝ≥0) (f : Path)
    (hs : f ∈ survival (-a) T) (hfin : firstPassage (-a) f ≠ ⊤) :
    realTime (-a) f = (T : ℝ)+realTime (-(a+f T)) (futurePath T f) := by
  let τ := (firstPassage (-a) f).toNNReal
  have hc : (τ : ℝ≥0∞) = firstPassage (-a) f := ENNReal.coe_toNNReal hfin
  have hT : T < τ := by
    have h := (mem_survival_iff_firstPassage (-a) T f).mp hs
    rwa [← hc,ENNReal.coe_lt_coe] at h
  have hupper : firstPassage (-(a+f T)) (futurePath T f) ≤ (τ-T : ℝ≥0) := by
    apply (firstPassage_le_iff _ _ _).mpr
    refine ⟨τ-T,le_rfl,?_⟩
    rw [futurePath_eval,add_tsub_cancel_of_le hT.le]
    have hhit := firstPassage_attained (-a) f hfin
    change f τ ≤ -a at hhit
    linarith
  have hfuture : firstPassage (-(a+f T)) (futurePath T f) ≠ ⊤ :=
    ne_of_lt (hupper.trans_lt ENNReal.coe_lt_top)
  let r := (firstPassage (-(a+f T)) (futurePath T f)).toNNReal
  have hcr : (r : ℝ≥0∞) = firstPassage (-(a+f T)) (futurePath T f) :=
    ENNReal.coe_toNNReal hfuture
  have hr : r ≤ τ-T := by rwa [← hcr,ENNReal.coe_le_coe] at hupper
  have hτ : τ ≤ T+r := by
    have hh := firstPassage_attained (-(a+f T)) (futurePath T f) hfuture
    change futurePath T f r ≤ -(a+f T) at hh
    rw [futurePath_eval] at hh
    have h := (firstPassage_le_iff (-a) f (T+r)).mpr ⟨T+r,le_rfl,by linarith⟩
    rwa [← hc,ENNReal.coe_le_coe] at h
  have hlow : T+r ≤ τ := by
    calc
      T+r ≤ T+(τ-T) := by simpa only [add_comm] using add_le_add_left hr T
      _ = τ := add_tsub_cancel_of_le hT.le
  have he : τ = T+r := le_antisymm hτ hlow
  change (τ : ℝ) = (T : ℝ)+(r : ℝ)
  exact_mod_cast he

private theorem measurable_joint_realTime : Measurable (fun p : ℝ × Path ↦ realTime p.1 p.2) :=
  NNReal.continuous_coe.measurable.comp measurable_joint_firstPassage.ennreal_toNNReal

private theorem shifted_passage_lintegral (h : ℝ) (hh : 0 < h) (T : ℝ≥0)
    (J : ℝ → ℝ≥0∞) (hJ : Measurable J) :
    (∫⁻ g, J ((T : ℝ)+realTime (-h) g) ∂pathLaw) =
      ∫⁻ s in Ioi (T : ℝ), BrownianFirstPassageDensityGeometry.density h (s-(T : ℝ))*J s := by
  have hc := BrownianFirstPassageDensityLaw.lintegral_firstPassage_density h hh
    (fun u ↦ J ((T : ℝ)+u)) (hJ.comp (measurable_const.add measurable_id))
  change (∫⁻ g, J ((T : ℝ)+realTime (-h) g) ∂pathLaw) =
    ∫⁻ u : ℝ, BrownianFirstPassageDensityGeometry.density h u*J ((T : ℝ)+u) at hc
  rw [hc]
  have hm : Measurable (fun s : ℝ ↦
      BrownianFirstPassageDensityGeometry.density h (s-(T : ℝ))*J s) :=
    ((BrownianFirstPassageDensityGeometry.measurable_density h).comp
      (measurable_id.sub_const _)).mul hJ
  calc
    _ = ∫⁻ s : ℝ, BrownianFirstPassageDensityGeometry.density h (s-(T : ℝ))*J s := by
      simpa only [Function.comp_def,add_sub_cancel_left] using
        (measurePreserving_add_left (volume : Measure ℝ) (T : ℝ)).lintegral_comp hm
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Ioi (T : ℝ)
      · rw [indicator_of_mem hs]
      · have hz : BrownianFirstPassageDensityGeometry.density h (s-(T : ℝ)) = 0 := by
          rw [BrownianFirstPassageDensityGeometry.density,
            BrownianFirstPassageDensityGeometry.densityReal_eq_zero_of_nonpos h _
              (sub_nonpos.mpr (not_lt.mp hs)),ENNReal.ofReal_zero]
        simp only [hz,zero_mul,indicator_of_notMem hs]

private def futureKernel (n : ℕ) (T : ℝ≥0)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (T : ℝ), BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
    (s-(T : ℝ))*H (v,s)

private theorem measurable_shifted_joint_density (n : ℕ) (T : ℝ≥0) :
    Measurable (fun q : FreeVector (n+1) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) (q.2-(T : ℝ))) := by
  have hl : Measurable (fun v : FreeVector (n+1) ↦ v (Fin.last n)) := measurable_pi_apply _
  have hp : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      (q.1 (Fin.last n),q.2-(T : ℝ))) :=
    (hl.comp measurable_fst).prodMk (measurable_snd.sub_const _)
  exact BrownianHeatResolvent.measurable_joint_passageDensity.comp hp

private theorem measurable_futureKernel (n : ℕ) (T : ℝ≥0)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    Measurable (futureKernel n T H) := by
  have hm : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n)) (q.2-(T : ℝ))*H q) :=
    (measurable_shifted_joint_density n T).mul hH
  exact hm.lintegral_prod_right' (ν := volume.restrict (Ioi (T : ℝ)))

theorem actual_ordered_prefix_firstPassage_lintegral (n : ℕ) (a : ℝ) (ha : 0 < a)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f in survival (-a) (times (Fin.last (n+1))),
      H ((fun i : Fin (n+1) ↦ a+f (times i.succ)),realTime (-a) f) ∂pathLaw) =
      ∫⁻ v : FreeVector (n+1), jointDensity (n+1) a (orderedGaps (n+1) times) v*
        (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
          BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
            (s-(times (Fin.last (n+1)) : ℝ))*H (v,s)) := by
  let T := times (Fin.last (n+1))
  let F : Path × Path → ℝ≥0∞ := fun p ↦ H (coordinates n a times p.1,
    (T : ℝ)+realTime (-(a+p.1 T)) p.2)
  have hF : Measurable F := hH.comp
    (((measurable_coordinates n a times).comp measurable_fst).prodMk
      (measurable_const.add (measurable_joint_realTime.comp
        ((measurable_const.add ((continuous_eval T).measurable.comp measurable_fst)).neg.prodMk
          measurable_snd))))
  have hj := (measurable_pastPath T).prodMk (measurable_futurePath T)
  have hfinite := BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-a) (neg_neg_of_pos ha)
  calc
    _ = ∫⁻ f in survival (-a) T, F (pastPath T f,futurePath T f) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hfinite,ae_restrict_mem (measurableSet_survival (-a) T)]
        with f hf hs
      change H (coordinates n a times f,realTime (-a) f) = _
      rw [realTime_after_survival a T f hs hf]
      change H (coordinates n a times f,(T : ℝ)+realTime (-(a+f T)) (futurePath T f)) =
        H (coordinates n a times (pastPath T f),
          (T : ℝ)+realTime (-(a+pastPath T f T)) (futurePath T f))
      rw [coordinates_past n a times hstrict.monotone]
      simp only [pastPath_eval,min_self]
    _ = ∫⁻ p in survival (-a) T, ∫⁻ g, F (p,g) ∂pathLaw ∂pastLaw T := by
      rw [← lintegral_map hF hj,survival_restricted_past_future_jointLaw,
        lintegral_prod _ hF.aemeasurable]
    _ = ∫⁻ p in survival (-a) T, futureKernel n T H (coordinates n a times p) ∂pastLaw T := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_survival (-a) T)] with p hp
      have hheight : 0 < a+p T := by
        have hs := (mem_survival_iff (-a) T p).mp hp T le_rfl
        linarith
      change (∫⁻ g, H (coordinates n a times p,(T : ℝ)+realTime (-(a+p T)) g) ∂pathLaw) =
        ∫⁻ s in Ioi (T : ℝ), BrownianFirstPassageDensityGeometry.density (a+p T)
          (s-(T : ℝ))*H (coordinates n a times p,s)
      exact shifted_passage_lintegral (a+p T) hheight T
        (fun s ↦ H (coordinates n a times p,s))
        (hH.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ f in survival (-a) T, futureKernel n T H (coordinates n a times f) ∂pathLaw := by
      have hJ : Measurable (fun p : Path ↦ futureKernel n T H (coordinates n a times p)) :=
        (measurable_futureKernel n T H hH).comp (measurable_coordinates n a times)
      rw [← survival_restricted_past_law a T,
        lintegral_map hJ (measurable_pastPath T)]
      exact lintegral_congr (fun f ↦ congrArg (futureKernel n T H)
        (coordinates_past n a times hstrict.monotone f))
    _ = _ := lintegral_ordered_free_density a ha (n+1) times hstrict hzero
      (measurable_futureKernel n T H hH)

def firstPassageJointDensity (n : ℕ) (a : ℝ) (times : Fin (n+2) → ℝ≥0)
    (q : FreeVector (n+1) × ℝ) : ℝ≥0∞ :=
  (Ioi (times (Fin.last (n+1)) : ℝ)).indicator
    (fun s ↦ jointDensity (n+1) a (orderedGaps (n+1) times) q.1*
      BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n))
        (s-(times (Fin.last (n+1)) : ℝ))) q.2

private theorem measurable_firstPassageJointDensity (n : ℕ) (a : ℝ)
    (times : Fin (n+2) → ℝ≥0) : Measurable (firstPassageJointDensity n a times) := by
  have hm : Measurable (fun q : FreeVector (n+1) × ℝ ↦
      jointDensity (n+1) a (orderedGaps (n+1) times) q.1*
        BrownianFirstPassageDensityGeometry.density (q.1 (Fin.last n))
          (q.2-(times (Fin.last (n+1)) : ℝ))) :=
    ((measurable_jointDensity (n+1) a _).comp measurable_fst).mul
      (measurable_shifted_joint_density n (times (Fin.last (n+1))))
  exact hm.indicator (measurable_snd measurableSet_Ioi)

private theorem lintegral_firstPassageJointDensity (n : ℕ) (a : ℝ)
    (times : Fin (n+2) → ℝ≥0) (H : FreeVector (n+1) × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ q, firstPassageJointDensity n a times q*H q) =
      ∫⁻ v : FreeVector (n+1), jointDensity (n+1) a (orderedGaps (n+1) times) v*
        (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
          BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
            (s-(times (Fin.last (n+1)) : ℝ))*H (v,s)) := by
  have hmj : Measurable (fun q : FreeVector (n+1) × ℝ ↦ firstPassageJointDensity n a times q*H q) :=
    (measurable_firstPassageJointDensity n a times).mul hH
  change (∫⁻ q : FreeVector (n+1) × ℝ, firstPassageJointDensity n a times q*H q
    ∂(volume : Measure (FreeVector (n+1))).prod (volume : Measure ℝ)) = _
  rw [lintegral_prod (μ := (volume : Measure (FreeVector (n+1)))) (ν := (volume : Measure ℝ))
    (fun q : FreeVector (n+1) × ℝ ↦ firstPassageJointDensity n a times q*H q)
    hmj.aemeasurable]
  apply lintegral_congr
  intro v
  have hm : Measurable (fun s : ℝ ↦
      BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
        (s-(times (Fin.last (n+1)) : ℝ))*H (v,s)) :=
    ((BrownianFirstPassageDensityGeometry.measurable_density _).comp
      (measurable_id.sub_const _)).mul (hH.comp (measurable_const.prodMk measurable_id))
  rw [← lintegral_const_mul _ hm,← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioi (times (Fin.last (n+1)) : ℝ) <;>
    simp [firstPassageJointDensity,hs,mul_assoc]

theorem actual_ordered_prefix_firstPassage_jointLaw (n : ℕ) (a : ℝ) (ha : 0 < a)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (pathLaw.restrict (survival (-a) (times (Fin.last (n+1))))).map
      (fun f : Path ↦ ((fun i : Fin (n+1) ↦ a+f (times i.succ)),realTime (-a) f)) =
        volume.withDensity (firstPassageJointDensity n a times) := by
  have hm : Measurable (fun f : Path ↦
      ((fun i : Fin (n+1) ↦ a+f (times i.succ)),realTime (-a) f)) :=
    (measurable_coordinates n a times).prodMk (measurable_realTime (-a))
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH hm,actual_ordered_prefix_firstPassage_lintegral n a ha times hstrict hzero H hH,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_firstPassageJointDensity n a times) hH]
  exact (lintegral_firstPassageJointDensity n a times H hH).symm

end PerronWright.BrownianKilledPrefixFirstPassageJointDensity
