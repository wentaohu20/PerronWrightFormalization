import PerronWright.Probability.BrownianPathSeparatedMinima
import PerronWright.Probability.BrownianParabolicDriftTilt
import PerronWright.Probability.BrownianPathReflectionLaw

/-! # Actual Brownian and parabolic compact-prefix minimum uniqueness

Two distinct minimizing times lie in separated intervals with rational
left cutoffs. The proved Gaussian gap null events exclude them. The
actual stopped parabolic density transfers those same Borel null events.
Neither terminal has a minimum-uniqueness hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPathMinimumUnique

open BrownianPathLaw ContinuousPathLeastMinimum ContinuousPathIntervalMinimum
open BrownianPathSeparatedMinima BrownianPathReflectionLaw
open BrownianParabolicDriftTiltGeometry BrownianParabolicDriftTilt

private theorem unique_of_separated (T : ℝ≥0) (f : Path)
    (hall : ∀ a b : ℚ, Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) →
      Real.toNNReal (b : ℝ) ≤ T →
      intervalMinimum 0 (Real.toNNReal (a : ℝ)) f ≠
        intervalMinimum (Real.toNNReal (b : ℝ)) T f) :
    ∀ t : ℝ≥0, t ≤ T → f t = minimumValue T f → t = leastMinimizer T f := by
  have hno (s t : ℝ≥0) (hst : s < t) (ht : t ≤ T)
      (hsmin : f s = minimumValue T f) (htmin : f t = minimumValue T f) : False := by
    obtain ⟨a,hsa,hat⟩ := exists_rat_btwn (show (s : ℝ) < t from hst)
    obtain ⟨b,hab,hbt⟩ := exists_rat_btwn hat
    have ha0 : 0 ≤ (a : ℝ) := s.coe_nonneg.trans hsa.le
    have hsa' : s ≤ Real.toNNReal (a : ℝ) := (Real.le_toNNReal_iff_coe_le ha0).mpr hsa.le
    have hab' : Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) :=
      (Real.toNNReal_lt_toNNReal_iff (ha0.trans_lt hab)).mpr hab
    have hbt' : Real.toNNReal (b : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.mpr hbt.le
    have hbT := hbt'.trans ht
    have haT := hab'.le.trans hbT
    have hleft : intervalMinimum 0 (Real.toNNReal (a : ℝ)) f = minimumValue T f := by
      apply intervalMinimum_eq_of_attains 0 _ zero_le
      · intro u hu
        exact minimumValue_le T f u (hu.2.trans haT)
      · exact ⟨s,⟨zero_le,hsa'⟩,hsmin⟩
    have hright : intervalMinimum (Real.toNNReal (b : ℝ)) T f = minimumValue T f := by
      apply intervalMinimum_eq_of_attains _ _ hbT
      · intro u hu
        exact minimumValue_le T f u hu.2
      · exact ⟨t,⟨hbt',ht⟩,htmin⟩
    exact hall a b hab' hbT (hleft.trans hright.symm)
  intro t ht he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact hno t (leastMinimizer T f) hlt (leastMinimizer_le_time T f) he (leastMinimizer_value T f)
  · exact hno (leastMinimizer T f) t hgt ht (leastMinimizer_value T f) he

theorem ae_unique_minimum (T : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, ∀ t : ℝ≥0, t ≤ T → f t = minimumValue T f → t = leastMinimizer T f := by
  have hall : ∀ᵐ f ∂pathLaw, ∀ a b : ℚ,
      Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) → Real.toNNReal (b : ℝ) ≤ T →
      intervalMinimum 0 (Real.toNNReal (a : ℝ)) f ≠
        intervalMinimum (Real.toNNReal (b : ℝ)) T f := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ)
    · by_cases hbT : Real.toNNReal (b : ℝ) ≤ T
      · exact (ae_separated_interval_minima_ne 0 _ _ T zero_le hab hbT).mono
          (fun f hf _ _ ↦ hf)
      · exact Eventually.of_forall (fun _ _ h ↦ (hbT h).elim)
    · exact Eventually.of_forall (fun _ h ↦ (hab h).elim)
  exact hall.mono (fun f hf ↦ unique_of_separated T f hf)

private theorem intervalMinimum_stopped (l u T : ℝ≥0) (hu : u ≤ T) (f : Path) :
    intervalMinimum l u (BrownianEndpointDriftTilt.stoppedPath T f) = intervalMinimum l u f := by
  unfold intervalMinimum
  congr 1
  apply image_congr
  intro t ht
  rw [BrownianEndpointDriftTilt.stoppedPath_eval,min_eq_left (ht.2.trans hu)]

private theorem ae_parabolic_separated (lambda : ℝ) (T a b : ℝ≥0) (hT : 0 < T)
    (hab : a < b) (hbT : b ≤ T) :
    ∀ᵐ f ∂pathLaw, intervalMinimum 0 a (driftPath lambda f) ≠
      intervalMinimum b T (driftPath lambda f) := by
  let P : Path → Prop := fun f ↦ intervalMinimum 0 a f ≠ intervalMinimum b T f
  have hP : MeasurableSet {f : Path | P f} :=
    (measurableSet_eq_fun (continuous_intervalMinimum 0 a).measurable
      (continuous_intervalMinimum b T).measurable).compl
  have hs (f : Path) : P (BrownianEndpointDriftTilt.stoppedPath T f) ↔ P f := by
    dsimp only [P]
    rw [intervalMinimum_stopped 0 a T (hab.le.trans hbT) f,
      intervalMinimum_stopped b T T le_rfl f]
  have hw : ∀ᵐ f ∂pathLaw.withDensity (density lambda T), P f :=
    (withDensity_absolutelyContinuous pathLaw (density lambda T)).ae_le
      (ae_separated_interval_minima_ne 0 a b T zero_le hab hbT)
  have hstop : ∀ᵐ f ∂(pathLaw.withDensity (density lambda T)).map
      (BrownianEndpointDriftTilt.stoppedPath T), P f :=
    (ae_map_iff (BrownianEndpointDriftTilt.measurable_stoppedPath T).aemeasurable hP).mpr
      (hw.mono (fun f hf ↦ (hs f).mpr hf))
  rw [← actual_stopped_parabolic_law_eq_weighted lambda T hT] at hstop
  have hd := (ae_map_iff (measurable_stoppedParabolicPath lambda T).aemeasurable hP).mp hstop
  filter_upwards [hd] with f hf
  have he : BrownianEndpointDriftTilt.stoppedPath T (driftPath lambda f) =
      stoppedParabolicPath lambda T f := by
    apply ContinuousMap.ext
    intro t
    rfl
  exact (hs (driftPath lambda f)).mp (he.symm ▸ hf)

theorem ae_actual_parabolic_unique_minimum (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ t : ℝ≥0, t ≤ T → driftPath lambda f t =
      minimumValue T (driftPath lambda f) → t = leastMinimizer T (driftPath lambda f) := by
  have hall : ∀ᵐ f ∂pathLaw, ∀ a b : ℚ,
      Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ) → Real.toNNReal (b : ℝ) ≤ T →
      intervalMinimum 0 (Real.toNNReal (a : ℝ)) (driftPath lambda f) ≠
        intervalMinimum (Real.toNNReal (b : ℝ)) T (driftPath lambda f) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : Real.toNNReal (a : ℝ) < Real.toNNReal (b : ℝ)
    · by_cases hbT : Real.toNNReal (b : ℝ) ≤ T
      · exact (ae_parabolic_separated lambda T _ _ hT hab hbT).mono (fun f hf _ _ ↦ hf)
      · exact Eventually.of_forall (fun _ _ h ↦ (hbT h).elim)
    · exact Eventually.of_forall (fun _ h ↦ (hab h).elim)
  exact hall.mono (fun f hf ↦ unique_of_separated T (driftPath lambda f) hf)

end PerronWright.BrownianPathMinimumUnique
