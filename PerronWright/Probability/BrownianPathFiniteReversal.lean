import PerronWright.Probability.BrownianMinimumNegative
import PerronWright.Probability.BrownianPathIndependentIncrements

/-! # Genuine Brownian reversal on a finite interval and interior minimum

Reverse the increments on [0,T] and continue with the original future
increments. Its Gaussian finite transforms have the actual Brownian mean
and covariance, hence the full continuous path law is Brownian. Applying
the already proved negative-minimum result excludes the terminal time
as a minimum. No time-reversal or interior-minimum interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPathFiniteReversal

open BrownianPathLaw BrownianPathIndependentIncrements
open BrownianMinimumNegative ContinuousPathLeastMinimum

def reversal (T t : ℝ≥0) (f : Path) : ℝ := f (T-t)+f (max t T)-2*f T

def reversePath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ reversal T t f,
    (((continuous_path f).comp (continuous_const.sub continuous_id)).add
      ((continuous_path f).comp (continuous_id.max continuous_const))).sub continuous_const⟩

theorem continuous_reversePath (T : ℝ≥0) : Continuous (reversePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.eval (continuous_const.sub continuous_snd)).add
    (continuous_fst.eval (continuous_snd.max continuous_const))).sub
      (((continuous_eval T).comp continuous_fst).const_mul 2)

theorem reversal_isGaussianProcess (T : ℝ≥0) : IsGaussianProcess (reversal T) pathLaw := by
  apply isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.of_isGaussianProcess
  intro t
  let I : Finset ℝ≥0 := {T-t,max t T,T}
  let L : (I → ℝ) →L[ℝ] ℝ :=
    { toFun x := x ⟨T-t,by simp [I]⟩+x ⟨max t T,by simp [I]⟩-2*x ⟨T,by simp [I]⟩
      map_add' x y := by simp; ring
      map_smul' c x := by simp; ring }
  exact ⟨I,L,fun _ ↦ rfl⟩

theorem integral_reversal (T t : ℝ≥0) : (∫ f, reversal T t f ∂pathLaw) = 0 := by
  unfold reversal
  have hi := isBrownian_pathLaw.toIsPreBrownianReal.integrable_eval
  have h1 : Integrable (fun f : Path ↦ f (T-t)+f (max t T)) pathLaw := (hi _).add (hi _)
  have h2 : Integrable (fun f : Path ↦ 2*f T) pathLaw := (hi T).const_mul 2
  rw [integral_sub h1 h2,integral_add (hi (T-t)) (hi (max t T)),
    integral_const_mul]
  simp only [isBrownian_pathLaw.toIsPreBrownianReal.integral_eval]
  ring

private theorem covariance_formula (T s t : ℝ≥0) :
    cov[reversal T s,reversal T t;pathLaw] =
      (min (T-s) (T-t) : ℝ≥0)+(min (T-s) (max t T) : ℝ≥0)+
      (min (max s T) (T-t) : ℝ≥0)+(min (max s T) (max t T) : ℝ≥0)-
      2*((min (T-s) T : ℝ≥0)+(min (max s T) T : ℝ≥0))-
      2*((min T (T-t) : ℝ≥0)+(min T (max t T) : ℝ≥0))+4*(T : ℝ) := by
  have hm (r : ℝ≥0) : MemLp (fun f : Path ↦ f r) 2 pathLaw :=
    (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
  change cov[(fun f : Path ↦ f (T-s))+(fun f ↦ f (max s T))-(fun f ↦ 2*f T),
    (fun f : Path ↦ f (T-t))+(fun f ↦ f (max t T))-(fun f ↦ 2*f T);pathLaw] = _
  rw [covariance_sub_sub ((hm _).add (hm _)) ((hm T).const_mul 2)
    ((hm _).add (hm _)) ((hm T).const_mul 2)]
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_left (hm _) (hm _) (hm T),covariance_add_right (hm T) (hm _) (hm _)]
  simp only [isBrownian_pathLaw.toIsPreBrownianReal.covariance_eval,min_self]
  ring

theorem covariance_reversal (T s t : ℝ≥0) (hst : s ≤ t) :
    cov[reversal T s,reversal T t;pathLaw] = (s : ℝ) := by
  rw [covariance_formula]
  by_cases ht : t ≤ T
  · have hs := hst.trans ht
    have hr := tsub_le_tsub_left hst T
    simp only [max_eq_right hs,max_eq_right ht,min_self,
      min_eq_right hr,min_eq_left (tsub_le_self (a := T) (b := s)),
      min_eq_right (tsub_le_self (a := T) (b := t)),NNReal.coe_sub hs,NNReal.coe_sub ht]
    ring
  · have ht' := le_of_not_ge ht
    by_cases hs : s ≤ T
    · have hA : T-s ≤ t := (tsub_le_self : T-s ≤ T).trans ht'
      simp only [max_eq_right hs,max_eq_left ht',tsub_eq_zero_of_le ht',min_zero,
        min_eq_left hA,min_eq_left ht',min_self,
        min_eq_left (tsub_le_self (a := T) (b := s)),NNReal.coe_zero,NNReal.coe_sub hs]
      ring
    · have hs' := le_of_not_ge hs
      simp only [max_eq_left hs',max_eq_left ht',tsub_eq_zero_of_le hs',
        tsub_eq_zero_of_le ht',min_zero,zero_min,min_eq_left hst,
        min_eq_right hs',min_eq_left ht',NNReal.coe_zero]
      ring

theorem reversal_isPreBrownian (T : ℝ≥0) :
    IsPreBrownianReal (reversal T) pathLaw :=
  (reversal_isGaussianProcess T).isPreBrownianReal_of_covariance
    (integral_reversal T) (fun s t hst ↦ covariance_reversal T s t hst)

theorem reversePath_law (T : ℝ≥0) : pathLaw.map (reversePath T) = pathLaw :=
  map_eq_pathLaw_of_preBrownian _ (continuous_reversePath T).measurable
    (reversal_isPreBrownian T)

theorem ae_minimumValue_lt_endpoint (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, minimumValue T f < f T := by
  have he : ∀ᵐ f ∂pathLaw, minimumValue T (reversePath T f) < 0 := by
    apply (ae_map_iff (continuous_reversePath T).measurable.aemeasurable
      ((continuous_minimumValue T).measurable measurableSet_Iio)).mp
    rw [reversePath_law]
    exact ae_minimumValue_negative T hT
  filter_upwards [he] with f hf
  obtain ⟨s,hs,hval,_⟩ := exists_minimumValue T (reversePath T f)
  rw [hval] at hf
  change f (T-s)+f (max s T)-2*f T < 0 at hf
  rw [max_eq_right hs] at hf
  exact (minimumValue_le T f (T-s) tsub_le_self).trans_lt (by linarith)

theorem ae_leastMinimizer_interior (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, 0 < leastMinimizer T f ∧ leastMinimizer T f < T := by
  filter_upwards [ae_minimumValue_lt_start T hT,ae_minimumValue_lt_endpoint T hT] with f h0 hEnd
  have hn0 : leastMinimizer T f ≠ 0 := by
    intro he
    rw [← leastMinimizer_value T f,he] at h0
    exact lt_irrefl _ h0
  have hnT : leastMinimizer T f ≠ T := by
    intro he
    rw [← leastMinimizer_value T f,he] at hEnd
    exact lt_irrefl _ hEnd
  exact ⟨pos_iff_ne_zero.mpr hn0,lt_of_le_of_ne (leastMinimizer_le_time T f) hnT⟩

end PerronWright.BrownianPathFiniteReversal
