import PerronWright.Probability.BrownianFirstPassageStrongMarkov
import PerronWright.Probability.BrownianEndpointDriftTilt

/-! # Actual exponential normalization at bounded first passage

The whole-future product law and the genuine Gaussian endpoint mgf
normalize the exponential at the literal bounded first passage.
No optional-stopping, martingale, or exponential-hitting interface is
assumed. All uses of integration before boundedness are nonnegative.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageExponential

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageReflection BrownianFirstPassageStrongMarkov
open BrownianEndpointDriftTilt

def exponential (u : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (u*x-(t : ℝ)*u^2/2)

theorem continuous_exponential (u : ℝ) :
    Continuous (fun p : ℝ≥0 × ℝ ↦ exponential u p.1 p.2) := by
  unfold exponential
  fun_prop

theorem lintegral_endpoint_exponential (T : ℝ≥0) (u : ℝ) :
    (∫⁻ f : Path, ENNReal.ofReal (exponential u T (f T)) ∂pathLaw) = 1 := by
  have hi : Integrable (fun f : Path ↦ exponential u T (f T)) pathLaw := by
    unfold exponential
    simp only [Real.exp_sub]
    exact (integrable_exp_mul_endpoint T u).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
  unfold exponential
  simp only [Real.exp_sub,integral_div,integral_exp_mul_endpoint]
  rw [div_self (Real.exp_ne_zero _),ENNReal.ofReal_one]

def jointExponential (T : ℝ≥0) (u : ℝ) (z : ℝ≥0 × Path) (q : Path) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp
    (u*(z.2 (min z.1 T)+q (T-min z.1 T))-(T : ℝ)*u^2/2))

theorem measurable_jointExponential (T : ℝ≥0) (u : ℝ) :
    Measurable (fun p : (ℝ≥0 × Path) × Path ↦ jointExponential T u p.1 p.2) := by
  have hs : Continuous (fun p : (ℝ≥0 × Path) × Path ↦ min p.1.1 T) :=
    continuous_fst.fst.min continuous_const
  have he : Continuous (fun p : (ℝ≥0 × Path) × Path ↦
      p.1.2 (min p.1.1 T)+p.2 (T-min p.1.1 T)) :=
    (continuous_joint_eval.comp (continuous_fst.snd.prodMk hs)).add
      (continuous_joint_eval.comp (continuous_snd.prodMk (continuous_const.sub hs)))
  exact (Real.continuous_exp.comp ((he.const_mul u).sub continuous_const)).measurable.ennreal_ofReal

theorem jointExponential_factor (T : ℝ≥0) (u : ℝ) (z : ℝ≥0 × Path) (q : Path) :
    jointExponential T u z q =
      ENNReal.ofReal (exponential u (min z.1 T) (z.2 (min z.1 T)))*
        ENNReal.ofReal (exponential u (T-min z.1 T) (q (T-min z.1 T))) := by
  have ht : ((min z.1 T : ℝ≥0) : ℝ)+((T-min z.1 T : ℝ≥0) : ℝ) = (T : ℝ) := by
    rw [NNReal.coe_sub (min_le_right _ _)]
    ring
  unfold jointExponential exponential
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  nlinarith

theorem lintegral_jointExponential_right (T : ℝ≥0) (u : ℝ) (z : ℝ≥0 × Path) :
    (∫⁻ q : Path, jointExponential T u z q ∂pathLaw) =
      ENNReal.ofReal (exponential u (min z.1 T) (z.2 (min z.1 T))) := by
  simp only [jointExponential_factor]
  rw [lintegral_const_mul]
  · rw [lintegral_endpoint_exponential,mul_one]
  · exact ((continuous_exponential u).comp
      (continuous_const.prodMk (continuous_eval _))).measurable.ennreal_ofReal

theorem jointExponential_at_bounded (level : ℝ) (T : ℝ≥0) (u : ℝ) (f : Path) :
    jointExponential T u (boundedPast level T f) (boundedFuture level T f) =
      ENNReal.ofReal (exponential u T (f T)) := by
  have ht := cappedTime_le level T f
  have he : cappedTime level T f+(T-cappedTime level T f) = T := add_tsub_cancel_of_le ht
  unfold jointExponential boundedPast boundedFuture
  simp only [min_eq_left ht,pastPath_eval,futurePath_eval,min_self,he]
  unfold exponential
  congr 2
  ring

theorem lintegral_capped_exponential (level : ℝ) (T : ℝ≥0) (u : ℝ) :
    (∫⁻ f : Path, ENNReal.ofReal
      (exponential u (cappedTime level T f) (f (cappedTime level T f))) ∂pathLaw) = 1 := by
  have hJ := measurable_jointExponential T u
  have hB := (measurable_boundedPast level T).prodMk (measurable_boundedFuture level T)
  have hZ : Measurable (fun z : ℝ≥0 × Path ↦
      ENNReal.ofReal (exponential u (min z.1 T) (z.2 (min z.1 T)))) := by
    have hs : Continuous (fun z : ℝ≥0 × Path ↦ min z.1 T) :=
      continuous_fst.min continuous_const
    exact ((continuous_exponential u).comp
      (hs.prodMk (continuous_joint_eval.comp (continuous_snd.prodMk hs)))).measurable.ennreal_ofReal
  calc
    _ = ∫⁻ z : ℝ≥0 × Path,
        ENNReal.ofReal (exponential u (min z.1 T) (z.2 (min z.1 T)))
          ∂pathLaw.map (boundedPast level T) := by
      rw [lintegral_map hZ (measurable_boundedPast level T)]
      apply lintegral_congr
      intro f
      unfold boundedPast
      simp only [min_eq_left (cappedTime_le level T f),pastPath_eval,min_self]
    _ = ∫⁻ p : (ℝ≥0 × Path) × Path, jointExponential T u p.1 p.2
        ∂(pathLaw.map (boundedPast level T)).prod pathLaw := by
      rw [lintegral_prod _ hJ.aemeasurable]
      exact (lintegral_congr (fun z ↦ lintegral_jointExponential_right T u z)).symm
    _ = ∫⁻ f : Path, ENNReal.ofReal (exponential u T (f T)) ∂pathLaw := by
      rw [← bounded_jointLaw level T,lintegral_map hJ hB]
      exact lintegral_congr (jointExponential_at_bounded level T u)
    _ = 1 := lintegral_endpoint_exponential T u

theorem capped_height_ge_level (level : ℝ) (T : ℝ≥0) (f : Path)
    (hstart : level < f 0) : level ≤ f (cappedTime level T f) := by
  by_cases ht : firstPassage level f ≤ (T : ℝ≥0∞)
  · have hfin : firstPassage level f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
    rw [cappedTime,min_eq_left ht]
    exact (firstPassage_exact_level level f hstart hfin).ge
  · have hb : (T : ℝ≥0∞) < firstPassage level f := lt_of_not_ge ht
    rw [cappedTime,min_eq_right hb.le,ENNReal.toNNReal_coe]
    exact (before_firstPassage level f T hb).le

theorem capped_exponential_le (level : ℝ) (T : ℝ≥0) (u : ℝ) (hu : u ≤ 0)
    (f : Path) (hstart : level < f 0) :
    exponential u (cappedTime level T f) (f (cappedTime level T f)) ≤ Real.exp (u*level) := by
  unfold exponential
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonpos_left (capped_height_ge_level level T f hstart) hu
  have ht : 0 ≤ (cappedTime level T f : ℝ)*u^2/2 := by positivity
  linarith

theorem measurable_capped_exponential (level : ℝ) (T : ℝ≥0) (u : ℝ) :
    Measurable (fun f : Path ↦ exponential u (cappedTime level T f) (f (cappedTime level T f))) :=
  (continuous_exponential u).measurable.comp
    ((measurable_cappedTime level T).prodMk
      (continuous_joint_eval.measurable.comp (measurable_id.prodMk (measurable_cappedTime level T))))

theorem integrable_capped_exponential (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (u : ℝ) (hu : u ≤ 0) :
    Integrable (fun f : Path ↦ exponential u (cappedTime level T f) (f (cappedTime level T f)))
      pathLaw := by
  apply Integrable.mono' (integrable_const (Real.exp (u*level)))
    (measurable_capped_exponential level T u).aestronglyMeasurable
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  rw [Real.norm_eq_abs,abs_of_pos (show 0 < exponential u (cappedTime level T f)
    (f (cappedTime level T f)) from Real.exp_pos _)]
  exact capped_exponential_le level T u hu f (by simpa only [hf] using hlevel)

theorem integral_capped_exponential (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (u : ℝ) (hu : u ≤ 0) :
    (∫ f : Path, exponential u (cappedTime level T f) (f (cappedTime level T f)) ∂pathLaw) = 1 := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun _ ↦ (Real.exp_pos _).le)) (by norm_num : (0 : ℝ) ≤ 1)).mp
  change ENNReal.ofReal (∫ f : Path,
    exponential u (cappedTime level T f) (f (cappedTime level T f)) ∂pathLaw) = ENNReal.ofReal 1
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_capped_exponential level hlevel T u hu)
      (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le)),lintegral_capped_exponential]
  norm_num

end PerronWright.BrownianFirstPassageExponential
