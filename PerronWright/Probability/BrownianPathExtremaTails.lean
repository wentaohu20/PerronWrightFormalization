import PerronWright.Probability.BrownianKilledTransitionKernel
import PerronWright.Probability.BrownianEndpointDriftTilt
import Mathlib.Probability.Moments.Basic

/-! # Actual Brownian finite-horizon extrema

The literal first-passage reflection identity gives exact Gaussian tails
of the running minimum. Actual path sign symmetry gives the maximum tail.
The attained absolute path maximum therefore has a Gaussian union bound,
and the proved endpoint MGF gives its explicit exponential tail bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPathExtremaTails

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathReflection
open ContinuousPathFirstPassage BrownianKilledTransitionKernel BrownianEndpointDriftTilt

def runningMaximum (f : Path) (T : ℝ≥0) : ℝ := -runningMinimum (negPath f) T

theorem le_runningMaximum (f : Path) {s T : ℝ≥0} (hs : s ≤ T) :
    f s ≤ runningMaximum f T := by
  have h := runningMinimum_le (continuous_path (negPath f)) hs
  change runningMinimum (negPath f) T ≤ -f s at h
  simpa only [runningMaximum,neg_neg] using neg_le_neg h

theorem runningMaximum_attained (f : Path) (T : ℝ≥0) :
    ∃ s ∈ Icc 0 T, runningMaximum f T = f s := by
  obtain ⟨s,hs,he⟩ := runningMinimum_attained (continuous_path (negPath f)) T
  exact ⟨s,hs,by simp only [runningMaximum,he,negPath_eval,neg_neg]⟩

theorem continuous_runningMaximum (T : ℝ≥0) : Continuous (fun f : Path ↦ runningMaximum f T) :=
  ((continuous_minimum_at T).comp continuous_negPath).neg

theorem continuous_joint_runningMaximum :
    Continuous (fun p : Path × ℝ≥0 ↦ runningMaximum p.1 p.2) :=
  (BrownianPathReflectionLaw.continuous_joint_minimum.comp
    ((continuous_negPath.comp continuous_fst).prodMk continuous_snd)).neg

def absolutePath (f : Path) : Path := ⟨fun t ↦ ‖f t‖,(continuous_path f).norm⟩

@[simp] theorem absolutePath_eval (f : Path) (t : ℝ≥0) : absolutePath f t = ‖f t‖ := rfl

theorem continuous_absolutePath : Continuous absolutePath := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_joint_eval.norm

/-- The actual attained supremum of the path norm on the whole interval. -/
def windowSup (f : Path) (T : ℝ≥0) : ℝ := runningMaximum (absolutePath f) T

theorem norm_le_windowSup (f : Path) {s T : ℝ≥0} (hs : s ≤ T) :
    ‖f s‖ ≤ windowSup f T := le_runningMaximum (absolutePath f) hs

theorem windowSup_attained (f : Path) (T : ℝ≥0) :
    ∃ s ∈ Icc 0 T, windowSup f T = ‖f s‖ := runningMaximum_attained (absolutePath f) T

theorem windowSup_nonneg (f : Path) (T : ℝ≥0) : 0 ≤ windowSup f T :=
  (norm_nonneg (f 0)).trans (norm_le_windowSup f (zero_le : (0 : ℝ≥0) ≤ T))

theorem windowSup_le_iff (f : Path) (T : ℝ≥0) (b : ℝ) :
    windowSup f T ≤ b ↔ ∀ s : ℝ≥0, s ≤ T → ‖f s‖ ≤ b := by
  constructor
  · intro h s hs
    exact (norm_le_windowSup f hs).trans h
  · intro h
    obtain ⟨s,hs,he⟩ := windowSup_attained f T
    rw [he]
    exact h s hs.2

theorem windowSup_eq_max (f : Path) (T : ℝ≥0) :
    windowSup f T = max (runningMaximum f T) (-runningMinimum f T) := by
  apply le_antisymm
  · apply (windowSup_le_iff f T _).mpr
    intro s hs
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · have h := runningMinimum_le (continuous_path f) hs
      have hm := le_max_right (runningMaximum f T) (-runningMinimum f T)
      linarith
    · exact (le_runningMaximum f hs).trans (le_max_left _ _)
  · apply max_le
    · obtain ⟨s,hs,he⟩ := runningMaximum_attained f T
      rw [he]
      exact (le_abs_self (f s)).trans (norm_le_windowSup f hs.2)
    · obtain ⟨s,hs,he⟩ := runningMinimum_attained (continuous_path f) T
      rw [he]
      exact (neg_le_abs (f s)).trans (norm_le_windowSup f hs.2)

theorem continuous_windowSup (T : ℝ≥0) : Continuous (fun f : Path ↦ windowSup f T) :=
  (continuous_runningMaximum T).comp continuous_absolutePath

theorem continuous_joint_windowSup :
    Continuous (fun p : Path × ℝ≥0 ↦ windowSup p.1 p.2) :=
  continuous_joint_runningMaximum.comp
    ((continuous_absolutePath.comp continuous_fst).prodMk continuous_snd)

theorem windowSup_tail_event_eq_exists (a : ℝ) (T : ℝ≥0) :
    {f : Path | a ≤ windowSup f T} = {f : Path | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ ‖f s‖} := by
  ext f
  change a ≤ windowSup f T ↔ ∃ s : ℝ≥0, s ≤ T ∧ a ≤ ‖f s‖
  constructor
  · intro h
    obtain ⟨s,hs,he⟩ := windowSup_attained f T
    exact ⟨s,hs.2,he ▸ h⟩
  · rintro ⟨s,hs,h⟩
    exact h.trans (norm_le_windowSup f hs)

theorem gaussian_reflected_upper_tail (level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    gaussianReal (2*level) T (Ioi level) = gaussianReal 0 T (Iic level) := by
  have hm : Measurable (fun x : ℝ ↦ 2*level-x) := by fun_prop
  have he : (fun x : ℝ ↦ 2*level-x) ⁻¹' Ioi level = Iio level := by
    ext x
    simp only [mem_preimage,mem_Ioi,mem_Iio]
    constructor <;> intro h <;> linarith
  have hzero : gaussianReal 0 T {level} = 0 :=
    (gaussianReal_absolutelyContinuous 0 hT.ne') (measure_singleton level)
  rw [← sub_zero (2*level),← gaussianReal_map_const_sub,
    Measure.map_apply hm measurableSet_Ioi,he]
  exact measure_congr (Iio_ae_eq_Iic' hzero)

/-- Exact reflection-principle tail under the constructed whole path law. -/
theorem runningMinimum_tail (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | runningMinimum f T ≤ level} =
      2 * gaussianReal 0 T (Iic level) := by
  let H : Set Path := {f | firstPassage level f ≤ T ∧ f T ∈ Ioi level}
  let E : Set Path := {f | f T ∈ Iic level}
  have hE : MeasurableSet E := (continuous_eval T).measurable measurableSet_Iic
  have hd : Disjoint H E := by
    apply disjoint_left.mpr
    intro f hh he
    change firstPassage level f ≤ T ∧ level < f T at hh
    change f T ≤ level at he
    exact (not_le_of_gt hh.2) he
  have hu : H ∪ E = {f : Path | runningMinimum f T ≤ level} := by
    ext f
    change (f ∈ H ∨ f ∈ E) ↔ runningMinimum f T ≤ level
    rw [← firstPassage_le_iff_minimum level f T]
    constructor
    · rintro (hh | he)
      · exact hh.1
      · exact (firstPassage_le_iff level f T).mpr ⟨T,le_rfl,he⟩
    · intro hh
      rcases lt_or_ge level (f T) with he | he
      · exact Or.inl ⟨hh,he⟩
      · exact Or.inr he
  have hHit : pathLaw H = gaussianReal (2*level) T (Ioi level) :=
    hit_endpoint_probability level hlevel T measurableSet_Ioi (Subset.rfl)
  have hEnd : pathLaw E = gaussianReal 0 T (Iic level) := by
    change pathLaw ((fun f : Path ↦ f T) ⁻¹' Iic level) = _
    rw [← Measure.map_apply (continuous_eval T).measurable measurableSet_Iic,
      (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq]
  rw [← hu,measure_union hd hE,hHit,hEnd,gaussian_reflected_upper_tail level T hT,← two_mul]

theorem runningMaximum_tail (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ runningMaximum f T} = 2 * gaussianReal 0 T (Iic (-a)) := by
  have he : {f : Path | a ≤ runningMaximum f T} =
      negPath ⁻¹' {f : Path | runningMinimum f T ≤ -a} := by
    ext f
    change a ≤ -runningMinimum (negPath f) T ↔ runningMinimum (negPath f) T ≤ -a
    constructor <;> intro h <;> linarith
  have hA : MeasurableSet {f : Path | runningMinimum f T ≤ -a} :=
    (isClosed_le (continuous_minimum_at T) continuous_const).measurableSet
  rw [he,← Measure.map_apply measurable_negPath hA,negPath_law]
  exact runningMinimum_tail (-a) (neg_neg_of_pos ha) T hT

theorem windowSup_gaussian_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ windowSup f T} ≤ 4 * gaussianReal 0 T (Iic (-a)) := by
  have he : {f : Path | a ≤ windowSup f T} =
      {f : Path | a ≤ runningMaximum f T} ∪ {f : Path | runningMinimum f T ≤ -a} := by
    ext f
    rw [mem_ofPred_eq,windowSup_eq_max,le_max_iff]
    simp only [mem_union,mem_ofPred_eq]
    constructor <;> rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [he]
  calc
    _ ≤ pathLaw {f : Path | a ≤ runningMaximum f T} +
        pathLaw {f : Path | runningMinimum f T ≤ -a} := measure_union_le _ _
    _ = 4 * gaussianReal 0 T (Iic (-a)) := by
      rw [runningMaximum_tail a ha T hT,runningMinimum_tail (-a) (neg_neg_of_pos ha) T hT]
      ring

theorem gaussian_endpoint_lower_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    gaussianReal 0 T (Iic (-a)) ≤ ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) := by
  have hTr : 0 < (T : ℝ) := hT
  have ht : -a/(T : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) T.coe_nonneg
  have hb := measure_le_le_exp_mul_mgf (X := fun f : Path ↦ f T) (μ := pathLaw) (-a) ht
    (integrable_exp_mul_endpoint T (-a/(T : ℝ)))
  have he : -( -a/(T : ℝ))*(-a) + (T : ℝ)*(-a/(T : ℝ))^2/2 = -a^2/(2*(T : ℝ)) := by
    field_simp
    ring
  have hEnd : pathLaw {f : Path | f T ≤ -a} = gaussianReal 0 T (Iic (-a)) := by
    change pathLaw ((fun f : Path ↦ f T) ⁻¹' Iic (-a)) = _
    rw [← Measure.map_apply (continuous_eval T).measurable measurableSet_Iic,
      (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq]
  rw [mgf,integral_exp_mul_endpoint,← Real.exp_add,he] at hb
  change (pathLaw {f : Path | f T ≤ -a}).toReal ≤ _ at hb
  rw [hEnd] at hb
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr hb

theorem runningMinimum_exponential_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | runningMinimum f T ≤ -a} ≤
      2 * ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) := by
  rw [runningMinimum_tail (-a) (neg_neg_of_pos ha) T hT]
  exact mul_le_mul' le_rfl (gaussian_endpoint_lower_tail_bound a ha T hT)

theorem runningMaximum_exponential_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ runningMaximum f T} ≤
      2 * ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) := by
  rw [runningMaximum_tail a ha T hT]
  exact mul_le_mul' le_rfl (gaussian_endpoint_lower_tail_bound a ha T hT)

theorem windowSup_exponential_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ windowSup f T} ≤
      4 * ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) :=
  (windowSup_gaussian_tail_bound a ha T hT).trans
    (mul_le_mul' le_rfl (gaussian_endpoint_lower_tail_bound a ha T hT))

theorem literal_path_norm_tail_bound (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ ‖f s‖} ≤
      4 * ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) := by
  rw [← windowSup_tail_event_eq_exists]
  exact windowSup_exponential_tail_bound a ha T hT

/-- The same proved bound applies to the actual whole forward-increment
path at any fixed starting time, not just to the initial interval. -/
theorem forward_increment_sup_tail_bound (S : ℝ≥0) (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ windowSup (futurePath S f) T} ≤
      4 * ENNReal.ofReal (Real.exp (-a^2/(2*(T : ℝ)))) := by
  have hA : MeasurableSet {f : Path | a ≤ windowSup f T} :=
    (isClosed_le continuous_const (continuous_windowSup T)).measurableSet
  change pathLaw ((futurePath S) ⁻¹' {f : Path | a ≤ windowSup f T}) ≤ _
  rw [← Measure.map_apply (measurable_futurePath S) hA,futurePath_law]
  exact windowSup_exponential_tail_bound a ha T hT

end PerronWright.BrownianPathExtremaTails
