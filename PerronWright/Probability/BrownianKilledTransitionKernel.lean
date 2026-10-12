import PerronWright.Probability.BrownianFirstPassageReflection
import PerronWright.Probability.BrownianFirstPassageBridgeLaw

/-! # Actual first-passage killed endpoint law

Reflection at the literal bounded first passage preserves the actual
Brownian path law. Its endpoint exchanges hit paths ending above the
negative level with Gaussian endpoints reflected below that level.
This proves the genuine killed Gaussian endpoint measure identity.
Neither a first-passage kernel nor an excursion/Palm identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledTransitionKernel

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageReflection

def killedEndpointLaw (level : ℝ) (T : ℝ≥0) : Measure ℝ :=
  (pathLaw.restrict (survival level T)).map (fun f : Path ↦ f T)

instance killedEndpointLaw_isFinite (level : ℝ) (T : ℝ≥0) :
    IsFiniteMeasure (killedEndpointLaw level T) := by
  unfold killedEndpointLaw
  infer_instance

theorem killedEndpointLaw_apply (level : ℝ) (T : ℝ≥0) {B : Set ℝ} (hB : MeasurableSet B) :
    killedEndpointLaw level T B =
      pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} := by
  rw [killedEndpointLaw,Measure.map_apply (continuous_eval T).measurable hB,
    Measure.restrict_apply ((continuous_eval T).measurable hB)]
  congr 1
  ext f
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,mem_survival_iff_firstPassage]
  exact and_comm

theorem boundedReflection_endpoint_of_survival (level : ℝ) (T : ℝ≥0) (f : Path)
    (hs : (T : ℝ≥0∞) < firstPassage level f) : boundedReflection level T f T = f T := by
  have hc : cappedTime level T f = T := by
    unfold cappedTime
    rw [min_eq_right hs.le,ENNReal.toNNReal_coe]
  change 2*f (min T (cappedTime level T f))-f T = f T
  rw [hc,min_self]
  ring

theorem boundedReflection_endpoint_of_hit (level : ℝ) (T : ℝ≥0) (f : Path)
    (hstart : level < f 0) (hh : firstPassage level f ≤ T) :
    boundedReflection level T f T = 2*level-f T := by
  have hfin : firstPassage level f ≠ ⊤ := by
    intro he
    rw [he] at hh
    exact ENNReal.coe_ne_top (le_antisymm le_top hh)
  have hc : cappedTime level T f = (firstPassage level f).toNNReal := by
    unfold cappedTime
    rw [min_eq_left hh]
  change 2*f (min T (cappedTime level T f))-f T = _
  rw [min_eq_right (cappedTime_le level T f),hc,firstPassage_exact_level level f hstart hfin]

theorem mirror_reflected_endpoint_law (level : ℝ) (T : ℝ≥0) :
    pathLaw.map (fun f : Path ↦ 2*level-boundedReflection level T f T) =
      gaussianReal (2*level) T := by
  have hR : HasLaw (boundedReflection level T) pathLaw pathLaw :=
    ⟨(measurable_boundedReflection level T).aemeasurable,boundedReflection_law level T⟩
  have h := gaussianReal_const_sub
    ((isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).comp hR) (2*level)
  simpa only [Function.comp_def,sub_zero] using h.map_eq

/-- Exact actual hit/endpoint identity in every Borel set above the
negative level; all random-time reflection properties are proved. -/
theorem hit_endpoint_probability (level : ℝ) (hlevel : level < 0) (T : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) (hhigh : B ⊆ Ioi level) :
    pathLaw {f : Path | firstPassage level f ≤ T ∧ f T ∈ B} = gaussianReal (2*level) T B := by
  have hm : Measurable (fun f : Path ↦ 2*level-boundedReflection level T f T) :=
    measurable_const.sub ((continuous_eval T).measurable.comp (measurable_boundedReflection level T))
  have he : {f : Path | firstPassage level f ≤ T ∧ f T ∈ B} =ᵐ[pathLaw]
      (fun f : Path ↦ 2*level-boundedReflection level T f T) ⁻¹' B := by
    filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
    have hstart : level < f 0 := hf ▸ hlevel
    apply propext
    change (firstPassage level f ≤ T ∧ f T ∈ B) ↔ 2*level-boundedReflection level T f T ∈ B
    by_cases hh : firstPassage level f ≤ T
    · have hv : 2*level-boundedReflection level T f T = f T := by
        rw [boundedReflection_endpoint_of_hit level T f hstart hh]
        ring
      simp only [hh,true_and,hv]
    · have hs := lt_of_not_ge hh
      have hv := boundedReflection_endpoint_of_survival level T f hs
      have hb : 2*level-f T ∉ B := by
        intro hb
        have hp := hhigh hb
        have hq := before_firstPassage level f T hs
        change level < 2*level-f T at hp
        linarith
      simp only [hh,false_and,hv,hb]
  rw [measure_congr he,← Measure.map_apply hm hB,mirror_reflected_endpoint_law]

/-- The genuine killed Gaussian kernel, expressed as an exact finite
measure difference identity without any assumed density. -/
theorem killedEndpointLaw_add_reflected (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) :
    killedEndpointLaw level T+(gaussianReal (2*level) T).restrict (Ioi level) =
      (gaussianReal 0 T).restrict (Ioi level) := by
  ext B hB
  let A := B ∩ Ioi level
  have hA : MeasurableSet A := hB.inter measurableSet_Ioi
  let S : Set Path := {f | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B}
  let H : Set Path := {f | firstPassage level f ≤ T ∧ f T ∈ A}
  let E : Set Path := {f | f T ∈ A}
  have hH : MeasurableSet H :=
    (measurableSet_le (measurable_firstPassage level) measurable_const).inter
      ((continuous_eval T).measurable hA)
  have hd : Disjoint S H :=
    disjoint_left.mpr (fun f hs hh ↦ (not_le_of_gt hs.1) hh.1)
  have hu : S ∪ H = E := by
    ext f
    constructor
    · rintro (hs | hh)
      · exact ⟨hs.2,before_firstPassage level f T hs.1⟩
      · exact hh.2
    · intro he
      rcases le_or_gt (firstPassage level f) (T : ℝ≥0∞) with hh | hs
      · exact Or.inr ⟨hh,he⟩
      · exact Or.inl ⟨hs,he.1⟩
  have hp : pathLaw E = pathLaw S+pathLaw H := by
    rw [← hu]
    exact measure_union hd hH
  have hHit : pathLaw H = gaussianReal (2*level) T A :=
    hit_endpoint_probability level hlevel T hA (fun _ h ↦ h.2)
  have hEnd : pathLaw E = gaussianReal 0 T A := by
    change pathLaw ((fun f : Path ↦ f T) ⁻¹' A) = _
    rw [← Measure.map_apply (continuous_eval T).measurable hA,
      (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq]
  rw [Measure.add_apply,killedEndpointLaw_apply level T hB,Measure.restrict_apply hB,
    Measure.restrict_apply hB]
  change pathLaw S+gaussianReal (2*level) T A = gaussianReal 0 T A
  rw [← hHit,← hEnd]
  exact hp.symm

end PerronWright.BrownianKilledTransitionKernel
