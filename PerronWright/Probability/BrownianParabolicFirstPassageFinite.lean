import PerronWright.Probability.BrownianParabolicFirstPassagePastFibers
import PerronWright.Probability.BrownianFirstPassageNegativeDrift

/-! # Literal parabolic Brownian first passages are almost surely finite

The actual proved subquadratic growth forces every parabolic driver to
minus infinity. Finiteness and exact hitting are derived for the source
path probability law, not assumptions of a future-factorization theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageFinite

open BrownianPathLaw BrownianGaussianSkeleton BrownianContinuousModification
open BrownianParabolicFirstPassagePastFibers ContinuousPathFirstPassage

theorem ae_all_parameter_source_finite :
    ∀ᵐ x ∂rationalLaw, ∀ lambda level : ℝ,
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda (measurablePath x)) ≠ ⊤ := by
  filter_upwards [BrownianFullHorizonDrift.ae_all_parameter_drift_tendsto_atBot,
    ae_all_measurablePath_eval] with x hx hmatch
  intro lambda level
  apply BrownianFirstPassageNegativeDrift.firstPassage_ne_top_of_tendsto_atBot
  have he : (fun t : ℝ≥0 ↦ BrownianPathReflectionLaw.driftPath lambda (measurablePath x) t) =
      fun t ↦ BrownianParabolicReflection.drift lambda t x := by
    funext t
    simp only [BrownianPathReflectionLaw.driftPath_apply,BrownianParabolicReflection.drift_formula,
      hmatch]
  rw [he]
  exact hx lambda

theorem ae_parabolicFirstPassage_ne_top (lambda level : ℝ) :
    ∀ᵐ f : Path ∂pathLaw,
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≠ ⊤ := by
  have hm : Measurable (fun f : Path ↦ firstPassage level (BrownianPathReflectionLaw.driftPath lambda f)) :=
    (measurable_firstPassage level).comp (measurable_actual_driftPath lambda)
  have hs : MeasurableSet {f : Path |
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ≠ ⊤} :=
    (hm (measurableSet_singleton ⊤)).compl
  rw [pathLaw]
  exact (ae_map_iff measurable_measurablePath.aemeasurable hs).mpr
    (ae_all_parameter_source_finite.mono (fun _ hx ↦ hx lambda level))

theorem ae_parabolicFirstPassage_lt_top (lambda level : ℝ) :
    ∀ᵐ f : Path ∂pathLaw,
      firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) < ⊤ :=
  (ae_parabolicFirstPassage_ne_top lambda level).mono (fun _ hf ↦ lt_top_iff_ne_top.mpr hf)

theorem ae_parabolicFirstPassage_pos (lambda level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw,
      0 < firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  by_contra h
  have hm := (firstPassage_le_iff level (BrownianPathReflectionLaw.driftPath lambda f) 0).mp
    (le_of_not_gt h)
  obtain ⟨t,ht,he⟩ := hm
  have ht0 : t = 0 := le_antisymm ht zero_le
  subst t
  have hh : (0 : ℝ) ≤ level := by
    simpa only [BrownianPathReflectionLaw.driftPath_apply,NNReal.coe_zero,mul_zero,add_zero,
      zero_pow (by norm_num : 2 ≠ 0),zero_div,sub_zero,hf] using he
  exact (not_le_of_gt hlevel) hh

theorem ae_parabolicFirstPassage_exact_level (lambda level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw,
      BrownianPathReflectionLaw.driftPath lambda f
        (firstPassage level (BrownianPathReflectionLaw.driftPath lambda f)).toNNReal = level := by
  filter_upwards [ae_parabolicFirstPassage_ne_top lambda level,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin hf
  apply firstPassage_exact_level level _ _ hfin
  simpa only [BrownianPathReflectionLaw.driftPath_apply,NNReal.coe_zero,mul_zero,add_zero,
    zero_pow (by norm_num : 2 ≠ 0),zero_div,sub_zero,hf] using hlevel

end PerronWright.BrownianParabolicFirstPassageFinite
