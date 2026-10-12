import PerronWright.Probability.BrownianKilledAreaMomentRecursion
import PerronWright.Probability.BrownianPinnedBridgeArea
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Actual finite killed Brownian area moments

The literal Brownian area splits into the signed pinned-bridge area and
one half of duration times the actual endpoint. Both have genuine Gaussian
laws. This proves all absolute moments without any path-maximum premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentFiniteness

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeArea
open BrownianBridgeCyclicArea BrownianKilledAreaGeometry
open BrownianKilledAreaMomentKernel ContinuousPathFirstPassage

theorem pathArea_eq_bridgeArea_add_endpoint (T : ℝ≥0) (f : Path) :
    pathArea T f = area T f + ((T : ℝ)/2)*f T := by
  by_cases hT : T = 0
  · subst T
    simp [pathArea,area]
  have hne : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  have hc : Continuous (fun s : ℝ ↦ f (Real.toNNReal s)) :=
    (continuous_path f).comp continuous_real_toNNReal
  have he : area T f = ∫ s in (0 : ℝ)..(T : ℝ),
      f (Real.toNNReal s) - s/(T : ℝ)*f T := by
    unfold area
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le T.coe_nonneg] using hs :
      s ∈ Icc (0 : ℝ) (T : ℝ)).1
    simp only [bridge,Real.coe_toNNReal _ hs0]
  have hl : Continuous (fun s : ℝ ↦ s/(T : ℝ)*f T) :=
    (continuous_id.div_const (T : ℝ)).mul continuous_const
  rw [he,intervalIntegral.integral_sub (hc.intervalIntegrable 0 T)
    (hl.intervalIntegrable 0 T),
    intervalIntegral.integral_mul_const,intervalIntegral.integral_div,integral_id]
  change pathArea T f = pathArea T f - ((T : ℝ)^2-0^2)/2/(T : ℝ)*f T + _
  field_simp [hne]
  ring

theorem memLp_pathArea (T : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (pathArea T) p pathLaw := by
  by_cases hT : T = 0
  · subst T
    have he : pathArea 0 = fun _ : Path ↦ (0 : ℝ) := by
      funext f
      simp [pathArea]
    rw [he]
    exact memLp_const 0
  have hpos : 0 < T := bot_lt_iff_ne_bot.mpr hT
  have hA := (area_hasGaussianLaw T hpos).memLp hp
  have hE := (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval T).memLp hp
  have h := hA.add (hE.const_mul ((T : ℝ)/2))
  convert h using 1
  funext f
  exact pathArea_eq_bridgeArea_add_endpoint T f

theorem memLp_shiftedArea (level x : ℝ) (T : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (shiftedArea level x T) p pathLaw :=
  (memLp_const ((T : ℝ)*(x-level))).add (memLp_pathArea T p hp)

theorem integrable_abs_shiftedArea_pow (level x : ℝ) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun f : Path ↦ |shiftedArea level x T f| ^ n) pathLaw := by
  simpa only [Real.norm_eq_abs] using
    (memLp_shiftedArea level x T (n : ℝ≥0∞) (by simp)).integrable_norm_pow' (p := n)

theorem momentWeight_ne_top (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) (f : Path) :
    momentWeight level n T x f ≠ ∞ := by
  by_cases hf : f ∈ survival (level-x) T
  · simp only [momentWeight,indicator_of_mem hf]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · simp [momentWeight,hf]

theorem momentWeight_toReal_le_abs_pow (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ)
    (f : Path) : (momentWeight level n T x f).toReal ≤ |shiftedArea level x T f|^n := by
  by_cases hf : f ∈ survival (level-x) T
  · rw [momentWeight,indicator_of_mem hf,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (shiftedArea_nonneg_of_survival level x T f hf),
      abs_of_nonneg (shiftedArea_nonneg_of_survival level x T f hf)]
  · simp only [momentWeight,indicator_of_notMem hf,ENNReal.toReal_zero]
    positivity

theorem integrable_momentWeight_toReal (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    Integrable (fun f : Path ↦ (momentWeight level n T x f).toReal) pathLaw := by
  apply (integrable_abs_shiftedArea_pow level x T n).mono'
    (measurable_momentWeight level n T x).ennreal_toReal.aestronglyMeasurable
  exact Eventually.of_forall (fun f ↦ by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact momentWeight_toReal_le_abs_pow level n T x f)

theorem lintegral_momentWeight_ne_top (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    (∫⁻ f, momentWeight level n T x f ∂pathLaw) ≠ ∞ :=
  (integrable_toReal_iff (measurable_momentWeight level n T x).aemeasurable
    (Eventually.of_forall (momentWeight_ne_top level n T x))).mp
    (integrable_momentWeight_toReal level n T x)

instance momentLaw_isFiniteMeasure (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    IsFiniteMeasure (momentLaw level n T x) := by
  let := isFiniteMeasure_withDensity (lintegral_momentWeight_ne_top level n T x)
  unfold momentLaw
  infer_instance

theorem momentLaw_univ_le_absoluteMoment (level : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    (momentLaw level n T x).real univ ≤
      ∫ f : Path, |shiftedArea level x T f|^n ∂pathLaw := by
  have he : momentLaw level n T x univ = ∫⁻ f, momentWeight level n T x f ∂pathLaw := by
    simpa using momentLaw_lintegral level n T x (measurable_const : Measurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)))
  rw [Measure.real,he,← integral_toReal (measurable_momentWeight level n T x).aemeasurable
    (Eventually.of_forall (fun f ↦ (momentWeight_ne_top level n T x f).lt_top))]
  exact integral_mono (integrable_momentWeight_toReal level n T x)
    (integrable_abs_shiftedArea_pow level x T n) (momentWeight_toReal_le_abs_pow level n T x)

end PerronWright.BrownianKilledAreaMomentFiniteness
