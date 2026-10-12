import PerronWright.Probability.BrownianFirstPassageExponential
import PerronWright.Probability.BrownianFirstPassageStrongMarkovFull

/-! # Literal negative Brownian first-passage Laplace transform

The actual bounded exponential normalization passes to the true finite
passage using a constant integrable bound. The constructed zero-drift
Brownian law discharges finiteness and exact hitting. No optional
stopping or transform identity occurs as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageLaplace

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageReflection
open BrownianFirstPassageExponential BrownianFirstPassageZeroDrift
open BrownianFirstPassageUncappedLaw

theorem measurable_passage_exponential (level u : ℝ) :
    Measurable (fun f : Path ↦ exponential u (passageTime level f) level) :=
  (continuous_exponential u).measurable.comp
    ((measurable_passageTime level).prodMk measurable_const)

theorem integrable_passage_exponential (level u : ℝ) :
    Integrable (fun f : Path ↦ exponential u (passageTime level f) level) pathLaw := by
  apply Integrable.mono' (integrable_const (Real.exp (u*level)))
    (measurable_passage_exponential level u).aestronglyMeasurable
  apply Eventually.of_forall
  intro f
  rw [Real.norm_eq_abs,abs_of_pos (show 0 < exponential u (passageTime level f) level
    from Real.exp_pos _)]
  unfold exponential
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ (passageTime level f : ℝ)*u^2/2 := by positivity
  linarith

theorem integral_passage_exponential (level : ℝ) (hlevel : level < 0)
    (u : ℝ) (hu : u ≤ 0) :
    (∫ f : Path, exponential u (passageTime level f) level ∂pathLaw) = 1 := by
  have hd : Tendsto
      (fun n : ℕ ↦ ∫ f : Path,
        exponential u (cappedTime level (n : ℝ≥0) f) (f (cappedTime level (n : ℝ≥0) f))
          ∂pathLaw) atTop
      (𝓝 (∫ f : Path, exponential u (passageTime level f) level ∂pathLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ Real.exp (u*level))
    · intro n
      exact (measurable_capped_exponential level (n : ℝ≥0) u).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
      rw [Real.norm_eq_abs,abs_of_pos (show 0 < exponential u (cappedTime level (n : ℝ≥0) f)
        (f (cappedTime level (n : ℝ≥0) f)) from Real.exp_pos _)]
      exact capped_exponential_le level (n : ℝ≥0) u hu f (by simpa only [hf] using hlevel)
    · filter_upwards [ae_firstPassage_ne_top level hlevel,
        ae_firstPassage_exact_level level hlevel] with f hfin hhit
      apply tendsto_const_nhds.congr'
      filter_upwards [cappedTime_eventually_eq level f hfin] with n hn
      rw [hn]
      change exponential u (passageTime level f) level =
        exponential u (passageTime level f) (f (firstPassage level f).toNNReal)
      rw [hhit]
  have hconst : Tendsto
      (fun n : ℕ ↦ ∫ f : Path,
        exponential u (cappedTime level (n : ℝ≥0) f) (f (cappedTime level (n : ℝ≥0) f))
          ∂pathLaw) atTop (𝓝 (1 : ℝ)) := by
    simp only [integral_capped_exponential level hlevel _ u hu]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hd hconst)

def passageLaplace (level p : ℝ) : ℝ :=
  ∫ f : Path, Real.exp (-p*(passageTime level f : ℝ)) ∂pathLaw

theorem integrable_passage_laplace (level : ℝ) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun f : Path ↦ Real.exp (-p*(passageTime level f : ℝ))) pathLaw := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_passageTime level).coe_nnreal_real.const_mul (-p)).exp.aestronglyMeasurable)
  apply Eventually.of_forall
  intro f
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp)
    (passageTime level f).coe_nonneg)

theorem passageLaplace_eq (level : ℝ) (hlevel : level < 0)
    (p : ℝ) (hp : 0 ≤ p) :
    passageLaplace level p = Real.exp (level*Real.sqrt (2*p)) := by
  let u : ℝ := -Real.sqrt (2*p)
  have hu : u ≤ 0 := neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hu2 : u^2/2 = p := by
    dsimp only [u]
    rw [neg_sq,Real.sq_sqrt (by positivity : 0 ≤ 2*p)]
    ring
  have he := integral_passage_exponential level hlevel u hu
  have hrewrite (f : Path) : exponential u (passageTime level f) level =
      Real.exp (u*level)*Real.exp (-p*(passageTime level f : ℝ)) := by
    unfold exponential
    rw [← Real.exp_add]
    congr 1
    nlinarith
  simp only [hrewrite,integral_const_mul] at he
  change Real.exp (u*level)*passageLaplace level p = 1 at he
  have hresult : passageLaplace level p = (Real.exp (u*level))⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff (Real.exp_ne_zero _)).mpr (by simpa only [mul_comm] using he)
  rw [hresult,← Real.exp_neg]
  congr 1
  dsimp only [u]
  ring

theorem negative_passageLaplace_eq (a : ℝ) (ha : 0 < a) (p : ℝ) (hp : 0 ≤ p) :
    passageLaplace (-a) p = Real.exp (-a*Real.sqrt (2*p)) :=
  passageLaplace_eq (-a) (by linarith) p hp

theorem lintegral_negative_passageLaplace (a : ℝ) (ha : 0 < a) (p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ f : Path, ENNReal.ofReal (Real.exp (-p*(passageTime (-a) f : ℝ))) ∂pathLaw) =
      ENNReal.ofReal (Real.exp (-a*Real.sqrt (2*p))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_passage_laplace (-a) p hp)
      (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
  exact congrArg ENNReal.ofReal (negative_passageLaplace_eq a ha p hp)

end PerronWright.BrownianFirstPassageLaplace
