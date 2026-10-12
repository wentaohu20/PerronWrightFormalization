import PerronWright.Probability.BrownianContinuousLinearTests
import Mathlib.Probability.BrownianMotion.Basic

/-!
# An actual continuous real Brownian realization

Finite-dimensional laws of the constructed process are identified with
the literal finite Brownian Gaussian measures by their characteristic
functions. Combined with proved sample continuity this constructs an
`IsBrownianReal` witness, rather than using one as an interface hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianContinuousGaussianLaw

open BrownianGaussianSkeleton BrownianContinuousModification BrownianContinuousLinearTests
open ProbabilityTheory.BrownianReal

theorem linearFunctional_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  calc
    _ = L (∑ i, x i • Pi.single i 1) := congrArg L (pi_eq_sum_univ' x)
    _ = ∑ i, x i * L (Pi.single i 1) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)

theorem projectiveFamily_charFunDual (I : Finset ℝ≥0) (L : StrongDual ℝ (I → ℝ)) :
    charFunDual (projectiveFamily I) L =
      Complex.exp (-((realQuadraticVariance (fun i : I ↦ i.val) (fun i ↦ L (Pi.single i 1)) : ℝ) : ℂ) / 2) := by
  let c : I → ℝ := fun i ↦ L (Pi.single i 1)
  have hL : (fun x : I → ℝ ↦ L x) = (fun x ↦ ∑ i, c i * x i) :=
    funext (linearFunctional_pi L)
  have hm : (∫ x, L x ∂projectiveFamily I) = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm,integral_id_projectiveFamily,map_zero]
    exact IsGaussian.integrable_id
  have hmem (i : I) : MemLp (fun x : I → ℝ ↦ c i * x i) 2 (projectiveFamily I) :=
    (measurePreserving_eval_projectiveFamily i).hasLaw.hasGaussianLaw.memLp_two.const_mul (c i)
  have hv : Var[fun x : I → ℝ ↦ L x;projectiveFamily I] =
      realQuadraticVariance (fun i : I ↦ i.val) c := by
    rw [hL,variance_fun_sum hmem]
    simp only [covariance_const_mul_left,covariance_const_mul_right,covariance_eval_projectiveFamily,
      NNReal.coe_min,realQuadraticVariance]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc,mul_comm (c j) (c i)]
    exact congrArg (fun z : ℝ ↦ c i * c j * z) (NNReal.coe_min i.val j.val)
  have hh := (IsGaussian.hasGaussianLaw_id (μ := projectiveFamily I)).charFunDual_map_eq_fun L
  simp only [Measure.map_id,id_eq,hm,hv,Complex.ofReal_zero,zero_mul,zero_sub] at hh
  simpa only [c,neg_div] using hh

/-- Exact finite-dimensional Brownian Gaussian law of the actual
constructed continuous process at every finite set of real times. -/
theorem process_hasLaw_finite (I : Finset ℝ≥0) :
    HasLaw (fun x ↦ I.restrict (process · x)) (projectiveFamily I) rationalLaw := by
  have hm : AEMeasurable (fun x ↦ I.restrict (process · x)) rationalLaw :=
    aemeasurable_pi_lambda _ (fun i ↦ aemeasurable_process i.val)
  refine ⟨hm,?_⟩
  let : IsProbabilityMeasure (rationalLaw.map (fun x ↦ I.restrict (process · x))) :=
    Measure.isProbabilityMeasure_map hm
  apply Measure.ext_of_charFunDual
  funext L
  have hfun : (fun x ↦ Complex.exp ((L (I.restrict (process · x)) : ℂ) * Complex.I)) =
      (fun x ↦ Complex.exp ((realLinearTest (fun i : I ↦ i.val) (fun i ↦ L (Pi.single i 1)) x : ℂ) * Complex.I)) := by
    funext x
    rw [linearFunctional_pi]
    rfl
  calc
    _ = ∫ x, Complex.exp ((L (I.restrict (process · x)) : ℂ) * Complex.I) ∂rationalLaw := by
      rw [charFunDual_apply,integral_map hm (by fun_prop)]
    _ = Complex.exp (-((realQuadraticVariance (fun i : I ↦ i.val)
        (fun i ↦ L (Pi.single i 1)) : ℝ) : ℂ) / 2) := by
      rw [hfun]
      exact integral_exp_realLinearTest (fun i : I ↦ i.val) (fun i ↦ L (Pi.single i 1))
    _ = _ := (projectiveFamily_charFunDual I L).symm

theorem isPreBrownian_process : IsPreBrownianReal process rationalLaw :=
  ⟨process_hasLaw_finite⟩

/-- A genuinely constructed continuous real Brownian process on the
explicit countable Gaussian probability space. No realization hypothesis. -/
theorem isBrownian_process : IsBrownianReal process rationalLaw :=
  ⟨isPreBrownian_process,ae_continuous_process⟩

theorem process_hasLaw_eval (t : ℝ≥0) :
    HasLaw (process t) (gaussianReal 0 t) rationalLaw :=
  isPreBrownian_process.hasLaw_eval t

theorem process_hasLaw_sub (s t : ℝ≥0) :
    HasLaw (fun x ↦ process s x - process t x)
      (gaussianReal 0 (nndist s.val t.val)) rationalLaw :=
  isPreBrownian_process.hasLaw_sub s t

theorem process_integral_eval (t : ℝ≥0) : (∫ x, process t x ∂rationalLaw) = 0 :=
  isPreBrownian_process.integral_eval t

theorem process_covariance_eval (s t : ℝ≥0) :
    cov[process s,process t;rationalLaw] = min s.val t.val := by
  convert isPreBrownian_process.covariance_eval s t using 1
  exact (NNReal.coe_min s t).symm

theorem process_hasIndepIncrements : HasIndepIncrements process rationalLaw :=
  isPreBrownian_process.hasIndepIncrements

theorem exists_real_brownian :
    ∃ P : Measure (ℕ → ℝ), IsProbabilityMeasure P ∧
      ∃ B : ℝ≥0 → (ℕ → ℝ) → ℝ, IsBrownianReal B P :=
  ⟨rationalLaw,inferInstance,process,isBrownian_process⟩

end PerronWright.BrownianContinuousGaussianLaw
