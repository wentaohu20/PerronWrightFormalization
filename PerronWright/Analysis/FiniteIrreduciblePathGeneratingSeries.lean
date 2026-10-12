import PerronWright.Analysis.FiniteIrreducibleMarkedPathResolvent
import PerronWright.Analysis.FiniteIrreducibleOuterNeumann
import PerronWright.Enumeration.ComplexProfilePathCoefficient

/-!
# Literal finite irreducible path series and the actual resolvent

The finite positive Perron gauge supplies norm convergence for the actual
paper-oriented path operator. Its kernel coefficients are precisely the
previously defined finite-dimensional path integrals. No primitivity or
second-power positivity is used, so bipartite matrices remain admissible.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section
namespace PerronWright.FiniteIrreduciblePathGeneratingSeries

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (profile pathOperatorParameterCLM operatorKernelize operatorKernelize_apply
   pathResolventKernel)
end MPR

namespace TON
export PerronWright.FiniteIrreducibleOuterNeumann
  (weightedComplexAction weightedComplexAction_pow_norm_le)
end TON

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev PathEnd (S : Type*) [MetricSpace S] [CompactSpace S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

local instance pathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance pathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance pathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance pathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance pathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance pathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

omit [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem pathProfileMultiplier_norm_le (tau : C(S, ℂ)) :
    ‖GraphCore.pathProfileMultiplier tau‖ ≤ ‖tau‖ := by
  calc
    ‖GraphCore.pathProfileMultiplier tau‖ ≤ ‖tau‖ * ‖(1 : C(S, ℂ))‖ :=
      ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ C(S, ℂ) tau 1
    _ ≤ ‖tau‖ * 1 := by
      gcongr
      apply (ContinuousMap.norm_le (1 : C(S, ℂ)) zero_le_one).2
      intro x
      norm_num
    _ = ‖tau‖ := by rw [mul_one]

private theorem pathOperatorParameter_eq_kernel_mul_multiplier
    (M : FiniteIrreducibleModel S) (tau : C(S, ℂ)) :
    MPR.pathOperatorParameterCLM M tau =
      M.bjrModel.kernel.complexActionCLM M.bjrModel.mu * GraphCore.pathProfileMultiplier tau := by
  rfl

private theorem weightedComplexAction_eq_multiplier_mul_kernel
    (M : FiniteIrreducibleModel S) (tau : C(S, ℂ)) :
    TON.weightedComplexAction M tau =
      GraphCore.pathProfileMultiplier tau * M.bjrModel.kernel.complexActionCLM M.bjrModel.mu := by
  rfl

private theorem pathOperator_pow_succ_factorization
    (M : FiniteIrreducibleModel S) (tau : C(S, ℂ)) (n : ℕ) :
    (MPR.pathOperatorParameterCLM M tau) ^ (n + 1) =
      M.bjrModel.kernel.complexActionCLM M.bjrModel.mu *
        (TON.weightedComplexAction M tau) ^ n *
          GraphCore.pathProfileMultiplier tau := by
  rw [pathOperatorParameter_eq_kernel_mul_multiplier,
    weightedComplexAction_eq_multiplier_mul_kernel, pow_succ]
  simpa only [mul_assoc] using
    congrArg (fun A : PathEnd S => A * GraphCore.pathProfileMultiplier tau)
      (mul_pow_mul (M.bjrModel.kernel.complexActionCLM M.bjrModel.mu)
        (GraphCore.pathProfileMultiplier tau) n)

/-- The Perron gauge controls powers of the paper-oriented operator
`K M_tau`, although the reusable Neumann bound was originally proved for
the opposite orientation `M_tau K`. -/
theorem pathOperator_pow_succ_norm_le (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (tau : C(S, ℂ))
    (q m : ℝ) (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x)
    (n : ℕ) :
    ‖(MPR.pathOperatorParameterCLM M tau) ^ (n + 1)‖ ≤
      ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * q ^ (n + 1) := by
  have htau : ‖tau‖ ≤ q :=
    (ContinuousMap.norm_le tau hq).2 ha
  have hmult : ‖GraphCore.pathProfileMultiplier tau‖ ≤ q :=
    (pathProfileMultiplier_norm_le tau).trans htau
  rw [pathOperator_pow_succ_factorization]
  calc
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu *
        TON.weightedComplexAction M tau ^ n *
          GraphCore.pathProfileMultiplier tau‖ ≤
        (‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
          ‖TON.weightedComplexAction M tau ^ n‖) *
            ‖GraphCore.pathProfileMultiplier tau‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
          (q ^ n * (‖M.continuousPerronFunction hM‖ / m))) * q := by
      gcongr
      exact TON.weightedComplexAction_pow_norm_le
        M hM tau q m hq ha hm hmu n
    _ = ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * q ^ (n + 1) := by ring

theorem profilePathOperator_pow_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    Summable (fun n : ℕ => (MPR.pathOperatorParameterCLM M tau) ^ n) := by
  obtain ⟨m, hm, hmu'⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  have hmu : ∀ x, m ≤ M.continuousPerronFunction hM x :=
    fun x => hmu' x (Set.mem_univ x)
  let C : ℝ := max 1
    (‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
      (‖M.continuousPerronFunction hM‖ / m))
  have hKC : ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
      (‖M.continuousPerronFunction hM‖ / m) ≤ C := by
    dsimp [C]
    exact le_max_right (1 : ℝ) _
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq1
  have hmajor : Summable (fun n : ℕ =>
      C * q ^ n) := hgeom.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact ContinuousLinearMap.norm_id_le.trans (by
        dsimp [C]
        exact le_max_left (1 : ℝ) _)
  | succ n =>
      have hp := pathOperator_pow_succ_norm_le M hM tau q m hq ha hm hmu n
      exact hp.trans (mul_le_mul_of_nonneg_right hKC (pow_nonneg hq _))

/-- On the strict subcritical profile ball the full operator Neumann sum is
the actual ring inverse used by `MarkedPathResolvent`. -/
theorem profilePathOperator_tsum_eq_inverse
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    (∑' n : ℕ, (MPR.pathOperatorParameterCLM M tau) ^ n) =
      Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) := by
  let L := MPR.pathOperatorParameterCLM M tau
  have hs : Summable (fun n : ℕ => L ^ n) :=
    profilePathOperator_pow_summable M hM tau q hq hq1 ha
  let U : (PathEnd S)ˣ :=
    ⟨1 - L, ∑' n : ℕ, L ^ n,
      hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  have hU : (U : PathEnd S) = 1 - L := rfl
  have hUinv : ((U⁻¹ : (PathEnd S)ˣ) : PathEnd S) =
      ∑' n : ℕ, L ^ n := rfl
  rw [← hU, Ring.inverse_unit, hUinv]


/-- The existing literal integral coefficient is the finite actual path power. -/
theorem literal_pathWeight_eq_operatorPower (M : FiniteIrreducibleModel S)
    (tau : C(S, ℂ)) (n : ℕ) (a b : S) :
    GraphCore.complexProfilePathWeight M.bjrModel tau n a b =
      ((MPR.pathOperatorParameterCLM M tau ^ n)
        (M.bjrModel.kernel.complexColumns b)) a := by
  exact GraphCore.complexProfilePathWeight_eq_operatorPower M.bjrModel tau n a b

/-- The Banach-valued Neumann coefficients converge to the genuine path kernel. -/
theorem hasSum_pathCoefficientKernel (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (tau : C(S, ℂ)) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖tau x‖ ≤ q) :
    HasSum
      (fun n : ℕ => MPR.operatorKernelize M (MPR.pathOperatorParameterCLM M tau ^ n))
      (MPR.operatorKernelize M (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau))) := by
  have hs := profilePathOperator_pow_summable M hM tau q hq hq1 ha
  have hsum : HasSum (fun n : ℕ => MPR.pathOperatorParameterCLM M tau ^ n)
      (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau)) := by
    rw [← profilePathOperator_tsum_eq_inverse M hM tau q hq hq1 ha]
    exact hs.hasSum
  exact hsum.map (MPR.operatorKernelize M) (MPR.operatorKernelize M).continuous

/-- Summing the literal finite-dimensional path integrals gives the actual kernel. -/
theorem hasSum_literal_pathWeight (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (tau : C(S, ℂ)) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖tau x‖ ≤ q) (a b : S) :
    HasSum (fun n : ℕ => GraphCore.complexProfilePathWeight M.bjrModel tau n a b)
      (MPR.operatorKernelize M
        (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau)) (a,b)) := by
  have hs := hasSum_pathCoefficientKernel M hM tau q hq hq1 ha
  have hev := hs.map (ContinuousMap.evalCLM ℂ (a,b))
    (ContinuousMap.evalCLM ℂ (a,b)).continuous
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, MPR.operatorKernelize_apply,
    literal_pathWeight_eq_operatorPower] using hev

/-- On an actual subcritical fold profile, the literal path weights sum to its
true rank-one-pole resolvent. -/
theorem hasSum_literal_fold_pathWeight (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (p : C(S, ℂ) × ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖MPR.profile M hM p x‖ ≤ q) (a b : S) :
    HasSum
      (fun n : ℕ => GraphCore.complexProfilePathWeight M.bjrModel
        (MPR.profile M hM p) n a b)
      (MPR.pathResolventKernel M hM p (a,b)) := by
  exact hasSum_literal_pathWeight M hM (MPR.profile M hM p) q hq hq1 ha a b

/-- A fixed bounded endpoint table is literally a finite product of these
path sums; every coefficient retains the existing finite path-integral definition. -/
theorem prod_tsum_literalPathWeight_eq_pathResolventKernel
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell) (x : Fin D.1.val → S)
    (p : C(S, ℂ) × ℂ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ y, ‖MPR.profile M hM p y‖ ≤ q) :
    (∏ e : Fin D.2.1.val,
      ∑' n : ℕ, GraphCore.complexProfilePathWeight M.bjrModel
        (MPR.profile M hM p) n
        (x (GraphCore.boundedKernelOrderedEndpoints D e).1)
        (x (GraphCore.boundedKernelOrderedEndpoints D e).2)) =
    ∏ e : Fin D.2.1.val, MPR.pathResolventKernel M hM p
      (x (GraphCore.boundedKernelOrderedEndpoints D e).1,
       x (GraphCore.boundedKernelOrderedEndpoints D e).2) := by
  apply Finset.prod_congr rfl
  intro e _
  exact (hasSum_literal_fold_pathWeight M hM p q hq hq1 ha _ _).tsum_eq

end PerronWright.FiniteIrreduciblePathGeneratingSeries

