import PerronWright.Analysis.FiniteIrreducibleSimpleCycleResolventBridge
import PerronWright.Analysis.FiniteIrreduciblePathGeneratingSeries
import PerronWright.Enumeration.JointSimpleCycleEGF

/-!
# The genuine finite profile simple-cycle series

All data-only cycle trace and finite differentiation identities are reused
on the literal discrete BJR data. The convergence estimates and Neumann
inverse use the proved finite Perron gauge and permit the eigenvalue -1.
-/

open MeasureTheory PerronWright
open scoped Topology RightActions
noncomputable section

namespace PerronWright.FiniteIrreducibleJointSimpleCycleEGF

open PerronWright.JointSimpleCycleEGF

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (profile pathOperatorParameterCLM pathOperator)
end MPR

namespace Bounds
export PerronWright.FiniteIrreduciblePathGeneratingSeries
  (pathOperator_pow_succ_norm_le profilePathOperator_pow_summable
   profilePathOperator_tsum_eq_inverse)
end Bounds

open Bounds

namespace MCS
export PerronWright.FiniteIrreducibleMarkedCycleSingularity
  (jointProfileVertical cycleResolventDerivative)
end MCS

namespace SCRB
export PerronWright.FiniteIrreducibleSimpleCycleResolventBridge
  (lengthOneCorrection lengthTwoCorrection simpleCycleDerivativeContinuation)
end SCRB

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

@[simp] theorem pathOperatorParameterCLM_eq_bjr
    (M : FiniteIrreducibleModel S) :
    MPR.pathOperatorParameterCLM M =
      MarkedPathResolvent.pathOperatorParameterCLM M.bjrModel := by
  rfl

omit [MeasurableSpace S] [BorelSpace S] in
private theorem perronFunction_uniform_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ M.continuousPerronFunction hM x := by
  obtain ⟨m, hm, hmu⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  exact ⟨m, hm, fun x => hmu x (Set.mem_univ x)⟩

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

/-- Uniform geometric bound for the derivative of one simple-cycle term. -/
theorem norm_profileSimpleCycleTerm_deriv_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau v : C(S, ℂ)) (q m c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x)
    (hv : ‖v‖ ≤ c) (n : ℕ) :
    ‖(1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
        ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v‖ ≤
      ((1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
        ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * c * q ^ 2) * q ^ n := by
  have hp := pathOperator_pow_succ_norm_le M hM tau q m hq ha hm hmu (n + 1)
  have hpair := norm_operatorCyclePairing_le M.bjrModel
    ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v
  calc
    ‖(1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
          (MPR.pathOperatorParameterCLM M tau ^ (n + 2)) v‖ =
      (1 / 2 : ℝ) *
        ‖operatorCyclePairing M.bjrModel
          (MPR.pathOperatorParameterCLM M tau ^ (n + 2)) v‖ := by
            rw [norm_mul]
            norm_num
    _ ≤
      (1 / 2 : ℝ) *
        (‖MPR.pathOperatorParameterCLM M tau ^ (n + 2)‖ *
          ‖M.bjrModel.kernel.toContinuousMap‖ * ‖v‖) := by gcongr
    _ ≤ (1 / 2 : ℝ) *
        ((‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
          (‖M.continuousPerronFunction hM‖ / m) * q ^ (n + 2)) *
            ‖M.bjrModel.kernel.toContinuousMap‖ * c) := by gcongr
    _ = ((1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
        ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * c * q ^ 2) * q ^ n := by ring

theorem norm_profileSimpleCycleTerm_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x)
    (n : ℕ) :
    ‖profileSimpleCycleTerm M.bjrModel tau n‖ ≤
      (‖M.bjrModel.kernel.toContinuousMap‖ *
        ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * q ^ 3) * q ^ n := by
  have htau : ‖tau‖ ≤ q := (ContinuousMap.norm_le tau hq).2 ha
  have hp := pathOperator_pow_succ_norm_le M hM tau q m hq ha hm hmu (n + 1)
  have hpair := norm_operatorCyclePairing_le M.bjrModel
    ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) tau
  have hden : 1 ≤ ‖(2 : ℂ) * ((n : ℂ) + 3)‖ := by
    rw [norm_mul]
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    have hrest : ‖(n : ℂ) + 3‖ = (n : ℝ) + 3 := by
      rw [show (n : ℂ) + 3 = (((n : ℝ) + 3 : ℝ) : ℂ) by norm_num,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [htwo, hrest]
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [profileSimpleCycleTerm, norm_div]
  calc
    ‖profileCycleTrace M.bjrModel tau (n + 2)‖ /
          ‖(2 : ℂ) * ((n : ℂ) + 3)‖ ≤
        ‖profileCycleTrace M.bjrModel tau (n + 2)‖ := by
      exact (div_le_iff₀ (by positivity)).2
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hden (norm_nonneg _))
    _ ≤ ‖MPR.pathOperatorParameterCLM M tau ^ (n + 2)‖ *
          ‖M.bjrModel.kernel.toContinuousMap‖ * ‖tau‖ := hpair
    _ ≤ (‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
          (‖M.continuousPerronFunction hM‖ / m) * q ^ (n + 2)) *
          ‖M.bjrModel.kernel.toContinuousMap‖ * q := by gcongr
    _ = (‖M.bjrModel.kernel.toContinuousMap‖ *
        ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * q ^ 3) * q ^ n := by ring

/-- The tail beginning with cycles of length three is exactly the inverse
minus its length-one and length-two terms. -/
theorem profilePathOperator_tail_two
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    (∑' n : ℕ, (MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) =
      Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
        MPR.pathOperatorParameterCLM M tau := by
  let L := MPR.pathOperatorParameterCLM M tau
  have hs : Summable (fun n : ℕ => L ^ n) :=
    profilePathOperator_pow_summable M hM tau q hq hq1 ha
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hfinite : ∑ i ∈ Finset.range 2, L ^ i = 1 + L := by
    norm_num [Finset.sum_range_succ]
  have hinv : (∑' n : ℕ, L ^ n) = Ring.inverse (1 - L) := by
    exact profilePathOperator_tsum_eq_inverse M hM tau q hq hq1 ha
  change (∑' n : ℕ, L ^ (n + 2)) = Ring.inverse (1 - L) - 1 - L
  rw [← hinv, ← hsplit, hfinite]
  noncomm_ring

/-- Scalar form of the preceding Neumann identity. -/
theorem profileCycleDerivativeTail_eq_resolvent
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau v : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    (∑' n : ℕ, operatorCyclePairing M.bjrModel
      ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v) =
      operatorCyclePairing M.bjrModel
        (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
          MPR.pathOperatorParameterCLM M tau) v := by
  have hs : Summable (fun n : ℕ =>
      (MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) :=
    (profilePathOperator_pow_summable M hM tau q hq hq1 ha).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hmap := ((operatorCyclePairingCLM M.bjrModel).flip v).map_tsum hs
  change (∑' n : ℕ, ((operatorCyclePairingCLM M.bjrModel).flip v)
      ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2))) =
    ((operatorCyclePairingCLM M.bjrModel).flip v)
      (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
        MPR.pathOperatorParameterCLM M tau)
  rw [← hmap, profilePathOperator_tail_two M hM tau q hq hq1 ha]

/-! ## The strict-subcritical profile series and its derivative -/

/-- Termwise differentiation is valid on every preconnected region on
which the profile stays in one strict Perron ball and its derivative is
uniformly bounded.  This is the reusable normal-convergence statement; all
hypotheses are discharged below from the actual analytic tree profile. -/
theorem profileSimpleCycleSeries_hasDerivAt_of_uniform_subcritical
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {s : Set ℂ} (hs : IsOpen s) (hsc : IsPreconnected s)
    (tau tau' : ℂ → C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c)
    (htau : ∀ z, z ∈ s → HasDerivAt tau (tau' z) z)
    (hprofile : ∀ z, z ∈ s → ∀ x, ‖tau z x‖ ≤ q)
    (hvelocity : ∀ z, z ∈ s → ‖tau' z‖ ≤ c)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ s) (hz : z ∈ s) :
    HasDerivAt (fun w => profileSimpleCycleSeries M.bjrModel (tau w))
      (profileSimpleCycleDerivative M.bjrModel (tau z) (tau' z)) z := by
  obtain ⟨m, hm, hmu⟩ := perronFunction_uniform_pos M hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * c * q ^ 2
  let V : ℝ := ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * q ^ 3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq1
  have hDu : Summable (fun n : ℕ => D * q ^ n) := hgeom.mul_left D
  have hVu : Summable (fun n : ℕ => V * q ^ n) := hgeom.mul_left V
  have hterm : ∀ n w, w ∈ s →
      HasDerivAt (fun y => profileSimpleCycleTerm M.bjrModel (tau y) n)
        ((1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
          ((MPR.pathOperatorParameterCLM M (tau w)) ^ (n + 2))
          (tau' w)) w := by
    intro n w hw
    exact profileSimpleCycleTerm_hasDerivAt M.bjrModel (htau w hw) n
  have hderivBound : ∀ n w, w ∈ s →
      ‖(1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
        ((MPR.pathOperatorParameterCLM M (tau w)) ^ (n + 2))
        (tau' w)‖ ≤ D * q ^ n := by
    intro n w hw
    exact norm_profileSimpleCycleTerm_deriv_le M hM
      (tau w) (tau' w) q m c hq (hprofile w hw) hm hmu
      (hvelocity w hw) n
  have hvalue₀ : Summable (fun n : ℕ =>
      profileSimpleCycleTerm M.bjrModel (tau z₀) n) := by
    apply Summable.of_norm_bounded hVu
    intro n
    exact norm_profileSimpleCycleTerm_le M hM (tau z₀) q m hq
      (hprofile z₀ hz₀) hm hmu n
  have hsum := hasDerivAt_tsum_of_isPreconnected hDu hs hsc hterm
    hderivBound hz₀ hvalue₀ hz
  have hsum' : HasDerivAt
      (fun w => profileSimpleCycleSeries M.bjrModel (tau w))
      (∑' n : ℕ, (1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
        ((MPR.pathOperatorParameterCLM M (tau z)) ^ (n + 2))
        (tau' z)) z := hsum
  apply hsum'.congr_deriv
  rw [profileSimpleCycleDerivative, tsum_mul_left]
  congr 1
  exact profileCycleDerivativeTail_eq_resolvent M hM
    (tau z) (tau' z) q hq hq1 (hprofile z hz)

/-- The direct strict-subcritical derivative and the independently
constructed singular continuation are the same concrete resolvent
expression when evaluated on the actual joint tree profile. -/
theorem profileSimpleCycleDerivative_actual_eq_continuation
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : C(S, ℂ) × ℂ) :
    profileSimpleCycleDerivative M.bjrModel (MPR.profile M hM q)
        (MCS.jointProfileVertical M hM q) =
      SCRB.simpleCycleDerivativeContinuation M hM q := by
  rw [profileSimpleCycleDerivative,
    SCRB.simpleCycleDerivativeContinuation,
    MCS.cycleResolventDerivative,
    SCRB.lengthOneCorrection, SCRB.lengthTwoCorrection]
  change (1 / 2 : ℂ) * operatorCyclePairing M.bjrModel
      (Ring.inverse (1 - MPR.pathOperator M hM q) - 1 -
        MPR.pathOperator M hM q) (MCS.jointProfileVertical M hM q) =
    (1 / 2 : ℂ) *
      (operatorCyclePairing M.bjrModel
          (Ring.inverse (1 - MPR.pathOperator M hM q))
          (MCS.jointProfileVertical M hM q) -
        operatorCyclePairing M.bjrModel 1 (MCS.jointProfileVertical M hM q) -
        operatorCyclePairing M.bjrModel (MPR.pathOperator M hM q)
          (MCS.jointProfileVertical M hM q))
  congr 1
  simp only [← operatorCyclePairingCLM_apply, map_sub, sub_apply]


end PerronWright.FiniteIrreducibleJointSimpleCycleEGF
