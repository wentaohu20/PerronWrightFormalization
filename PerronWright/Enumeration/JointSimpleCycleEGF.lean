import PerronWright.Analysis.SimpleCycleResolventBridge
import PerronWright.Analysis.TreeOuterNeumann
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The profile simple-cycle series on the strict subcritical region

This module develops the analytic bridge without a determinant.
For a complex tree profile `tau`, put `L_tau = K M_tau`.  The cycle of
length `n+1` is represented by

`integral tau(x) ((L_tau)^n K(.,x))(x) dmu(x)`.

The key finite identity below is cyclic rotation of this trace.  It is
proved directly by Fubini and by commuting a bounded operator with a
Bochner integral; no abstract trace-class interface is assumed.
-/

open MeasureTheory PerronWright
open scoped Topology RightActions

noncomputable section

namespace PerronWright.JointSimpleCycleEGF

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply profile
   pathOperatorParameterCLM pathOperator operatorKernelize
   operatorKernelize_apply pathResolventKernel)

end MPR

namespace TON

export PerronWright.TreeOuterNeumann
  (weightedComplexAction weightedComplexAction_apply
   weightedComplexAction_pow_norm_le)

end TON

variable {S : Type*} [MetricSpace S] [CompactSpace S]
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

private def diagonalMap : C(S, S × S) :=
  ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

private def diagonalRestrictionCLM : C(S × S, ℂ) →L[ℂ] C(S, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ diagonalMap

/-- Diagonal trace pairing of the kernel of `B K` with a terminal profile.
When `B = (K M_tau)^n`, this is the cycle trace of length `n+1`. -/
def operatorCyclePairing (M : CompactBJRModel S)
    (B : PathEnd S) (v : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M (diagonalRestrictionCLM (MPR.operatorKernelize M B) * v)

@[simp] theorem operatorCyclePairing_apply (M : CompactBJRModel S)
    (B : PathEnd S) (v : C(S, ℂ)) :
    operatorCyclePairing M B v =
      ∫ x, B (M.kernel.complexColumns x) x * v x ∂M.mu := by
  rw [operatorCyclePairing, MPR.scalarIntegralCLM_apply]
  rfl

@[simp] theorem pathOperatorParameterCLM_apply
    (M : CompactBJRModel S) (tau f : C(S, ℂ)) :
    MPR.pathOperatorParameterCLM M tau f =
      M.kernel.complexAction M.mu (tau * f) := by
  simp only [MPR.pathOperatorParameterCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    MarkedPathResolvent.profileMultiplierCLM_apply,
    GraphCore.pathProfileMultiplier_apply,
    ContinuousKernel.complexActionCLM_apply]

/-- The continuous family of columns that closes one cycle after Fubini. -/
private def closingColumnIntegrand (M : CompactBJRModel S)
    (v : C(S, ℂ)) (y : S) : C(S, C(S, ℂ)) :=
  ⟨fun x => (v x * (M.kernel x y : ℂ)) • M.kernel.complexColumns x,
    by fun_prop⟩

private theorem integrable_closingColumnIntegrand (M : CompactBJRModel S)
    (v : C(S, ℂ)) (y : S) :
    Integrable (closingColumnIntegrand M v y) M.mu := by
  apply (closingColumnIntegrand M v y).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

private theorem integral_closingColumnIntegrand (M : CompactBJRModel S)
    (v : C(S, ℂ)) (y : S) :
    (∫ x, closingColumnIntegrand M v y x ∂M.mu) =
      MPR.pathOperatorParameterCLM M v (M.kernel.complexColumns y) := by
  ext z
  rw [ContinuousMap.integral_apply
    (integrable_closingColumnIntegrand M v y) z,
    pathOperatorParameterCLM_apply,
    ContinuousKernel.complexAction_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  change (v x * (M.kernel x y : ℂ)) * (M.kernel z x : ℂ) =
    (M.kernel z x : ℂ) * (v x * (M.kernel x y : ℂ))
  ring

/-- Finite trace cyclicity in the only form needed below.  It rotates the
leading factor `K M_tau` past an arbitrary bounded middle operator. -/
theorem operatorCyclePairing_rotate (M : CompactBJRModel S)
    (tau v : C(S, ℂ)) (B : PathEnd S) :
    operatorCyclePairing M
        (MPR.pathOperatorParameterCLM M tau * B) v =
      operatorCyclePairing M
        (B * MPR.pathOperatorParameterCLM M v) tau := by
  rw [operatorCyclePairing_apply, operatorCyclePairing_apply]
  simp only [mul_apply_eq_comp, pathOperatorParameterCLM_apply]
  calc
    (∫ x, M.kernel.complexAction M.mu
          (tau * B (M.kernel.complexColumns x)) x * v x ∂M.mu) =
        ∫ x, ∫ y, ((M.kernel x y : ℂ) *
          (tau y * B (M.kernel.complexColumns x) y)) * v x
          ∂M.mu ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [ContinuousKernel.complexAction_apply, integral_mul_const]
      apply congrArg (fun z : ℂ => z * v x)
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [ContinuousMap.mul_apply]
    _ = ∫ y, ∫ x, ((M.kernel x y : ℂ) *
          (tau y * B (M.kernel.complexColumns x) y)) * v x
          ∂M.mu ∂M.mu := by
      exact integral_integral_swap_of_hasCompactSupport
        (μ := M.mu) (ν := M.mu)
        (f := fun x y => ((M.kernel x y : ℂ) *
          (tau y * B (M.kernel.complexColumns x) y)) * v x)
        (by fun_prop) isClosed_closure.isCompact
    _ = ∫ y, B (∫ x, closingColumnIntegrand M v y x ∂M.mu) y *
          tau y ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hB := B.integral_comp_comm (integrable_closingColumnIntegrand M v y)
      have heval := ContinuousMap.integral_apply
        (B.integrable_comp (integrable_closingColumnIntegrand M v y)) y
      rw [← hB, heval, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      change (M.kernel x y : ℂ) *
          (tau y * B (M.kernel.complexColumns x) y) * v x =
        B ((v x * (M.kernel x y : ℂ)) • M.kernel.complexColumns x) y * tau y
      rw [map_smul]
      change (M.kernel x y : ℂ) *
          (tau y * B (M.kernel.complexColumns x) y) * v x =
        (v x * (M.kernel x y : ℂ)) * B (M.kernel.complexColumns x) y * tau y
      rw [M.kernel.symmetric x y]
      ring
    _ = ∫ y, B (M.kernel.complexAction M.mu
          (v * M.kernel.complexColumns y)) y * tau y ∂M.mu := by
      simp_rw [integral_closingColumnIntegrand,
        pathOperatorParameterCLM_apply]

/-- The direct complex trace of a cycle of length `n+1` with common vertex
profile `tau`. -/
def profileCycleTrace (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (n : ℕ) : ℂ :=
  operatorCyclePairing M ((MPR.pathOperatorParameterCLM M tau) ^ n) tau

/-- Direct simple-cycle term of length `n+3`. -/
def profileSimpleCycleTerm (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (n : ℕ) : ℂ :=
  profileCycleTrace M tau (n + 2) / ((2 : ℂ) * ((n : ℂ) + 3))

/-- The direct profile simple-cycle series.  Outside its convergence region
the `tsum` convention gives zero; all theorems below explicitly work in a
strict subcritical region. -/
def profileSimpleCycleSeries (M : CompactBJRModel S)
    (tau : C(S, ℂ)) : ℂ :=
  ∑' n : ℕ, profileSimpleCycleTerm M tau n

/-! ## Finite cyclicity and the exact derivative of one cycle -/

private theorem operatorCyclePairing_rotate_same_power
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (B : PathEnd S) (p : ℕ) :
    operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M tau) ^ p * B) tau =
      operatorCyclePairing M
        (B * (MPR.pathOperatorParameterCLM M tau) ^ p) tau := by
  let L := MPR.pathOperatorParameterCLM M tau
  induction p generalizing B with
  | zero => simp
  | succ p ih =>
      calc
        operatorCyclePairing M (L ^ (p + 1) * B) tau =
            operatorCyclePairing M (L * (L ^ p * B)) tau := by
              simp only [pow_succ', mul_assoc]
        _ = operatorCyclePairing M ((L ^ p * B) * L) tau := by
              exact operatorCyclePairing_rotate M tau tau (L ^ p * B)
        _ = operatorCyclePairing M (L ^ p * (B * L)) tau := by
              simp only [mul_assoc]
        _ = operatorCyclePairing M ((B * L) * L ^ p) tau := ih (B * L)
        _ = operatorCyclePairing M (B * L ^ (p + 1)) tau := by
              simp only [pow_succ', mul_assoc]

/-- Every insertion in the derivative of a power has the same cycle trace.
This is the precise finite trace-cyclicity statement needed for the power
rule; it does not use an abstract nuclear trace. -/
theorem operatorCyclePairing_power_insertion
    (M : CompactBJRModel S) (tau v : C(S, ℂ)) (p q : ℕ) :
    operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M tau) ^ p *
          MPR.pathOperatorParameterCLM M v *
          (MPR.pathOperatorParameterCLM M tau) ^ q) tau =
      operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M tau) ^ (p + q + 1)) v := by
  let L := MPR.pathOperatorParameterCLM M tau
  let V := MPR.pathOperatorParameterCLM M v
  calc
    operatorCyclePairing M (L ^ p * V * L ^ q) tau =
        operatorCyclePairing M (L ^ p * (V * L ^ q)) tau := by
          simp only [mul_assoc]
    _ = operatorCyclePairing M ((V * L ^ q) * L ^ p) tau :=
      operatorCyclePairing_rotate_same_power M tau (V * L ^ q) p
    _ = operatorCyclePairing M (V * L ^ (q + p)) tau := by
      simp only [pow_add, mul_assoc]
    _ = operatorCyclePairing M (L ^ (q + p) * L) v := by
      exact operatorCyclePairing_rotate M v tau (L ^ (q + p))
    _ = operatorCyclePairing M (L ^ (p + q + 1)) v := by
      simp only [pow_succ, add_comm]

/-- The trace pairing as a bounded bilinear map. -/
def operatorCyclePairingCLM (M : CompactBJRModel S) :
    PathEnd S →L[ℂ] C(S, ℂ) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ C(S, ℂ) C(S, ℂ) ℂ)
      (MPR.scalarIntegralCLM M)).comp
    ((ContinuousLinearMap.mul ℂ C(S, ℂ)).comp
      ((diagonalRestrictionCLM (S := S)).comp (MPR.operatorKernelize M)))

@[simp] theorem operatorCyclePairingCLM_apply
    (M : CompactBJRModel S) (B : PathEnd S) (v : C(S, ℂ)) :
    operatorCyclePairingCLM M B v = operatorCyclePairing M B v := by
  rfl

private theorem operatorCyclePairing_zero_right (M : CompactBJRModel S)
    (B : PathEnd S) : operatorCyclePairing M B 0 = 0 := by
  rw [← operatorCyclePairingCLM_apply]
  exact map_zero _

private theorem profileCycleTrace_zero (M : CompactBJRModel S) (n : ℕ) :
    profileCycleTrace M 0 n = 0 := by
  simp [profileCycleTrace]

/-- Exact derivative of one finite cycle along an arbitrary analytic profile
curve.  The factor `n+1` is obtained by rotating every noncommutative power
insertion to the same diagonal pairing. -/
theorem profileCycleTrace_hasDerivAt
    (M : CompactBJRModel S) {tau : ℂ → C(S, ℂ)} {z : ℂ}
    {v : C(S, ℂ)} (htau : HasDerivAt tau v z) (n : ℕ) :
    HasDerivAt (fun w => profileCycleTrace M (tau w) n)
      (((n : ℂ) + 1) *
        operatorCyclePairing M
          ((MPR.pathOperatorParameterCLM M (tau z)) ^ n) v) z := by
  let L : ℂ → PathEnd S := fun w => MPR.pathOperatorParameterCLM M (tau w)
  let L' : PathEnd S := MPR.pathOperatorParameterCLM M v
  have hL : HasDerivAt L L' z := by
    exact (MPR.pathOperatorParameterCLM M).hasFDerivAt.comp_hasDerivAt z htau
  have hpow := hL.hasFDerivAt.pow' n
  have hpair : HasDerivAt
      (fun w => operatorCyclePairingCLM M ((L w) ^ n) (tau w))
      (operatorCyclePairingCLM M ((L z) ^ n) v +
        operatorCyclePairingCLM M
          (∑ i ∈ Finset.range n, L z ^ (n.pred - i) * L' * L z ^ i)
          (tau z)) z := by
    have hconst : HasFDerivAt
        (fun _ : ℂ => operatorCyclePairingCLM M)
        (0 : ℂ →L[ℂ] (PathEnd S →L[ℂ] C(S, ℂ) →L[ℂ] ℂ)) z :=
      hasFDerivAt_const (operatorCyclePairingCLM M) z
    have hc := HasFDerivAt.clm_apply
      (𝕜 := ℂ) (E := ℂ) (G := PathEnd S) (H := C(S, ℂ) →L[ℂ] ℂ)
      hconst hpow
    simpa [operatorCyclePairingCLM_apply] using
      (HasFDerivAt.clm_apply
        (𝕜 := ℂ) (E := ℂ) (G := C(S, ℂ)) (H := ℂ) hc
        htau.hasFDerivAt).hasDerivAt
  change HasDerivAt
    (fun w => operatorCyclePairingCLM M ((L w) ^ n) (tau w))
    (((n : ℂ) + 1) * operatorCyclePairing M (L z ^ n) v) z
  apply hpair.congr_deriv
  have hterm : ∀ i ∈ Finset.range n,
      operatorCyclePairing M
          (L z ^ (n.pred - i) * L' * L z ^ i) (tau z) =
        operatorCyclePairing M (L z ^ n) v := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hi : i ≤ n.pred := Nat.le_pred_of_lt hin
    rw [operatorCyclePairing_power_insertion]
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hin
    have heq : n.pred - i + i + 1 = n := by
      rw [Nat.sub_add_cancel hi]
      simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hnpos
    rw [heq]
  have hsum : operatorCyclePairingCLM M
        (∑ i ∈ Finset.range n, L z ^ (n.pred - i) * L' * L z ^ i)
        (tau z) =
      (n : ℂ) * operatorCyclePairing M (L z ^ n) v := by
    let phi : PathEnd S →L[ℂ] ℂ :=
      (operatorCyclePairingCLM M).flip (tau z)
    change phi (∑ i ∈ Finset.range n,
      L z ^ (n.pred - i) * L' * L z ^ i) = _
    rw [map_sum]
    calc
      (∑ i ∈ Finset.range n,
          phi (L z ^ (n.pred - i) * L' * L z ^ i)) =
          ∑ _i ∈ Finset.range n,
            operatorCyclePairing M (L z ^ n) v := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa only [phi, ContinuousLinearMap.flip_apply,
                operatorCyclePairingCLM_apply] using hterm i hi
      _ = (n : ℂ) * operatorCyclePairing M (L z ^ n) v := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [operatorCyclePairingCLM_apply, hsum]
  ring

/-- Exact derivative of the length `n+3` simple-cycle term. -/
theorem profileSimpleCycleTerm_hasDerivAt
    (M : CompactBJRModel S) {tau : ℂ → C(S, ℂ)} {z : ℂ}
    {v : C(S, ℂ)} (htau : HasDerivAt tau v z) (n : ℕ) :
    HasDerivAt (fun w => profileSimpleCycleTerm M (tau w) n)
      ((1 / 2 : ℂ) * operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M (tau z)) ^ (n + 2)) v) z := by
  have h := (profileCycleTrace_hasDerivAt M htau (n + 2)).div_const
      ((2 : ℂ) * ((n : ℂ) + 3))
  change HasDerivAt
    (fun w => profileCycleTrace M (tau w) (n + 2) /
      ((2 : ℂ) * ((n : ℂ) + 3)))
    ((1 / 2 : ℂ) * operatorCyclePairing M
      ((MPR.pathOperatorParameterCLM M (tau z)) ^ (n + 2)) v) z
  apply h.congr_deriv
  have hn : (n : ℂ) + 3 ≠ 0 := by
    exact_mod_cast (by omega : n + 3 ≠ 0)
  rw [show ((n + 2 : ℕ) : ℂ) + 1 = (n : ℂ) + 3 by
    push_cast
    ring]
  field_simp [hn]

/-! ## Uniform Perron-gauge majorants -/

theorem norm_operatorCyclePairing_le (M : CompactBJRModel S)
    (B : PathEnd S) (v : C(S, ℂ)) :
    ‖operatorCyclePairing M B v‖ ≤
      ‖B‖ * ‖M.kernel.toContinuousMap‖ * ‖v‖ := by
  rw [operatorCyclePairing_apply]
  calc
    ‖∫ x, B (M.kernel.complexColumns x) x * v x ∂M.mu‖ ≤
        (‖B‖ * ‖M.kernel.toContinuousMap‖ * ‖v‖) *
          M.mu.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with x
      rw [norm_mul]
      calc
        ‖B (M.kernel.complexColumns x) x‖ * ‖v x‖ ≤
            (‖B‖ * ‖M.kernel.complexColumns x‖) * ‖v x‖ := by
          gcongr
          exact (B (M.kernel.complexColumns x)).norm_coe_le_norm x |>.trans
            (B.le_opNorm (M.kernel.complexColumns x))
        _ ≤ (‖B‖ * ‖M.kernel.toContinuousMap‖) * ‖v‖ := by
          gcongr
          · exact M.kernel.norm_complexColumns_le x
          · exact v.norm_coe_le_norm x
        _ = ‖B‖ * ‖M.kernel.toContinuousMap‖ * ‖v‖ := by ring
    _ = ‖B‖ * ‖M.kernel.toContinuousMap‖ * ‖v‖ := by
      simp only [probReal_univ, mul_one]

omit [MeasurableSpace S] [BorelSpace S] in
private theorem pathProfileMultiplier_norm_le (tau : C(S, ℂ)) :
    ‖GraphCore.pathProfileMultiplier tau‖ ≤ ‖tau‖ := by
  calc
    ‖GraphCore.pathProfileMultiplier tau‖ ≤
        ‖tau‖ * ‖(1 : C(S, ℂ))‖ := by
      exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le
        ℂ C(S, ℂ) tau 1
    _ ≤ ‖tau‖ * 1 := by
      gcongr
      apply (ContinuousMap.norm_le (1 : C(S, ℂ)) zero_le_one).2
      intro x
      norm_num
    _ = ‖tau‖ := by rw [mul_one]

private theorem pathOperatorParameter_eq_kernel_mul_multiplier
    (M : CompactBJRModel S) (tau : C(S, ℂ)) :
    MPR.pathOperatorParameterCLM M tau =
      M.kernel.complexActionCLM M.mu * GraphCore.pathProfileMultiplier tau := by
  rfl

private theorem weightedComplexAction_eq_multiplier_mul_kernel
    (M : CompactBJRModel S) (tau : C(S, ℂ)) :
    TON.weightedComplexAction M tau =
      GraphCore.pathProfileMultiplier tau * M.kernel.complexActionCLM M.mu := by
  rfl

private theorem pathOperator_pow_succ_factorization
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (n : ℕ) :
    (MPR.pathOperatorParameterCLM M tau) ^ (n + 1) =
      M.kernel.complexActionCLM M.mu *
        (TON.weightedComplexAction M tau) ^ n *
          GraphCore.pathProfileMultiplier tau := by
  rw [pathOperatorParameter_eq_kernel_mul_multiplier,
    weightedComplexAction_eq_multiplier_mul_kernel, pow_succ]
  simpa only [mul_assoc] using
    congrArg (fun A : PathEnd S => A * GraphCore.pathProfileMultiplier tau)
      (mul_pow_mul (M.kernel.complexActionCLM M.mu)
        (GraphCore.pathProfileMultiplier tau) n)

/-- The Perron gauge controls powers of the paper-oriented operator
`K M_tau`, although the reusable Neumann bound was originally proved for
the opposite orientation `M_tau K`. -/
theorem pathOperator_pow_succ_norm_le (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (tau : C(S, ℂ))
    (q m : ℝ) (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x)
    (n : ℕ) :
    ‖(MPR.pathOperatorParameterCLM M tau) ^ (n + 1)‖ ≤
      ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * q ^ (n + 1) := by
  have htau : ‖tau‖ ≤ q :=
    (ContinuousMap.norm_le tau hq).2 ha
  have hmult : ‖GraphCore.pathProfileMultiplier tau‖ ≤ q :=
    (pathProfileMultiplier_norm_le tau).trans htau
  rw [pathOperator_pow_succ_factorization]
  calc
    ‖M.kernel.complexActionCLM M.mu *
        TON.weightedComplexAction M tau ^ n *
          GraphCore.pathProfileMultiplier tau‖ ≤
        (‖M.kernel.complexActionCLM M.mu‖ *
          ‖TON.weightedComplexAction M tau ^ n‖) *
            ‖GraphCore.pathProfileMultiplier tau‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖M.kernel.complexActionCLM M.mu‖ *
          (q ^ n * (‖M.perronFunction hM‖ / m))) * q := by
      gcongr
      exact TON.weightedComplexAction_pow_norm_le
        M hM tau q m hq ha hm hmu n
    _ = ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * q ^ (n + 1) := by ring

/-- Uniform geometric bound for the derivative of one simple-cycle term. -/
theorem norm_profileSimpleCycleTerm_deriv_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau v : C(S, ℂ)) (q m c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x)
    (hv : ‖v‖ ≤ c) (n : ℕ) :
    ‖(1 / 2 : ℂ) * operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v‖ ≤
      ((1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
        ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * c * q ^ 2) * q ^ n := by
  have hp := pathOperator_pow_succ_norm_le M hM tau q m hq ha hm hmu (n + 1)
  have hpair := norm_operatorCyclePairing_le M
    ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v
  calc
    ‖(1 / 2 : ℂ) * operatorCyclePairing M
          (MPR.pathOperatorParameterCLM M tau ^ (n + 2)) v‖ =
      (1 / 2 : ℝ) *
        ‖operatorCyclePairing M
          (MPR.pathOperatorParameterCLM M tau ^ (n + 2)) v‖ := by
            rw [norm_mul]
            norm_num
    _ ≤
      (1 / 2 : ℝ) *
        (‖MPR.pathOperatorParameterCLM M tau ^ (n + 2)‖ *
          ‖M.kernel.toContinuousMap‖ * ‖v‖) := by gcongr
    _ ≤ (1 / 2 : ℝ) *
        ((‖M.kernel.complexActionCLM M.mu‖ *
          (‖M.perronFunction hM‖ / m) * q ^ (n + 2)) *
            ‖M.kernel.toContinuousMap‖ * c) := by gcongr
    _ = ((1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
        ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * c * q ^ 2) * q ^ n := by ring

theorem norm_profileSimpleCycleTerm_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x)
    (n : ℕ) :
    ‖profileSimpleCycleTerm M tau n‖ ≤
      (‖M.kernel.toContinuousMap‖ *
        ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * q ^ 3) * q ^ n := by
  have htau : ‖tau‖ ≤ q := (ContinuousMap.norm_le tau hq).2 ha
  have hp := pathOperator_pow_succ_norm_le M hM tau q m hq ha hm hmu (n + 1)
  have hpair := norm_operatorCyclePairing_le M
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
    ‖profileCycleTrace M tau (n + 2)‖ /
          ‖(2 : ℂ) * ((n : ℂ) + 3)‖ ≤
        ‖profileCycleTrace M tau (n + 2)‖ := by
      exact (div_le_iff₀ (by positivity)).2
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hden (norm_nonneg _))
    _ ≤ ‖MPR.pathOperatorParameterCLM M tau ^ (n + 2)‖ *
          ‖M.kernel.toContinuousMap‖ * ‖tau‖ := hpair
    _ ≤ (‖M.kernel.complexActionCLM M.mu‖ *
          (‖M.perronFunction hM‖ / m) * q ^ (n + 2)) *
          ‖M.kernel.toContinuousMap‖ * q := by gcongr
    _ = (‖M.kernel.toContinuousMap‖ *
        ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * q ^ 3) * q ^ n := by ring

theorem profilePathOperator_pow_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    Summable (fun n : ℕ => (MPR.pathOperatorParameterCLM M tau) ^ n) := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let C : ℝ := max 1
    (‖M.kernel.complexActionCLM M.mu‖ *
      (‖M.perronFunction hM‖ / m))
  have hKC : ‖M.kernel.complexActionCLM M.mu‖ *
      (‖M.perronFunction hM‖ / m) ≤ C := by
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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

/-- The tail beginning with cycles of length three is exactly the inverse
minus its length-one and length-two terms. -/
theorem profilePathOperator_tail_two
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
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
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau v : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    (∑' n : ℕ, operatorCyclePairing M
      ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) v) =
      operatorCyclePairing M
        (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
          MPR.pathOperatorParameterCLM M tau) v := by
  have hs : Summable (fun n : ℕ =>
      (MPR.pathOperatorParameterCLM M tau) ^ (n + 2)) :=
    (profilePathOperator_pow_summable M hM tau q hq hq1 ha).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hmap := ((operatorCyclePairingCLM M).flip v).map_tsum hs
  change (∑' n : ℕ, ((operatorCyclePairingCLM M).flip v)
      ((MPR.pathOperatorParameterCLM M tau) ^ (n + 2))) =
    ((operatorCyclePairingCLM M).flip v)
      (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
        MPR.pathOperatorParameterCLM M tau)
  rw [← hmap, profilePathOperator_tail_two M hM tau q hq hq1 ha]

/-! ## The strict-subcritical profile series and its derivative -/

/-- The direct profile-series derivative written with the actual operator
inverse. -/
def profileSimpleCycleDerivative (M : CompactBJRModel S)
    (tau v : C(S, ℂ)) : ℂ :=
  (1 / 2 : ℂ) * operatorCyclePairing M
    (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau) - 1 -
      MPR.pathOperatorParameterCLM M tau) v

/-- Termwise differentiation is valid on every preconnected region on
which the profile stays in one strict Perron ball and its derivative is
uniformly bounded.  This is the reusable normal-convergence statement; all
hypotheses are discharged below from the actual analytic tree profile. -/
theorem profileSimpleCycleSeries_hasDerivAt_of_uniform_subcritical
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {s : Set ℂ} (hs : IsOpen s) (hsc : IsPreconnected s)
    (tau tau' : ℂ → C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c)
    (htau : ∀ z, z ∈ s → HasDerivAt tau (tau' z) z)
    (hprofile : ∀ z, z ∈ s → ∀ x, ‖tau z x‖ ≤ q)
    (hvelocity : ∀ z, z ∈ s → ‖tau' z‖ ≤ c)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ s) (hz : z ∈ s) :
    HasDerivAt (fun w => profileSimpleCycleSeries M (tau w))
      (profileSimpleCycleDerivative M (tau z) (tau' z)) z := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * c * q ^ 2
  let V : ℝ := ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * q ^ 3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq1
  have hDu : Summable (fun n : ℕ => D * q ^ n) := hgeom.mul_left D
  have hVu : Summable (fun n : ℕ => V * q ^ n) := hgeom.mul_left V
  have hterm : ∀ n w, w ∈ s →
      HasDerivAt (fun y => profileSimpleCycleTerm M (tau y) n)
        ((1 / 2 : ℂ) * operatorCyclePairing M
          ((MPR.pathOperatorParameterCLM M (tau w)) ^ (n + 2))
          (tau' w)) w := by
    intro n w hw
    exact profileSimpleCycleTerm_hasDerivAt M (htau w hw) n
  have hderivBound : ∀ n w, w ∈ s →
      ‖(1 / 2 : ℂ) * operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M (tau w)) ^ (n + 2))
        (tau' w)‖ ≤ D * q ^ n := by
    intro n w hw
    exact norm_profileSimpleCycleTerm_deriv_le M hM
      (tau w) (tau' w) q m c hq (hprofile w hw) hm hmu
      (hvelocity w hw) n
  have hvalue₀ : Summable (fun n : ℕ =>
      profileSimpleCycleTerm M (tau z₀) n) := by
    apply Summable.of_norm_bounded hVu
    intro n
    exact norm_profileSimpleCycleTerm_le M hM (tau z₀) q m hq
      (hprofile z₀ hz₀) hm hmu n
  have hsum := hasDerivAt_tsum_of_isPreconnected hDu hs hsc hterm
    hderivBound hz₀ hvalue₀ hz
  have hsum' : HasDerivAt
      (fun w => profileSimpleCycleSeries M (tau w))
      (∑' n : ℕ, (1 / 2 : ℂ) * operatorCyclePairing M
        ((MPR.pathOperatorParameterCLM M (tau z)) ^ (n + 2))
        (tau' z)) z := hsum
  apply hsum'.congr_deriv
  rw [profileSimpleCycleDerivative, tsum_mul_left]
  congr 1
  exact profileCycleDerivativeTail_eq_resolvent M hM
    (tau z) (tau' z) q hq hq1 (hprofile z hz)

namespace MCS

export PerronWright.MarkedCycleSingularity
  (jointProfileVertical cycleResolventDerivative)

end MCS

namespace SCRB

export PerronWright.SimpleCycleResolventBridge
  (lengthOneCorrection lengthTwoCorrection simpleCycleDerivativeContinuation)

end SCRB

/-- The direct strict-subcritical derivative and the independently
constructed singular continuation are the same concrete resolvent
expression when evaluated on the actual joint tree profile. -/
theorem profileSimpleCycleDerivative_actual_eq_continuation
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : C(S, ℂ) × ℂ) :
    profileSimpleCycleDerivative M (MPR.profile M hM q)
        (MCS.jointProfileVertical M hM q) =
      SCRB.simpleCycleDerivativeContinuation M hM q := by
  rw [profileSimpleCycleDerivative,
    SCRB.simpleCycleDerivativeContinuation,
    MCS.cycleResolventDerivative,
    SCRB.lengthOneCorrection, SCRB.lengthTwoCorrection]
  change (1 / 2 : ℂ) * operatorCyclePairing M
      (Ring.inverse (1 - MPR.pathOperator M hM q) - 1 -
        MPR.pathOperator M hM q) (MCS.jointProfileVertical M hM q) =
    (1 / 2 : ℂ) *
      (operatorCyclePairing M
          (Ring.inverse (1 - MPR.pathOperator M hM q))
          (MCS.jointProfileVertical M hM q) -
        operatorCyclePairing M 1 (MCS.jointProfileVertical M hM q) -
        operatorCyclePairing M (MPR.pathOperator M hM q)
          (MCS.jointProfileVertical M hM q))
  congr 1
  simp only [← operatorCyclePairingCLM_apply, map_sub, sub_apply]

end PerronWright.JointSimpleCycleEGF
