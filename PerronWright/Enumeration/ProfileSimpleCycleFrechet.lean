import PerronWright.Enumeration.JointSimpleCycleEGF
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Fréchet holomorphy of the profile simple-cycle series

This module upgrades the existing one-variable normal-convergence argument
to the profile Banach space itself.  The finite-cycle derivative is identified
from the already proved cyclicity formula, and the derivative series is summed
with the already proved Perron-gauge majorant.  The final statement is complex
Fréchet differentiability on the open unit profile ball, i.e. holomorphy in the
Banach-calculus sense.
-/

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.ProfileSimpleCycleFrechet

namespace JS

export PerronWright.JointSimpleCycleEGF
  (operatorCyclePairing profileSimpleCycleTerm profileSimpleCycleSeries
   profileSimpleCycleTerm_hasDerivAt norm_profileSimpleCycleTerm_deriv_le
   profileCycleDerivativeTail_eq_resolvent profileSimpleCycleDerivative)

end JS

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Each finite simple-cycle term is an entire polynomial on the profile
Banach space. -/
theorem profileSimpleCycleTerm_differentiableAt
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (n : ℕ) :
    DifferentiableAt ℂ (fun sigma : C(S, ℂ) =>
      JS.profileSimpleCycleTerm M sigma n) tau := by
  unfold JointSimpleCycleEGF.profileSimpleCycleTerm
    JointSimpleCycleEGF.profileCycleTrace
    JointSimpleCycleEGF.operatorCyclePairing
  fun_prop

/-- The actual Fréchet derivative of one finite simple-cycle term. -/
def profileSimpleCycleTermFDeriv
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (n : ℕ) :
    C(S, ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (fun sigma : C(S, ℂ) =>
    JS.profileSimpleCycleTerm M sigma n) tau

theorem profileSimpleCycleTerm_hasFDerivAt
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (n : ℕ) :
    HasFDerivAt (fun sigma : C(S, ℂ) =>
      JS.profileSimpleCycleTerm M sigma n)
      (profileSimpleCycleTermFDeriv M tau n) tau := by
  exact (profileSimpleCycleTerm_differentiableAt M tau n).hasFDerivAt

/-- Applying the finite-term Fréchet derivative recovers exactly the
cyclically rotated directional derivative proved in
`JointSimpleCycleEGF`. -/
theorem profileSimpleCycleTermFDeriv_apply
    (M : CompactBJRModel S) (tau v : C(S, ℂ)) (n : ℕ) :
    profileSimpleCycleTermFDeriv M tau n v =
      (1 / 2 : ℂ) * JS.operatorCyclePairing M
        ((MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ (n + 2)) v := by
  let line : ℂ → C(S, ℂ) :=
    (fun _ => tau) + fun z => z • v
  have hline : HasDerivAt line v 0 := by
    simpa only [line, zero_add, one_smul] using
      (hasDerivAt_const (0 : ℂ) tau).add
        ((hasDerivAt_id' (0 : ℂ)).smul_const v)
  have hline0 : line 0 = tau := by
    simp [line]
  have houter : HasFDerivAt
      (fun sigma : C(S, ℂ) => JS.profileSimpleCycleTerm M sigma n)
      (profileSimpleCycleTermFDeriv M tau n) (line 0) := by
    simpa only [hline0] using
      profileSimpleCycleTerm_hasFDerivAt M tau n
  have hchain : HasDerivAt
      (fun z : ℂ => JS.profileSimpleCycleTerm M (line z) n)
      (profileSimpleCycleTermFDeriv M tau n v) 0 := by
    simpa only [Function.comp_def] using houter.comp_hasDerivAt 0 hline
  have hcycle : HasDerivAt
      (fun z : ℂ => JS.profileSimpleCycleTerm M (line z) n)
      ((1 / 2 : ℂ) * JS.operatorCyclePairing M
        ((MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ (n + 2)) v) 0 := by
    simpa only [hline0] using
      JS.profileSimpleCycleTerm_hasDerivAt M hline n
  exact hchain.unique hcycle

/-- The existing scalar directional majorant controls the operator norm of
the finite-term Fréchet derivative. -/
theorem norm_profileSimpleCycleTermFDeriv_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (htau : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x)
    (n : ℕ) :
    ‖profileSimpleCycleTermFDeriv M tau n‖ ≤
      ((1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
        ‖M.kernel.complexActionCLM M.mu‖ *
        (‖M.perronFunction hM‖ / m) * q ^ 2) * q ^ n := by
  let D : ℝ := (1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * q ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDqn : 0 ≤ D * q ^ n := mul_nonneg hD (pow_nonneg hq n)
  apply ContinuousLinearMap.opNorm_le_bound _ hDqn
  intro v
  rw [profileSimpleCycleTermFDeriv_apply]
  have hbound := JS.norm_profileSimpleCycleTerm_deriv_le M hM
    tau v q m ‖v‖ hq htau hm hmu le_rfl n
  dsimp only [D]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The Fréchet derivative of the full series, first defined by normally
summing the derivatives of its finite-cycle terms. -/
def profileSimpleCycleDerivativeCLM
    (M : CompactBJRModel S) (tau : C(S, ℂ)) : C(S, ℂ) →L[ℂ] ℂ :=
  ∑' n : ℕ, profileSimpleCycleTermFDeriv M tau n

private theorem summable_profileSimpleCycleTermFDeriv
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (htau : ∀ x, ‖tau x‖ ≤ q) :
    Summable (fun n : ℕ => profileSimpleCycleTermFDeriv M tau n) := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * q ^ 2
  have hgeom : Summable (fun n : ℕ => D * q ^ n) :=
    (summable_geometric_of_lt_one hq hq1).mul_left D
  apply Summable.of_norm_bounded hgeom
  intro n
  exact norm_profileSimpleCycleTermFDeriv_le
    M hM tau q m hq htau hm hmu n

/-- On a strict profile ball, the summed Fréchet derivative acts by the
same concrete resolvent expression already used by the singular
continuation. -/
theorem profileSimpleCycleDerivativeCLM_apply_of_uniform_subcritical
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau v : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (htau : ∀ x, ‖tau x‖ ≤ q) :
    profileSimpleCycleDerivativeCLM M tau v =
      JS.profileSimpleCycleDerivative M tau v := by
  have hs : Summable (fun n : ℕ =>
      profileSimpleCycleTermFDeriv M tau n) :=
    summable_profileSimpleCycleTermFDeriv M hM tau q hq hq1 htau
  rw [profileSimpleCycleDerivativeCLM]
  change (ContinuousLinearMap.apply ℂ ℂ v)
      (∑' n : ℕ, profileSimpleCycleTermFDeriv M tau n) = _
  rw [(ContinuousLinearMap.apply ℂ ℂ v).map_tsum hs]
  calc
    (∑' n : ℕ, profileSimpleCycleTermFDeriv M tau n v) =
        ∑' n : ℕ, (1 / 2 : ℂ) * JS.operatorCyclePairing M
          ((MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ (n + 2)) v := by
      apply tsum_congr
      intro n
      exact profileSimpleCycleTermFDeriv_apply M tau v n
    _ = (1 / 2 : ℂ) * ∑' n : ℕ, JS.operatorCyclePairing M
          ((MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ (n + 2)) v := by
      rw [tsum_mul_left]
    _ = JS.profileSimpleCycleDerivative M tau v := by
      rw [JointSimpleCycleEGF.profileSimpleCycleDerivative]
      congr 1
      exact JS.profileCycleDerivativeTail_eq_resolvent
        M hM tau v q hq hq1 htau

/-- Normal convergence on every strict profile ball gives the full
Fréchet derivative there. -/
theorem profileSimpleCycleSeries_hasFDerivAt_of_uniform_subcritical
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (tau : C(S, ℂ)) (htau : ‖tau‖ < q) :
    HasFDerivAt (JS.profileSimpleCycleSeries M)
      (profileSimpleCycleDerivativeCLM M tau) tau := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.kernel.toContinuousMap‖ *
    ‖M.kernel.complexActionCLM M.mu‖ *
    (‖M.perronFunction hM‖ / m) * q ^ 2
  let u : ℕ → ℝ := fun n => D * q ^ n
  have hu : Summable u :=
    (summable_geometric_of_lt_one hq.le hq1).mul_left D
  let U : Set C(S, ℂ) := Metric.ball 0 q
  have hterm : ∀ n sigma, sigma ∈ U →
      HasFDerivAt (fun a : C(S, ℂ) => JS.profileSimpleCycleTerm M a n)
        (profileSimpleCycleTermFDeriv M sigma n) sigma := by
    intro n sigma hsigma
    exact profileSimpleCycleTerm_hasFDerivAt M sigma n
  have hbound : ∀ n sigma, sigma ∈ U →
      ‖profileSimpleCycleTermFDeriv M sigma n‖ ≤ u n := by
    intro n sigma hsigma
    have hsigmaNorm : ‖sigma‖ < q := by
      simpa only [U, Metric.mem_ball, dist_zero_right] using hsigma
    exact norm_profileSimpleCycleTermFDeriv_le M hM sigma q m hq.le
      (fun x => (sigma.norm_coe_le_norm x).trans hsigmaNorm.le)
      hm hmu n
  have hzero : Summable (fun n : ℕ =>
      JS.profileSimpleCycleTerm M (0 : C(S, ℂ)) n) := by
    simp [JointSimpleCycleEGF.profileSimpleCycleTerm,
      JointSimpleCycleEGF.profileCycleTrace,
      JointSimpleCycleEGF.operatorCyclePairing]
  have hsum := hasFDerivAt_tsum_of_isPreconnected hu
    Metric.isOpen_ball (convex_ball (0 : C(S, ℂ)) q).isPreconnected
    hterm hbound (Metric.mem_ball_self hq) hzero
    (show tau ∈ U by
      simpa only [U, Metric.mem_ball, dist_zero_right] using htau)
  change HasFDerivAt
    (fun sigma : C(S, ℂ) =>
      ∑' n : ℕ, JS.profileSimpleCycleTerm M sigma n)
    (∑' n : ℕ, profileSimpleCycleTermFDeriv M tau n) tau
  exact hsum

/-- Pointwise form on the whole open unit profile ball. -/
theorem profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (htau : ‖tau‖ < 1) :
    HasFDerivAt (JS.profileSimpleCycleSeries M)
      (profileSimpleCycleDerivativeCLM M tau) tau := by
  let q : ℝ := (‖tau‖ + 1) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have htauq : ‖tau‖ < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  exact profileSimpleCycleSeries_hasFDerivAt_of_uniform_subcritical
    M hM q hq hq1 tau htauq

/-- Concrete resolvent action of the Fréchet derivative at an arbitrary
strictly subcritical profile. -/
theorem profileSimpleCycleDerivativeCLM_apply_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau v : C(S, ℂ)) (htau : ‖tau‖ < 1) :
    profileSimpleCycleDerivativeCLM M tau v =
      JS.profileSimpleCycleDerivative M tau v := by
  let q : ℝ := (‖tau‖ + 1) / 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have htauq : ‖tau‖ < q := by dsimp [q]; linarith
  exact profileSimpleCycleDerivativeCLM_apply_of_uniform_subcritical
    M hM tau v q hq hq1
      (fun x => (tau.norm_coe_le_norm x).trans htauq.le)

/-- Chain rule along one complex parameter, with the derivative written in
the concrete resolvent form used by the fold singularity calculation. -/
theorem profileSimpleCycleSeries_comp_hasDerivAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {tau : ℂ → C(S, ℂ)} {tau' : C(S, ℂ)} {z : ℂ}
    (htau : HasDerivAt tau tau' z)
    (hsub : ‖tau z‖ < 1) :
    HasDerivAt (fun w => JS.profileSimpleCycleSeries M (tau w))
      (JS.profileSimpleCycleDerivative M (tau z) tau') z := by
  have hcomp := (profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
    M hM (tau z) hsub).comp_hasDerivAt z htau
  exact hcomp.congr_deriv
    (profileSimpleCycleDerivativeCLM_apply_of_norm_lt_one
      M hM (tau z) tau' hsub)

/-- The direct profile simple-cycle series is complex Fréchet differentiable,
hence Banach-holomorphic, throughout the open unit profile ball. -/
theorem profileSimpleCycleSeries_differentiableOn_unitBall
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    DifferentiableOn ℂ (JS.profileSimpleCycleSeries M)
      (Metric.ball (0 : C(S, ℂ)) 1) := by
  intro tau htau
  have htauNorm : ‖tau‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using htau
  exact (profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
    M hM tau htauNorm).differentiableAt.differentiableWithinAt

/-- Although mathlib does not automatically turn Fréchet differentiability
on an infinite-dimensional complex Banach space into its power-series
predicate, restriction along any scalar analytic profile curve is analytic
as soon as the curve lies strictly inside the unit profile ball at the base
point. -/
theorem profileSimpleCycleSeries_comp_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {tau : ℂ → C(S, ℂ)} {z : ℂ}
    (htau : AnalyticAt ℂ tau z) (hsub : ‖tau z‖ < 1) :
    AnalyticAt ℂ (fun w => JS.profileSimpleCycleSeries M (tau w)) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hmem : tau z ∈ Metric.ball (0 : C(S, ℂ)) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hsub
  have hball : ∀ᶠ w in 𝓝 z, tau w ∈ Metric.ball (0 : C(S, ℂ)) 1 :=
    htau.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  filter_upwards [htau.eventually_analyticAt, hball] with w htw hw
  have hnorm : ‖tau w‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  simpa only [Function.comp_def] using
    (profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
      M hM (tau w) hnorm).differentiableAt.comp w htw.differentiableAt

end PerronWright.ProfileSimpleCycleFrechet
