import PerronWright.Enumeration.ProfileSimpleCycleFrechet
import PerronWright.Analysis.FiniteIrreducibleJointSimpleCycleEGF

/-! # Genuine finite profile simple-cycle Fréchet derivative

The finite-term maps are the literal data-only cycle polynomials. Normal
convergence and the actual finite Neumann inverse give the derivative of
their full sum; no unproved differentiability or continuation is assumed.
-/

open MeasureTheory PerronWright
open scoped Topology
noncomputable section

namespace PerronWright.FiniteIrreducibleProfileSimpleCycleFrechet

open PerronWright.ProfileSimpleCycleFrechet

namespace JS
export PerronWright.JointSimpleCycleEGF
  (operatorCyclePairing profileSimpleCycleTerm profileSimpleCycleSeries
   profileSimpleCycleTerm_hasDerivAt profileSimpleCycleDerivative)
export PerronWright.FiniteIrreducibleJointSimpleCycleEGF
  (norm_profileSimpleCycleTerm_deriv_le profileCycleDerivativeTail_eq_resolvent)
end JS

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
private theorem perronFunction_uniform_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ M.continuousPerronFunction hM x := by
  obtain ⟨m, hm, hmu⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  exact ⟨m, hm, fun x => hmu x (Set.mem_univ x)⟩

/-- The existing scalar directional majorant controls the operator norm of
the finite-term Fréchet derivative. -/
theorem norm_profileSimpleCycleTermFDeriv_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (htau : ∀ x, ‖tau x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x)
    (n : ℕ) :
    ‖profileSimpleCycleTermFDeriv M.bjrModel tau n‖ ≤
      ((1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
        ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
        (‖M.continuousPerronFunction hM‖ / m) * q ^ 2) * q ^ n := by
  let D : ℝ := (1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * q ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDqn : 0 ≤ D * q ^ n := mul_nonneg hD (pow_nonneg hq n)
  apply ContinuousLinearMap.opNorm_le_bound _ hDqn
  intro v
  rw [profileSimpleCycleTermFDeriv_apply]
  have hbound := JS.norm_profileSimpleCycleTerm_deriv_le M hM
    tau v q m ‖v‖ hq htau hm hmu le_rfl n
  dsimp only [D]
  simpa only [FiniteIrreducibleJointSimpleCycleEGF.pathOperatorParameterCLM_eq_bjr,
    mul_assoc, mul_left_comm, mul_comm] using hbound

private theorem summable_profileSimpleCycleTermFDeriv
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (htau : ∀ x, ‖tau x‖ ≤ q) :
    Summable (fun n : ℕ => profileSimpleCycleTermFDeriv M.bjrModel tau n) := by
  obtain ⟨m, hm, hmu⟩ := perronFunction_uniform_pos M hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * q ^ 2
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
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau v : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (htau : ∀ x, ‖tau x‖ ≤ q) :
    profileSimpleCycleDerivativeCLM M.bjrModel tau v =
      JS.profileSimpleCycleDerivative M.bjrModel tau v := by
  have hs : Summable (fun n : ℕ =>
      profileSimpleCycleTermFDeriv M.bjrModel tau n) :=
    summable_profileSimpleCycleTermFDeriv M hM tau q hq hq1 htau
  rw [profileSimpleCycleDerivativeCLM]
  change (ContinuousLinearMap.apply ℂ ℂ v)
      (∑' n : ℕ, profileSimpleCycleTermFDeriv M.bjrModel tau n) = _
  rw [(ContinuousLinearMap.apply ℂ ℂ v).map_tsum hs]
  calc
    (∑' n : ℕ, profileSimpleCycleTermFDeriv M.bjrModel tau n v) =
        ∑' n : ℕ, (1 / 2 : ℂ) * JS.operatorCyclePairing M.bjrModel
          ((MarkedPathResolvent.pathOperatorParameterCLM M.bjrModel tau) ^ (n + 2)) v := by
      apply tsum_congr
      intro n
      exact profileSimpleCycleTermFDeriv_apply M.bjrModel tau v n
    _ = (1 / 2 : ℂ) * ∑' n : ℕ, JS.operatorCyclePairing M.bjrModel
          ((MarkedPathResolvent.pathOperatorParameterCLM M.bjrModel tau) ^ (n + 2)) v := by
      rw [tsum_mul_left]
    _ = JS.profileSimpleCycleDerivative M.bjrModel tau v := by
      rw [JointSimpleCycleEGF.profileSimpleCycleDerivative]
      congr 1
      exact JS.profileCycleDerivativeTail_eq_resolvent
        M hM tau v q hq hq1 htau

/-- Normal convergence on every strict profile ball gives the full
Fréchet derivative there. -/
theorem profileSimpleCycleSeries_hasFDerivAt_of_uniform_subcritical
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (tau : C(S, ℂ)) (htau : ‖tau‖ < q) :
    HasFDerivAt (JS.profileSimpleCycleSeries M.bjrModel)
      (profileSimpleCycleDerivativeCLM M.bjrModel tau) tau := by
  obtain ⟨m, hm, hmu⟩ := perronFunction_uniform_pos M hM
  let D : ℝ := (1 / 2 : ℝ) * ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m) * q ^ 2
  let u : ℕ → ℝ := fun n => D * q ^ n
  have hu : Summable u :=
    (summable_geometric_of_lt_one hq.le hq1).mul_left D
  let U : Set C(S, ℂ) := Metric.ball 0 q
  have hterm : ∀ n sigma, sigma ∈ U →
      HasFDerivAt (fun a : C(S, ℂ) => JS.profileSimpleCycleTerm M.bjrModel a n)
        (profileSimpleCycleTermFDeriv M.bjrModel sigma n) sigma := by
    intro n sigma hsigma
    exact profileSimpleCycleTerm_hasFDerivAt M.bjrModel sigma n
  have hbound : ∀ n sigma, sigma ∈ U →
      ‖profileSimpleCycleTermFDeriv M.bjrModel sigma n‖ ≤ u n := by
    intro n sigma hsigma
    have hsigmaNorm : ‖sigma‖ < q := by
      simpa only [U, Metric.mem_ball, dist_zero_right] using hsigma
    exact norm_profileSimpleCycleTermFDeriv_le M hM sigma q m hq.le
      (fun x => (sigma.norm_coe_le_norm x).trans hsigmaNorm.le)
      hm hmu n
  have hzero : Summable (fun n : ℕ =>
      JS.profileSimpleCycleTerm M.bjrModel (0 : C(S, ℂ)) n) := by
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
      ∑' n : ℕ, JS.profileSimpleCycleTerm M.bjrModel sigma n)
    (∑' n : ℕ, profileSimpleCycleTermFDeriv M.bjrModel tau n) tau
  exact hsum

/-- Pointwise form on the whole open unit profile ball. -/
theorem profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (htau : ‖tau‖ < 1) :
    HasFDerivAt (JS.profileSimpleCycleSeries M.bjrModel)
      (profileSimpleCycleDerivativeCLM M.bjrModel tau) tau := by
  let q : ℝ := (‖tau‖ + 1) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have htauq : ‖tau‖ < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  exact profileSimpleCycleSeries_hasFDerivAt_of_uniform_subcritical
    M hM q hq hq1 tau htauq

/-- Concrete resolvent action of the Fréchet derivative at an arbitrary
strictly subcritical profile. -/
theorem profileSimpleCycleDerivativeCLM_apply_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau v : C(S, ℂ)) (htau : ‖tau‖ < 1) :
    profileSimpleCycleDerivativeCLM M.bjrModel tau v =
      JS.profileSimpleCycleDerivative M.bjrModel tau v := by
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
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {tau : ℂ → C(S, ℂ)} {tau' : C(S, ℂ)} {z : ℂ}
    (htau : HasDerivAt tau tau' z)
    (hsub : ‖tau z‖ < 1) :
    HasDerivAt (fun w => JS.profileSimpleCycleSeries M.bjrModel (tau w))
      (JS.profileSimpleCycleDerivative M.bjrModel (tau z) tau') z := by
  have hcomp := (profileSimpleCycleSeries_hasFDerivAt_of_norm_lt_one
    M hM (tau z) hsub).comp_hasDerivAt z htau
  exact hcomp.congr_deriv
    (profileSimpleCycleDerivativeCLM_apply_of_norm_lt_one
      M hM (tau z) tau' hsub)

/-- The direct profile simple-cycle series is complex Fréchet differentiable,
hence Banach-holomorphic, throughout the open unit profile ball. -/
theorem profileSimpleCycleSeries_differentiableOn_unitBall
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    DifferentiableOn ℂ (JS.profileSimpleCycleSeries M.bjrModel)
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
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {tau : ℂ → C(S, ℂ)} {z : ℂ}
    (htau : AnalyticAt ℂ tau z) (hsub : ‖tau z‖ < 1) :
    AnalyticAt ℂ (fun w => JS.profileSimpleCycleSeries M.bjrModel (tau w)) z := by
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


end PerronWright.FiniteIrreducibleProfileSimpleCycleFrechet
