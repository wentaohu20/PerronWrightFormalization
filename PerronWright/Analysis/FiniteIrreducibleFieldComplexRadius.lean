import PerronWright.Analysis.FiniteIrreducibleNormalizedDeltaProfile
import PerronWright.Analysis.FiniteIrreducibleFieldSeriesNormalization
import PerronWright.Analysis.FiniteIrreducibleSeriesScaling
import PerronWright.Enumeration.FieldRootedTreeAnalyticGerm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The complex-field radius of the literal finite irreducible tree series

This file identifies the convergence radius of the genuine field-weighted
labelled rooted-tree series with the analytic critical radius.  The proof is
deliberately separated into three pieces.

* `FiniteIrreducibleFieldRootedTree.fms` is the one-variable formal multilinear series of the
  literal finite-tree coefficients.
* `FiniteIrreducibleFieldRootedTree.normalizedFMS` pulls the activity back by the analytic
  critical radius.  The terminal Cartesian-Delta profile supplies an analytic
  representative of this Taylor series on the open unit disc.
* A nonzero square-root derivative at the fold prevents this normalized
  series from extending analytically across `w = 1`.  Hence its radius is
  exactly one, and undoing the scalar change of variables gives the physical
  critical radius.

No convergence-radius or least-fixed-point statement is assumed here.
-/

open Filter Topology
open scoped Classical Topology ENNReal NNReal ComplexOrder

noncomputable section

namespace PerronWright

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

namespace FiniteIrreducibleFieldRootedTree

/-- The one-variable formal multilinear series of the genuine finite
field-weighted rooted-tree coefficients. -/
def fms (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
  oneDimensionalFormalMultilinearSeries (FieldRootedTree.series M.bjrModel g)

/-- This is definitionally the already constructed literal field series,
not a replacement coefficient family. -/
theorem fms_eq_fieldFMS (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) :
    fms M g = M.fieldFMS g := rfl

@[simp] theorem oneDimensionalPowerSeries_fms
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) :
    oneDimensionalPowerSeries (fms M g) = FieldRootedTree.series M.bjrModel g := by
  exact oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries _

/-- The same genuine tree series in the normalized activity coordinate
`z = rho(g) * w`. -/
def normalizedFMS (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
  (fms M g).compContinuousLinearMap
    ((FiniteIrreducibleRadiusResponse.radius M hM g) • ContinuousLinearMap.id ℂ ℂ)

private theorem fms_eq_of_oneDimensionalPowerSeries_eq
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ))
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : oneDimensionalPowerSeries p = FieldRootedTree.series M.bjrModel g) :
    p = fms M g := by
  calc
    p = oneDimensionalFormalMultilinearSeries
        (oneDimensionalPowerSeries p) :=
      (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries p).symm
    _ = fms M g := by rw [hp]; rfl

/-- An analytic function on the unit disc whose germ has Taylor series `p`
forces radius at least one. -/
private theorem one_le_radius_of_analyticOn_unitBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1))
    (hp : HasFPowerSeriesAt F p 0) :
    (1 : ℝ≥0∞) ≤ p.radius := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro R hR hR1
  have hRreal : (R : ℝ) < 1 := by
    exact_mod_cast hR1
  have hdiff : DifferentiableOn ℂ F (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    have hzUnit : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      have hzR : ‖z‖ ≤ (R : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      exact hzR.trans_lt hRreal
    exact (hF z hzUnit).differentiableAt.differentiableWithinAt
  obtain ⟨r, hpBall⟩ := hp
  exact (hpBall.exchange_radius
    (hdiff.hasFPowerSeriesOnBall hR)).r_le

/-- Abstract square-root obstruction.  If the Taylor sum agrees inside the
unit disc with one side of a holomorphic fold whose first `X`-derivative is
nonzero, then the Taylor radius cannot exceed one. -/
private theorem radius_eq_one_of_squareRoot_obstruction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F H : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E}
    (hF : AnalyticOnNhd ℂ F (Metric.ball 0 1))
    (hp : HasFPowerSeriesAt F p 0)
    (hH : AnalyticAt ℂ H 0)
    (hHderiv : deriv H 0 ≠ 0)
    (hmatch : ∃ᶠ X : ℂ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      1 - X ^ 2 ∈ Metric.ball (0 : ℂ) 1 ∧ F (1 - X ^ 2) = H X) :
    p.radius = 1 := by
  apply le_antisymm ?_ (one_le_radius_of_analyticOn_unitBall hF hp)
  by_contra hle
  have hRadius : (1 : ℝ≥0∞) < p.radius := lt_of_not_ge hle
  have hRadiusPos : 0 < p.radius := zero_lt_one.trans hRadius
  have hOne : (1 : ℂ) ∈ Metric.eball 0 p.radius := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
      norm_one, ENNReal.ofReal_one] using hRadius
  have hsumAtOne : AnalyticAt ℂ p.sum 1 := p.analyticOnNhd 1 hOne
  have hsumOnUnit : AnalyticOnNhd ℂ p.sum (Metric.ball 0 1) := by
    intro z hz
    apply p.analyticOnNhd z
    have hz1 : ‖z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hz1e : ENNReal.ofReal ‖z‖ < 1 := by
      exact ENNReal.ofReal_lt_one.mpr hz1
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right] using
      hz1e.trans hRadius
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hRadiusPos).hasFPowerSeriesAt
  have hsumEqFNear : p.sum =ᶠ[nhds (0 : ℂ)] F := by
    filter_upwards [hpSum.eventually_hasSum_sub,
      hp.eventually_hasSum_sub] with z hzSum hzF
    exact hzSum.unique hzF
  have hsumEqF : Set.EqOn p.sum F (Metric.ball (0 : ℂ) 1) :=
    hsumOnUnit.eqOn_of_preconnected_of_eventuallyEq hF
      (convex_ball (0 : ℂ) 1).isPreconnected
      (Metric.mem_ball_self (by norm_num)) hsumEqFNear
  let A : ℂ → E := fun X ↦ p.sum (1 - X ^ 2)
  have hinner : HasDerivAt (fun X : ℂ ↦ 1 - X ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℂ)).const_sub (1 : ℂ))
  have hA : AnalyticAt ℂ A 0 := by
    exact hsumAtOne.comp_of_eq
      ((analyticAt_const.sub (analyticAt_id.pow 2))) (by norm_num)
  have hAderiv : deriv A 0 = 0 := by
    have houter : HasFDerivAt p.sum (fderiv ℂ p.sum 1) 1 :=
      hsumAtOne.differentiableAt.hasFDerivAt
    have hcomp : HasDerivAt
        (p.sum ∘ fun X : ℂ ↦ 1 - X ^ 2)
        ((fderiv ℂ p.sum 1) 0) 0 :=
      houter.comp_hasDerivAt_of_eq 0 hinner (by norm_num)
    change deriv (p.sum ∘ fun X : ℂ ↦ 1 - X ^ 2) 0 = 0
    simpa only [map_zero] using hcomp.deriv
  have hfreq : ∃ᶠ X : ℂ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      A X = H X := by
    exact hmatch.mono fun X hX ↦ by
      dsimp only [A]
      exact (hsumEqF hX.1).trans hX.2
  have heq : A =ᶠ[nhds (0 : ℂ)] H :=
    (hA.frequently_eq_iff_eventually_eq hH).mp hfreq
  have hderivEq : deriv A 0 = deriv H 0 := heq.deriv_eq
  exact hHderiv (hderivEq.symm.trans hAderiv)

/-- The Taylor series of a normalized Cartesian-Delta tree profile is the
literal field-rooted-tree series with its activity rescaled by `rho(g)`.
The proof uses only the residual equation near activity zero and formal
uniqueness of the labelled-tree solution. -/
theorem normalizedFMS_hasFPowerSeriesAt_of_cartesianDelta_profile
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta s : ℝ} {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (heta : 0 < eta) (_hs : 0 < s)
    (hTheta : AnalyticOnNhd ℂ Theta
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s))
    (hData : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M.bjrModel
          (FiniteIrreducibleNormalizedFoldActivity.activityMap M hM q, Theta q) = 0)
    {g : C(S, ℂ)} (hg : g ∈ Metric.ball 0 s) :
    HasFPowerSeriesAt (fun w : ℂ ↦ Theta (w, g))
      (normalizedFMS M hM g) 0 := by
  let rho : ℂ := FiniteIrreducibleRadiusResponse.radius M hM g
  have hzeroUnit : (0 : ℂ) ∈ Metric.ball 0 1 :=
    Metric.mem_ball_self (by norm_num)
  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta 0 :=
    Transfer.unit_ball_subset_cartesianDelta heta hzeroUnit
  have hq0 : ((0 : ℂ), g) ∈
      Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s := ⟨hzeroDelta, hg⟩
  have hrho : rho ≠ 0 := (hData (0, g) hq0).1
  let psi : ℂ × C(S, ℂ) → C(S, ℂ) :=
    fun q ↦ Theta (q.1 / rho, g)
  have hinput : AnalyticAt ℂ
      (fun q : ℂ × C(S, ℂ) ↦ (q.1 / rho, g)) (0, g) := by
    exact analyticAt_fst.div_const.prod analyticAt_const
  have hinput0 : ((0 : ℂ) / rho, g) = (0, g) := by
    simp only [zero_div]
  have hpsi : AnalyticAt ℂ psi (0, g) := by
    exact (hTheta (0, g) hq0).comp_of_eq hinput hinput0
  have hpsi0 : psi (0, g) = 0 := by
    have hres0 := (hData (0, g) hq0).2
    change Theta (0, g) - (rho * 0) •
      NormedSpace.exp
        (g - TreeCritical.degree M.bjrModel +
          M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (Theta (0, g))) = 0 at hres0
    simpa only [mul_zero, zero_smul, sub_zero, psi, zero_div] using hres0
  have hopen : IsOpen
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) :=
    (Transfer.isOpen_cartesianDelta eta 0).prod Metric.isOpen_ball
  have hmapTend : Tendsto (fun z : ℂ ↦ (z / rho, g))
      (nhds 0) (nhds (0, g)) := by
    have ha : ContinuousAt (fun z : ℂ ↦ z / rho) 0 :=
      continuousAt_id.div_const rho
    simpa only [zero_div] using ha.tendsto.prodMk_nhds tendsto_const_nhds
  have hres : ∀ᶠ z : ℂ in nhds 0,
      TreeCritical.residual M.bjrModel ((z, g), psi (z, g)) = 0 := by
    filter_upwards [hmapTend.eventually (hopen.mem_nhds hq0)] with z hz
    have hzres := (hData (z / rho, g) hz).2
    change TreeCritical.residual M.bjrModel
      ((rho * (z / rho), g), Theta (z / rho, g)) = 0 at hzres
    have hmul : rho * (z / rho) = z := by
      rw [div_eq_mul_inv]
      calc
        rho * (z * rho⁻¹) = z * (rho * rho⁻¹) := by ring
        _ = z := by rw [mul_inv_cancel₀ hrho, mul_one]
    rw [hmul] at hzres
    exact hzres
  obtain ⟨p, hp, -, hpSeries⟩ :=
    FieldRootedTree.branch_taylorSeries_eq_series M.bjrModel g psi hpsi hpsi0 hres
  have hpEq : p = fms M g := fms_eq_of_oneDimensionalPowerSeries_eq M g hpSeries
  let u : ℂ →L[ℂ] ℂ := rho • ContinuousLinearMap.id ℂ ℂ
  have hpAtUZero : HasFPowerSeriesAt (fun z : ℂ ↦ psi (z, g)) p (u 0) := by
    simpa only [u, smul_apply,
      ContinuousLinearMap.id_apply, smul_zero] using hp
  have hpComp := hpAtUZero.compContinuousLinearMap (u := u) (x := (0 : ℂ))
  have hfun : (fun z : ℂ ↦ psi (z, g)) ∘ u =
      (fun w : ℂ ↦ Theta (w, g)) := by
    funext w
    simp only [Function.comp_apply, u, psi, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    have hcancel : rho * w / rho = w := by
      rw [mul_comm rho w, mul_div_cancel_right₀ w hrho]
    rw [hcancel]
  rw [hfun, hpEq] at hpComp
  simpa only [normalizedFMS, u, rho] using hpComp

/-! ## The fold obstruction and exact rescaling -/

/-- The derivative of the joint fold profile in its fold coordinate.  It is
packaged as an analytic function of the field so that nonvanishing at the
zero field persists on one genuine complex field ball. -/
private def foldVerticalDerivative (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) : C(S, ℂ) :=
  (fderiv ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0)) (0, 1)

private theorem foldVerticalDerivative_analyticAt
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (foldVerticalDerivative M hM) 0 := by
  have hdf : AnalyticAt ℂ
      (fderiv ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM)) (0, 0) :=
    (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM).fderiv
  have hline : AnalyticAt ℂ
      (fun g : C(S, ℂ) ↦ (g, (0 : ℂ))) 0 :=
    analyticAt_id.prod analyticAt_const
  have hcomp : AnalyticAt ℂ
      (fun g : C(S, ℂ) ↦
        fderiv ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0)) 0 :=
    hdf.comp_of_eq hline rfl
  let ev : ((C(S, ℂ) × ℂ) →L[ℂ] C(S, ℂ)) →L[ℂ] C(S, ℂ) :=
    ContinuousLinearMap.apply ℂ C(S, ℂ) (0, 1)
  exact (ev.analyticAt
    (fderiv ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (0, 0))).comp_of_eq
      hcomp rfl

private theorem foldVerticalDerivative_eq_slice_deriv
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {g : C(S, ℂ)}
    (hg : AnalyticAt ℂ
      (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0)) :
    foldVerticalDerivative M hM g =
      deriv (fun X : ℂ ↦
        FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X)) 0 := by
  let line : ℂ → C(S, ℂ) × ℂ := fun X ↦ (g, X)
  have hline : HasDerivAt line (0, 1) 0 :=
    (hasDerivAt_const (x := (0 : ℂ)) g).prodMk (hasDerivAt_id (x := (0 : ℂ)))
  have hcomp := hg.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
  change HasDerivAt
    (fun X : ℂ ↦ FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X))
      ((fderiv ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0)) (0, 1)) 0
    at hcomp
  symm
  exact hcomp.deriv

private theorem foldVerticalDerivative_base_ne_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    foldVerticalDerivative M hM 0 ≠ 0 := by
  have hu : M.complexPerronFunction hM ≠ 0 := by
    intro hu
    have happ := congrArg (M.normalizedPerronFunctional hM) hu
    have : (1 : ℂ) = 0 := by
      simpa only [M.normalizedPerronFunctional_perronFunction,
        map_zero] using happ
    exact one_ne_zero this
  have hgamma : (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr
        (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne')
  rw [foldVerticalDerivative_eq_slice_deriv M hM
      (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM),
    FiniteIrreducibleNormalizedFoldActivity.foldProfile_vertical_deriv]
  exact smul_ne_zero hgamma hu

/-- Equality along an arbitrarily short positive real fold ray is frequent
at the punctured complex origin.  The additional unit-disc clause is built
in because it is exactly what the radius obstruction consumes. -/
private theorem frequently_square_substitution_eq
    {E : Type*} [NormedAddCommGroup E]
    {F H : ℂ → E} {r : ℝ} (hr : 0 < r)
    (hEq : ∀ x : ℝ, 0 < x → x < r → x < 1 →
      F (((1 - x ^ 2 : ℝ) : ℂ)) = H (x : ℂ)) :
    ∃ᶠ X : ℂ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      1 - X ^ 2 ∈ Metric.ball (0 : ℂ) 1 ∧ F (1 - X ^ 2) = H X := by
  let a : ℝ := min r 1 / 2
  have ha : 0 < a := half_pos (lt_min hr zero_lt_one)
  have har : a < r := by
    dsimp only [a]
    nlinarith [min_le_left r 1]
  have ha1 : a < 1 := by
    dsimp only [a]
    nlinarith [min_le_right r 1]
  let x : ℕ → ℝ := fun n ↦ a / ((n : ℝ) + 1)
  have hxlim : Tendsto x atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ a) atTop (nhds a) :=
      tendsto_const_nhds
    have h := (hconst.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [x, div_eq_mul_inv, one_div, one_mul, mul_zero] using h
  rw [frequently_iff_seq_forall]
  refine ⟨fun n ↦ (x n : ℂ), ?_, ?_⟩
  · rw [tendsto_nhdsWithin_iff]
    constructor
    · rw [← Complex.ofReal_zero, tendsto_ofReal_iff]
      exact hxlim
    · apply Filter.Eventually.of_forall
      intro n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (by
        dsimp only [x]
        exact div_ne_zero ha.ne' (by positivity))
  · intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdenOne : 1 ≤ (n : ℝ) + 1 := by linarith
    have hx0 : 0 < x n := by
      exact div_pos ha hden
    have hxa : x n ≤ a := by
      dsimp only [x]
      rw [div_le_iff₀ hden]
      nlinarith
    have hxr : x n < r := hxa.trans_lt har
    have hx1 : x n < 1 := hxa.trans_lt ha1
    have hwpos : 0 < 1 - (x n) ^ 2 := by nlinarith [sq_nonneg (x n)]
    have hwlt : 1 - (x n) ^ 2 < 1 := by nlinarith [sq_pos_of_pos hx0]
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      have hcast : (1 : ℂ) - (x n : ℂ) ^ 2 =
          ((1 - (x n) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
      exact hwlt
    · simpa only [← Complex.ofReal_one, ← Complex.ofReal_pow,
        ← Complex.ofReal_sub] using hEq (x n) hx0 hxr hx1

/-- The norm of a nonzero scalar activity change is the only change in the
convergence radius.  This is the exact (not merely one-sided) version of
`div_le_radius_compContinuousLinearMap` in one complex dimension. -/
private theorem radius_comp_smul_id_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ ℂ E) {rho : ℂ} (hrho : rho ≠ 0) :
    (p.compContinuousLinearMap
      (rho • ContinuousLinearMap.id ℂ ℂ)).radius =
        p.radius / ‖rho‖ₑ := by
  let u : ℂ ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 rho hrho)
  have hu : u.toContinuousLinearMap =
      rho • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [u, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm z rho
  have huinv : u.symm.toContinuousLinearMap =
      rho⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [u, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm z rho⁻¹
  have hid : ‖ContinuousLinearMap.id ℂ ℂ‖ₑ = 1 := by
    rw [enorm_eq_nnnorm]
    norm_num
  apply le_antisymm
  · rw [← hu]
    calc
      (p.compContinuousLinearMap u.toContinuousLinearMap).radius ≤
          ‖u.symm.toContinuousLinearMap‖ₑ * p.radius :=
        p.radius_compContinuousLinearMap_le u
      _ = p.radius / ‖rho‖ₑ := by
        rw [huinv]
        rw [enorm_smul, hid, mul_one]
        rw [enorm_inv hrho]
        simp only [ENNReal.div_eq_inv_mul]
  · have hlower := p.div_le_radius_compContinuousLinearMap
      (rho • ContinuousLinearMap.id ℂ ℂ)
    rw [enorm_smul, hid, mul_one] at hlower
    exact hlower

/-- Exact radius scaling between the genuine rooted-tree series and its
normalized activity pullback. -/
theorem normalizedFMS_radius_eq_scaled_fms_radius
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {g : C(S, ℂ)}
    (hrho : FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0) :
    (normalizedFMS M hM g).radius =
      (fms M g).radius / ‖FiniteIrreducibleRadiusResponse.radius M hM g‖ₑ := by
  exact radius_comp_smul_id_eq (fms M g) hrho

/-- Undoing the normalized activity change after identifying its radius with
one gives the exact physical convergence radius. -/
theorem fms_radius_eq_of_normalized_radius_eq_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {g : C(S, ℂ)}
    (hrho : FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0)
    (hnormalized : (normalizedFMS M hM g).radius = 1) :
    (fms M g).radius = ‖FiniteIrreducibleRadiusResponse.radius M hM g‖ₑ := by
  have hscale := normalizedFMS_radius_eq_scaled_fms_radius M hM hrho
  rw [hnormalized] at hscale
  exact (ENNReal.div_eq_one_iff
    (enorm_ne_zero.mpr hrho) enorm_ne_top).mp hscale.symm

/-- The terminal Cartesian-Delta profile has normalized Taylor radius one
uniformly on one complex field ball.  The upper bound is forced by the
nonzero first fold-coordinate derivative; no convergence-radius hypothesis
is included in the terminal interface. -/
theorem normalizedFMS_radius_eq_one_eventually
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) epsilon,
        (normalizedFMS M hM g).radius = 1 := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, -, hTheta,
      hData, hThetaFold, -⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  have hline : ContinuousAt
      (fun g : C(S, ℂ) ↦ (g, (0 : ℂ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hfoldAnalytic : ∀ᶠ g : C(S, ℂ) in nhds 0,
      AnalyticAt ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0) :=
    hline.tendsto.eventually
      (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM).eventually_analyticAt
  have hvertical : ∀ᶠ g : C(S, ℂ) in nhds 0,
      foldVerticalDerivative M hM g ≠ 0 :=
    (foldVerticalDerivative_analyticAt M hM).continuousAt.eventually_ne
      (foldVerticalDerivative_base_ne_zero M hM)
  have hsball : Metric.ball (0 : C(S, ℂ)) s ∈ nhds 0 :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)
  have hgood : ∀ᶠ g : C(S, ℂ) in nhds 0,
      AnalyticAt ℂ (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM) (g, 0) ∧
        foldVerticalDerivative M hM g ≠ 0 ∧
        g ∈ Metric.ball (0 : C(S, ℂ)) s :=
    hfoldAnalytic.and (hvertical.and hsball)
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨epsilon, hepsilon, ?_⟩
  intro g hg
  obtain ⟨hfoldg, hvertg, hgs⟩ := hball hg
  have hp : HasFPowerSeriesAt (fun w : ℂ ↦ Theta (w, g))
      (normalizedFMS M hM g) 0 :=
    normalizedFMS_hasFPowerSeriesAt_of_cartesianDelta_profile
      M hM heta hs hTheta hData hgs
  have hF : AnalyticOnNhd ℂ (fun w : ℂ ↦ Theta (w, g))
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hwDelta : w ∈ Transfer.cartesianDelta eta 0 :=
      Transfer.unit_ball_subset_cartesianDelta heta hw
    exact (hTheta (w, g) ⟨hwDelta, hgs⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hH : AnalyticAt ℂ
      (fun X : ℂ ↦
        FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X)) 0 :=
    hfoldg.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hHderiv : deriv
      (fun X : ℂ ↦
        FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X)) 0 ≠ 0 := by
    rw [← foldVerticalDerivative_eq_slice_deriv M hM hfoldg]
    exact hvertg
  have hreal : ∀ x : ℝ, 0 < x → x < r → x < 1 →
      Theta ((((1 - x ^ 2 : ℝ) : ℂ)), g) =
        FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, (x : ℂ)) := by
    intro x hx0 hxr hx1
    let w : ℂ := ((1 - x ^ 2 : ℝ) : ℂ)
    have hwpos : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
    have hwlt : 1 - x ^ 2 < 1 := by nlinarith [sq_pos_of_pos hx0]
    have hwUnit : w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp only [w]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
      exact hwlt
    have hsqrt : Transfer.cartesianDeltaSqrt w = (x : ℂ) := by
      rw [Transfer.cartesianDeltaSqrt]
      have harg : (1 : ℂ) - w = ((x ^ 2 : ℝ) : ℂ) := by
        dsimp only [w]
        push_cast
        ring
      rw [harg]
      have hnonneg : 0 ≤ (((x ^ 2 : ℝ) : ℂ)) := by
        exact_mod_cast sq_nonneg x
      rw [Complex.sqrt_of_nonneg hnonneg]
      exact_mod_cast (by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hx0] : Real.sqrt (x ^ 2) = x)
    have hwLocal : w ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r := by
      refine ⟨Transfer.unit_ball_subset_cartesianDelta (by norm_num) hwUnit, ?_⟩
      change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
      rw [hsqrt, Metric.mem_ball, dist_zero_right,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hxr
    have hpair : (w, g) ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s := ⟨hwLocal, hgs⟩
    have heq := hThetaFold hpair
    change Theta (w, g) =
      FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM
        (g, Transfer.cartesianDeltaSqrt w) at heq
    rw [hsqrt] at heq
    exact heq
  have hmatch := frequently_square_substitution_eq
    (F := fun w : ℂ ↦ Theta (w, g))
    (H := fun X : ℂ ↦
      FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (g, X)) hr hreal
  exact radius_eq_one_of_squareRoot_obstruction hF hp hH hHderiv hmatch

/-- On the same field ball, the genuine (unnormalized) rooted-tree series
has radius exactly equal to the norm of the analytic critical activity. -/
theorem fms_radius_eq_critical_radius_eventually
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) epsilon,
        (fms M g).radius = ‖FiniteIrreducibleRadiusResponse.radius M hM g‖ₑ := by
  obtain ⟨epsilonNorm, hepsilonNorm, hnormalized⟩ :=
    normalizedFMS_radius_eq_one_eventually M hM
  have hrhoEventually : ∀ᶠ g : C(S, ℂ) in nhds 0,
      FiniteIrreducibleRadiusResponse.radius M hM g ≠ 0 :=
    (FiniteIrreducibleRadiusResponse.radius_analytic M hM).continuousAt.eventually_ne (by
      rw [FiniteIrreducibleRadiusResponse.radius_base]
      exact one_ne_zero)
  obtain ⟨epsilonRho, hepsilonRho, hrhoBall⟩ :=
    Metric.mem_nhds_iff.mp hrhoEventually
  let epsilon : ℝ := min epsilonNorm epsilonRho
  have hepsilon : 0 < epsilon := lt_min hepsilonNorm hepsilonRho
  refine ⟨epsilon, hepsilon, ?_⟩
  intro g hg
  have hgNorm : g ∈ Metric.ball (0 : C(S, ℂ)) epsilonNorm := by
    exact Metric.ball_subset_ball (min_le_left _ _) hg
  have hgRho : g ∈ Metric.ball (0 : C(S, ℂ)) epsilonRho := by
    exact Metric.ball_subset_ball (min_le_right _ _) hg
  exact fms_radius_eq_of_normalized_radius_eq_one M hM
    (hrhoBall hgRho) (hnormalized g hgNorm)

end FiniteIrreducibleFieldRootedTree

namespace FiniteIrreducibleModel

/-- The real-field radius theorem now extends to one genuine complex-field
ball. Its upper bound comes from the nonzero actual fold derivative. -/
theorem fieldFMS_radius_eq_critical_radius_complex_eventually
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) epsilon,
        (M.fieldFMS g).radius =
          ‖FiniteIrreducibleRadiusResponse.radius M hM g‖ₑ := by
  simpa only [FiniteIrreducibleFieldRootedTree.fms_eq_fieldFMS] using
    FiniteIrreducibleFieldRootedTree.fms_radius_eq_critical_radius_eventually M hM

end FiniteIrreducibleModel

end PerronWright
