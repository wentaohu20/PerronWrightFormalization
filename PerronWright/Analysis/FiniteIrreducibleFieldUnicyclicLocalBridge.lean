import PerronWright.Enumeration.FieldTreeEGFMatching
import PerronWright.Analysis.FiniteIrreducibleUnicyclicFullTaylor
import PerronWright.Analysis.FiniteIrreducibleNormalizedDeltaProfile
import PerronWright.Analysis.FiniteIrreducibleSimpleCycleResolventBridge
import PerronWright.Transfer.CoefficientCauchy

/-!
# The literal complex-field unicyclic germ and the joint fold germ

This module records the two rigorously available ends of the complex-field
unicyclic argument.

* At activity zero, the simple-cycle functional of any genuine normalized
  joint tree profile has the Taylor series of the literal connected
  unicyclic graph weights, with the exact factor `rho(g)^n`.
* At the critical fold, the marked-cycle calculation gives a jointly
  analytic regular part and a normalized joint primitive after the explicit
  pole `-1/(2X)` is removed.

No global determinant and no global unicyclic continuation are assumed.
In particular, the last theorem deliberately keeps the literal activity-zero
germ and the critical fold germ as two separately proved interfaces.  A later
global gluing theorem must identify them before a family-uniform coefficient
transfer may be applied.
-/

open Filter Topology PerronWright Set
open scoped Classical Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldUnicyclicLocalBridge

namespace Global

export PerronWright.FiniteIrreducibleNormalizedDeltaProfile
  (exists_uniform_normalized_cartesianDelta_profile_of_terminal)

end Global

namespace JS

export PerronWright.JointSimpleCycleEGF
  (profileSimpleCycleSeries)

end JS

namespace SC

export PerronWright.FiniteIrreducibleSimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation
   exists_simpleCycleDerivativeContinuation_regularPrimitive)

end SC

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal labelled EGF of connected unicyclic graphs in a fixed
complex field.  Its coefficient is the graph weight itself divided by the
vertex factorial; no analytic continuation is built into this definition. -/
def complexFieldUnicyclicEGF (M : FiniteIrreducibleModel S)
    (g : C(S, ℂ)) : PowerSeries ℂ :=
  PowerSeries.mk (fun n ↦
    M.bjrModel.complexFieldConnectedWeight g n 1 / (n.factorial : ℂ))

@[simp] theorem complexFieldUnicyclicEGF_coeff
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (n : ℕ) :
    PowerSeries.coeff n (complexFieldUnicyclicEGF M g) =
      M.bjrModel.complexFieldConnectedWeight g n 1 / (n.factorial : ℂ) := by
  simp [complexFieldUnicyclicEGF]

/-- One-dimensional formal multilinear form of the literal complex-field
unicyclic EGF. -/
def fieldUnicyclicFMS (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  oneDimensionalFormalMultilinearSeries (complexFieldUnicyclicEGF M g)

/-- Pullback of the literal unicyclic EGF by the genuine critical activity
`z = rho(g) w`. -/
def normalizedFieldUnicyclicFMS (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (fieldUnicyclicFMS M g).compContinuousLinearMap
    ((FiniteIrreducibleRadiusResponse.radius M hM g) • ContinuousLinearMap.id ℂ ℂ)

/-- Exact coefficient of the normalized literal unicyclic series. -/
theorem normalizedFieldUnicyclicFMS_coeff
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (n : ℕ) :
    (normalizedFieldUnicyclicFMS M hM g).coeff n =
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
        (M.bjrModel.complexFieldConnectedWeight g n 1 / (n.factorial : ℂ)) := by
  rw [normalizedFieldUnicyclicFMS,
    FieldTreeEGFMatching.comp_smul_id_coeff]
  simp only [fieldUnicyclicFMS,
    oneDimensionalFormalMultilinearSeries_coeff,
    complexFieldUnicyclicEGF_coeff, smul_eq_mul]

/-- For a genuine normalized joint tree profile, composition with the direct
simple-cycle functional has exactly the normalized literal unicyclic Taylor
series at activity zero.

The proof first returns to the physical activity `z = rho(g) w`, applies the
finite-graph coefficient theorem there, and then pulls the series back by the
same scalar map.  Thus no generating-function identity is assumed. -/
theorem normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta s : ℝ}
    {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
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
    HasFPowerSeriesAt
      (fun w : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (Theta (w, g)))
      (normalizedFieldUnicyclicFMS M hM g) 0 := by
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
  have hpPhysical : HasFPowerSeriesAt
      (fun z : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (psi (z, g)))
      (fieldUnicyclicFMS M g) 0 := by
    simpa only [fieldUnicyclicFMS, complexFieldUnicyclicEGF] using
      FiniteIrreducibleUnicyclicFullTaylor.profileSimpleCycleSeries_hasFPowerSeriesAt_connectedWeights
        M hM g psi hpsi hpsi0 hres
  let u : ℂ →L[ℂ] ℂ := rho • ContinuousLinearMap.id ℂ ℂ
  have hpAtUZero : HasFPowerSeriesAt
      (fun z : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (psi (z, g)))
      (fieldUnicyclicFMS M g) (u 0) := by
    simpa only [u, smul_apply,
      ContinuousLinearMap.id_apply, smul_zero] using hpPhysical
  have hpComp := hpAtUZero.compContinuousLinearMap
    (u := u) (x := (0 : ℂ))
  have hfun :
      (fun z : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (psi (z, g))) ∘ u =
        (fun w : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (Theta (w, g))) := by
    funext w
    simp only [Function.comp_apply, u, psi, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    have hcancel : rho * w / rho = w := by
      rw [mul_comm rho w, mul_div_cancel_right₀ w hrho]
    rw [hcancel]
  rw [hfun] at hpComp
  simpa only [normalizedFieldUnicyclicFMS, u, rho] using hpComp

/-- Exact Taylor-coefficient identification for the literal normalized
unicyclic profile germ. -/
theorem normalized_profileSimpleCycle_taylorCoefficient_eq_connectedWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta s : ℝ}
    {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (heta : 0 < eta) (hs : 0 < s)
    (hTheta : AnalyticOnNhd ℂ Theta
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s))
    (hData : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M.bjrModel
          (FiniteIrreducibleNormalizedFoldActivity.activityMap M hM q, Theta q) = 0)
    {g : C(S, ℂ)} (hg : g ∈ Metric.ball 0 s) (n : ℕ) :
    Transfer.taylorCoefficient
        (fun w : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel (Theta (w, g))) n =
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
        (M.bjrModel.complexFieldConnectedWeight g n 1 / (n.factorial : ℂ)) := by
  rw [← normalizedFieldUnicyclicFMS_coeff M hM g n]
  have hF :=
    normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile
      M hM heta hs hTheta hData hg
  have hcanonical := hF.analyticAt.hasFPowerSeriesAt
  have hseries := hF.eq_formalMultilinearSeries hcanonical
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) hseries
  simpa only [Transfer.taylorCoefficient,
    FormalMultilinearSeries.coeff_ofScalars] using hcoeff.symm

/-- The concrete global tree profile supplies the literal normalized
unicyclic germ at activity zero, while the marked-cycle construction supplies
the normalized joint critical-fold primitive.  These are the maximal two
interfaces currently derivable without a global joint unicyclic gluing
theorem. -/
theorem exists_normalizedFieldUnicyclic_literal_and_fold_germs
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (eta r s : ℝ)
      (Theta : ℂ × C(S, ℂ) → C(S, ℂ))
      (U : ℂ × C(S, ℂ) → ℂ)
      (B H : C(S, ℂ) × ℂ → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ Theta
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel
            (FiniteIrreducibleNormalizedFoldActivity.activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta
        (FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile M hM)
        (FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        U q = JS.profileSimpleCycleSeries M.bjrModel (Theta q)) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ U (w, g))
          (normalizedFieldUnicyclicFMS M hM g) 0) ∧
      AnalyticAt ℂ B (0, 0) ∧
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0), q.2 ≠ 0 →
        SC.simpleCycleDerivativeContinuation M hM q =
          -(1 / 2 : ℂ) * q.2⁻¹ + B q) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0),
        (fderiv ℂ H q) (0, 1) = B q := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, _hActivity, hTheta,
      hData, hThetaFold, _hInside⟩ :=
    Global.exists_uniform_normalized_cartesianDelta_profile_of_terminal M hM
  obtain ⟨B, H, hB, hH, hHaxis, hsplit, hHderiv⟩ :=
    SC.exists_simpleCycleDerivativeContinuation_regularPrimitive M hM
  let U : ℂ × C(S, ℂ) → ℂ := fun q ↦
    JS.profileSimpleCycleSeries M.bjrModel (Theta q)
  refine ⟨eta, r, s, Theta, U, B, H, heta, hr, hs,
    hTheta, hData, hThetaFold, fun _ ↦ rfl, ?_,
    hB, hH, hHaxis, hsplit, hHderiv⟩
  intro g hg
  simpa only [U] using
    normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile
      M hM heta hs hTheta hData hg

end PerronWright.FiniteIrreducibleFieldUnicyclicLocalBridge
