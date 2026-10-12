import PerronWright.Analysis.FiniteIrreducibleNoncubicFieldLocalBridge
import PerronWright.Analysis.FiniteIrreducibleTreeProfileTube
import PerronWright.Enumeration.FieldTreeEGFMatching

/-!
# Joint Cartesian-Delta continuation of the positive-surplus noncubic part

The away chart is the finite noncubic admissible-profile functional
evaluated at the global normalized tree profile.  The fold chart is the
finite noncubic integrated amplitude divided by the explicit cubic pole
factor.  Their equality on the overlap is the exact bounded-kernel profile
identity, so the gluing introduces no uniqueness assumption.

At activity zero the glued function has the actual complex-field
noncubic-part EGF as its Taylor series.  The local numerator also retains
the proved extra fold-coordinate factor carried by every noncubic kernel.
-/

open Filter Topology PerronWright Set
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleNoncubicGlobalContinuation

open PerronWright.GraphCore PerronWright.FiniteIrreducibleKernelAmplitude

namespace MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent (profile)

end MPR

namespace ZA

export PerronWright.ZeroFieldUnicyclicActivitySingularity
  (cartesianDeltaSqrt_mem_slitPlane)

end ZA

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- Pullback of the actual complex-field noncubic-part EGF by the
normalized activity change `z = rho(g) w`. -/
def normalizedFieldNoncubicPartFMS
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (ell : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  (oneDimensionalFormalMultilinearSeries
      (complexFieldNoncubicPartEGF M g ell)).compContinuousLinearMap
    ((FiniteIrreducibleRadiusResponse.radius M hM g) • ContinuousLinearMap.id ℂ ℂ)

/-- Exact coefficient rescaling from physical to normalized activity. -/
@[simp] theorem normalizedFieldNoncubicPartFMS_coeff
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (ell n : ℕ) :
    (normalizedFieldNoncubicPartFMS M hM g ell).coeff n =
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
        PowerSeries.coeff n (complexFieldNoncubicPartEGF M g ell) := by
  rw [normalizedFieldNoncubicPartFMS,
    FieldTreeEGFMatching.comp_smul_id_coeff]
  simp only [oneDimensionalFormalMultilinearSeries_coeff, smul_eq_mul]

/-- A genuine normalized tree profile has the normalized actual noncubic
EGF as the Taylor series of its admissible profile functional. -/
private theorem
    profileFunctional_hasFPowerSeriesAt_normalizedFieldNoncubicPart
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
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
      (fun w : ℂ ↦
        positiveSurplusNoncubicAdmissibleProfileFunctional
          M ell (Theta (w, g)))
      (normalizedFieldNoncubicPartFMS M hM g ell) 0 := by
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
  have hres : ∀ᶠ z : ℂ in 𝓝 0,
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
      (fun z : ℂ ↦
        positiveSurplusNoncubicAdmissibleProfileFunctional
          M ell (psi (z, g)))
      (oneDimensionalFormalMultilinearSeries
        (complexFieldNoncubicPartEGF M g ell)) 0 :=
    positiveSurplusNoncubicAdmissibleProfileFunctional_hasFPowerSeriesAt_complexFieldNoncubicPart
      M hM hell g psi hpsi hpsi0 hres
  let u : ℂ →L[ℂ] ℂ :=
    rho • ContinuousLinearMap.id ℂ ℂ
  have hpAtUZero : HasFPowerSeriesAt
      (fun z : ℂ ↦
        positiveSurplusNoncubicAdmissibleProfileFunctional
          M ell (psi (z, g)))
      (oneDimensionalFormalMultilinearSeries
        (complexFieldNoncubicPartEGF M g ell)) (u 0) := by
    simpa only [u, smul_apply, ContinuousLinearMap.id_apply, smul_zero]
      using hpPhysical
  have hpComp := hpAtUZero.compContinuousLinearMap
    (u := u) (x := (0 : ℂ))
  have hfun :
      (fun z : ℂ ↦
        positiveSurplusNoncubicAdmissibleProfileFunctional
          M ell (psi (z, g))) ∘ u =
        (fun w : ℂ ↦
          positiveSurplusNoncubicAdmissibleProfileFunctional
            M ell (Theta (w, g))) := by
    funext w
    simp only [Function.comp_apply, u, psi, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    have hcancel : rho * w / rho = w := by
      rw [mul_comm rho w, mul_div_cancel_right₀ w hrho]
    rw [hcancel]
  rw [hfun] at hpComp
  simpa only [normalizedFieldNoncubicPartFMS, u, rho] using hpComp

private theorem cartesianDelta_mono_eta {eta₁ eta₂ m : ℝ}
    (h : eta₁ ≤ eta₂) :
    Transfer.cartesianDelta eta₁ m ⊆
      Transfer.cartesianDelta eta₂ m := by
  intro w hw
  exact ⟨hw.1.trans_le (by linarith), hw.2⟩

/-- The actual complex-field noncubic-part EGF has a jointly analytic
Cartesian-Delta continuation on a fixed complex field ball.  Its fold
chart is the finite noncubic integrated amplitude divided by the explicit
`X^(3*ell)` factor.  The numerator itself is analytic and has the separate
explicit factor `X` recorded in
`exists_analytic_noncubicIntegratedRemainder`. -/
theorem exists_complexFieldNoncubicPart_cartesianDelta_continuation
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ (eta r s : ℝ) (G : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ
        (positiveSurplusNoncubicIntegratedAmplitude M hM ell)
        (Metric.ball (0 : C(S, ℂ)) s ×ˢ Metric.ball (0 : ℂ) r) ∧
      positiveSurplusNoncubicIntegratedAmplitude M hM ell (0, 0) = 0 ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (normalizedFieldNoncubicPartFMS M hM g ell) 0) ∧
      ∀ q ∈ FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        G q =
          (Transfer.cartesianDeltaSqrt q.1 ^ (3 * ell))⁻¹ *
            positiveSurplusNoncubicIntegratedAmplitude M hM ell
              (q.2, Transfer.cartesianDeltaSqrt q.1) := by
  obtain ⟨eta₀, rTheta, sTheta, Theta,
      heta₀, hrTheta, hsTheta, _hActivity, hTheta, hData,
      hThetaFold, hInside⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM

  have hgoodLocal : ∀ᶠ z : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ
          (positiveSurplusNoncubicIntegratedAmplitude M hM ell) z ∧
        (z.2 ≠ 0 →
          positiveSurplusNoncubicIntegratedAmplitude M hM ell z =
            z.2 ^ (3 * ell) *
              positiveSurplusNoncubicAdmissibleProfileFunctional M ell
                (MPR.profile M hM z)) := by
    filter_upwards
      [(positiveSurplusNoncubicIntegratedAmplitude_analytic
          M hM ell).eventually_analyticAt,
        positiveSurplusNoncubicIntegratedAmplitude_eq_profileFunctional
          M hM ell]
      with z hzAnalytic hzProfile
    exact ⟨hzAnalytic, hzProfile⟩
  obtain ⟨rLocal, hrLocal, hLocal⟩ :=
    Metric.eventually_nhds_iff.mp hgoodLocal

  let r : ℝ := min (min rTheta rLocal) 1 / 2
  have hr : 0 < r := by
    dsimp only [r]
    exact half_pos (lt_min (lt_min hrTheta hrLocal) zero_lt_one)
  have hrTheta' : r ≤ rTheta := by
    dsimp only [r]
    nlinarith [min_le_left rTheta rLocal,
      min_le_left (min rTheta rLocal) 1]
  have hrLocal' : r ≤ rLocal := by
    dsimp only [r]
    nlinarith [min_le_right rTheta rLocal,
      min_le_left (min rTheta rLocal) 1]

  let delta : ℝ := min 1 (r ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact half_pos (lt_min zero_lt_one (pow_pos hr 2))
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    nlinarith [min_le_left (1 : ℝ) (r ^ 2)]
  have hdeltaR : delta ≤ r ^ 2 := by
    dsimp only [delta]
    nlinarith [min_le_right (1 : ℝ) (r ^ 2), pow_pos hr 2]
  let K : Set ℂ :=
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta

  obtain ⟨t, ht, hAwaySub₀, hAwayNorm₀⟩ :=
    FiniteIrreducibleTreeProfileTube.exists_uniform_profile_unitBall_tube
      M hM heta₀ hsTheta hdelta hTheta hInside
  let s : ℝ := min t (min sTheta rLocal)
  have hs : 0 < s := lt_min ht (lt_min hsTheta hrLocal)
  have hsT : s ≤ t := min_le_left t (min sTheta rLocal)
  have hsTheta' : s ≤ sTheta :=
    (min_le_right t (min sTheta rLocal)).trans
      (min_le_left sTheta rLocal)
  have hsLocal : s ≤ rLocal :=
    (min_le_right t (min sTheta rLocal)).trans
      (min_le_right sTheta rLocal)

  obtain ⟨etaCover, hetaCover, hCover⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_cartesianDelta_subset_fold_union_away
      hr ht hdeltaR
  let eta : ℝ := min etaCover eta₀
  have heta : 0 < eta := lt_min hetaCover heta₀
  have hDeltaCover : Transfer.cartesianDelta eta 0 ⊆
      FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ∪
        Metric.thickening t K := by
    intro w hw
    apply hCover
    exact cartesianDelta_mono_eta (min_le_left etaCover eta₀) hw

  let D₀ : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta₀ 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) sTheta
  let DAway : Set (ℂ × C(S, ℂ)) :=
    Metric.thickening t K ×ˢ Metric.ball (0 : C(S, ℂ)) s
  have hAwaySub : DAway ⊆ D₀ := by
    intro q hq
    exact hAwaySub₀ ⟨hq.1, Metric.ball_subset_ball hsT hq.2⟩
  have hAwayNorm : ∀ q ∈ DAway, ‖Theta q‖ < 1 := by
    intro q hq
    exact hAwayNorm₀ q
      ⟨hq.1, Metric.ball_subset_ball hsT hq.2⟩

  let A : ℂ × C(S, ℂ) → ℂ := fun q ↦
    positiveSurplusNoncubicAdmissibleProfileFunctional M ell (Theta q)
  have hA : AnalyticOnNhd ℂ A DAway := by
    intro q hq
    have hqD : q ∈ D₀ := hAwaySub hq
    have hprofile : AnalyticAt ℂ Theta q := hTheta q hqD
    have hnorm : ‖Theta q‖ < 1 := hAwayNorm q hq
    have hnoncubic : AnalyticAt ℂ
        (positiveSurplusNoncubicAdmissibleProfileFunctional M ell)
          (Theta q) :=
      positiveSurplusNoncubicAdmissibleProfileFunctional_analyticOnNhd_unitBall
        M hM ell (Theta q) (by
          simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    exact hnoncubic.comp_of_eq hprofile rfl

  have hN : AnalyticOnNhd ℂ
      (positiveSurplusNoncubicIntegratedAmplitude M hM ell)
      (Metric.ball (0 : C(S, ℂ)) s ×ˢ
        Metric.ball (0 : ℂ) r) := by
    intro z hz
    apply (hLocal ?_).1
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(Metric.mem_ball.mp hz.1).trans_le hsLocal,
      (Metric.mem_ball.mp hz.2).trans_le hrLocal'⟩

  let F : ℂ × C(S, ℂ) → ℂ := fun q ↦
    (Transfer.cartesianDeltaSqrt q.1 ^ (3 * ell))⁻¹ *
      positiveSurplusNoncubicIntegratedAmplitude M hM ell
        (q.2, Transfer.cartesianDeltaSqrt q.1)
  let DFold : Set (ℂ × C(S, ℂ)) :=
    FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  have hF : AnalyticOnNhd ℂ F DFold := by
    intro q hq
    have hX : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          Transfer.cartesianDeltaSqrt p.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num)) q.1 hq.1.1).comp_of_eq analyticAt_fst rfl
    have hXslit : Transfer.cartesianDeltaSqrt q.1 ∈ Complex.slitPlane :=
      ZA.cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ))
        (by norm_num) hq.1.1
    have hXne : Transfer.cartesianDeltaSqrt q.1 ≠ 0 :=
      (Complex.mem_slitPlane_iff_arg.mp hXslit).2
    have hInv : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          (Transfer.cartesianDeltaSqrt p.1 ^ (3 * ell))⁻¹) q :=
      (hX.pow (3 * ell)).inv (pow_ne_zero _ hXne)
    have hNcomp : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          positiveSurplusNoncubicIntegratedAmplitude M hM ell
            (p.2, Transfer.cartesianDeltaSqrt p.1)) q := by
      exact (hN (q.2, Transfer.cartesianDeltaSqrt q.1)
        ⟨hq.2, hq.1.2⟩).comp_of_eq (analyticAt_snd.prod hX) rfl
    change AnalyticAt ℂ
      (fun p : ℂ × C(S, ℂ) ↦
        (Transfer.cartesianDeltaSqrt p.1 ^ (3 * ell))⁻¹ *
          positiveSurplusNoncubicIntegratedAmplitude M hM ell
            (p.2, Transfer.cartesianDeltaSqrt p.1)) q
    exact hInv.mul hNcomp

  have hOverlap : Set.EqOn F A (DFold ∩ DAway) := by
    intro q hq
    let X : ℂ := Transfer.cartesianDeltaSqrt q.1
    have hThetaDomain : q ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rTheta ×ˢ
          Metric.ball (0 : C(S, ℂ)) sTheta := by
      exact ⟨⟨hq.1.1.1,
        Metric.ball_subset_ball hrTheta' hq.1.1.2⟩,
        Metric.ball_subset_ball hsTheta' hq.1.2⟩
    have hThetaEq : Theta q = MPR.profile M hM (q.2, X) := by
      simpa only [FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile,
        MPR.profile, X] using hThetaFold hThetaDomain
    have hInput : dist (q.2, X)
        ((0 : C(S, ℂ)), (0 : ℂ)) < rLocal := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(Metric.mem_ball.mp hq.1.2).trans_le hsLocal,
        (Metric.mem_ball.mp hq.1.1.2).trans_le hrLocal'⟩
    have hraw := (hLocal hInput).2
    have hXslit : X ∈ Complex.slitPlane := by
      exact ZA.cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ))
        (by norm_num) hq.1.1.1
    have hXne : X ≠ 0 :=
      (Complex.mem_slitPlane_iff_arg.mp hXslit).2
    have hpow : X ^ (3 * ell) ≠ 0 := pow_ne_zero _ hXne
    calc
      F q = (X ^ (3 * ell))⁻¹ *
          positiveSurplusNoncubicIntegratedAmplitude M hM ell
            (q.2, X) := rfl
      _ = positiveSurplusNoncubicAdmissibleProfileFunctional M ell
          (MPR.profile M hM (q.2, X)) := by
        rw [hraw hXne, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
      _ = A q := by
        rw [← hThetaEq]

  let G : ℂ × C(S, ℂ) → ℂ :=
    AnalyticTwoChartGluing.glueOn DFold F A
  have hDFoldOpen : IsOpen DFold :=
    (FiniteIrreducibleNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num)).prod
      Metric.isOpen_ball
  have hDAwayOpen : IsOpen DAway :=
    Metric.isOpen_thickening.prod Metric.isOpen_ball
  have hGunion : AnalyticOnNhd ℂ G (DFold ∪ DAway) :=
    AnalyticTwoChartGluing.analyticOnNhd_glueOn_union
      hDFoldOpen hDAwayOpen hF hA hOverlap
  have hTargetCover :
      Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s ⊆ DFold ∪ DAway := by
    intro q hq
    rcases hDeltaCover hq.1 with hwFold | hwAway
    · exact Or.inl ⟨hwFold, hq.2⟩
    · exact Or.inr ⟨hwAway, hq.2⟩
  have hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) :=
    fun q hq ↦ hGunion q (hTargetCover hq)
  have hGleft : Set.EqOn G F DFold :=
    AnalyticTwoChartGluing.glueOn_eqOn_left DFold F A
  have hGright : Set.EqOn G A DAway :=
    AnalyticTwoChartGluing.glueOn_eqOn_right_of_eqOn_inter hOverlap

  have hzeroK : (0 : ℂ) ∈ K := by
    dsimp only [K]
    constructor
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      norm_num
    · change delta ≤ dist (0 : ℂ) 1
      simpa only [dist_zero_left, norm_one] using hdeltaOne
  have hzeroAway : (0 : ℂ) ∈ Metric.thickening t K :=
    Metric.self_subset_thickening ht K hzeroK
  have hTaylor : ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
      HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
        (normalizedFieldNoncubicPartFMS M hM g ell) 0 := by
    intro g hg
    have hAseries : HasFPowerSeriesAt (fun w : ℂ ↦ A (w, g))
        (normalizedFieldNoncubicPartFMS M hM g ell) 0 := by
      simpa only [A] using
        profileFunctional_hasFPowerSeriesAt_normalizedFieldNoncubicPart
          M hM hell heta₀ hsTheta hTheta hData
            (Metric.ball_subset_ball hsTheta' hg)
    have hEq : (fun w : ℂ ↦ G (w, g)) =ᶠ[nhds 0]
        (fun w : ℂ ↦ A (w, g)) := by
      filter_upwards [Metric.isOpen_thickening.mem_nhds hzeroAway] with w hw
      exact hGright ⟨hw, hg⟩
    exact hAseries.congr hEq.symm

  have hFormula : ∀ q ∈ DFold,
      G q =
        (Transfer.cartesianDeltaSqrt q.1 ^ (3 * ell))⁻¹ *
          positiveSurplusNoncubicIntegratedAmplitude M hM ell
            (q.2, Transfer.cartesianDeltaSqrt q.1) := by
    intro q hq
    simpa only [F] using hGleft hq
  have hbase :
      positiveSurplusNoncubicIntegratedAmplitude M hM ell (0, 0) = 0 := by
    rw [FiniteIrreducibleKernelAmplitude.positiveSurplusNoncubicIntegratedAmplitude_eq_X_mul]
    simp
  exact ⟨eta, r, s, G, heta, hr, hs, hN, hbase,
    hG, hTaylor, hFormula⟩

end PerronWright.FiniteIrreducibleNoncubicGlobalContinuation
