import PerronWright.Enumeration.FieldRootedTreeFormal

open MeasureTheory
open Topology
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

namespace FieldRootedTree

/-- At any field where the actual implicit branch is analytic at activity
zero, its one-variable Taylor series is the genuine finite labelled-tree
series just constructed. -/
theorem branch_taylorSeries_eq_series
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (psi : ℂ × C(S, ℂ) → C(S, ℂ))
    (hpsi : AnalyticAt ℂ psi (0, g))
    (hpsi0 : psi (0, g) = 0)
    (hres : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M ((z, g), psi (z, g)) = 0) :
    ∃ p : FormalMultilinearSeries ℂ ℂ C(S, ℂ),
      HasFPowerSeriesAt (fun z ↦ psi (z, g)) p 0 ∧
      oneDimensionalPowerSeries p = formalRHS M g (oneDimensionalPowerSeries p) ∧
      oneDimensionalPowerSeries p = series M g := by
  let phi : ℂ → C(S, ℂ) := fun z ↦ psi (z, g)
  have hline : AnalyticAt ℂ (fun z : ℂ ↦ (z, g)) 0 :=
    analyticAt_id.prod analyticAt_const
  have hphi : AnalyticAt ℂ phi 0 := hpsi.comp_of_eq hline rfl
  obtain ⟨p, hp⟩ := hphi
  have hphi0 : phi 0 = 0 := hpsi0
  have hp0 : p.coeff 0 = 0 := by
    calc
      p.coeff 0 = phi 0 := by
        simpa only [FormalMultilinearSeries.coeff] using
          hp.coeff_zero (1 : Fin 0 → ℂ)
      _ = 0 := hphi0
  let K : C(S, ℂ) →L[ℂ] C(S, ℂ) := M.kernel.complexActionCLM M.mu
  let kappa : ℂ → C(S, ℂ) := fun z ↦ K (phi z)
  let pK : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    K.compFormalMultilinearSeries p
  have hpK : HasFPowerSeriesAt kappa pK 0 := by
    obtain ⟨r, hr⟩ := hp
    refine ⟨r, ?_⟩
    simpa only [kappa, pK, Function.comp_def] using
      K.comp_hasFPowerSeriesOnBall hr
  have hpK0 : pK.coeff 0 = 0 := by
    change K (p.coeff 0) = 0
    rw [hp0, map_zero]
  let q : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    (NormedSpace.expSeries ℂ C(S, ℂ)).comp pK
  have hkappa0 : kappa 0 = 0 := by simp only [kappa, hphi0, map_zero]
  have hexp0 : HasFPowerSeriesAt
      (NormedSpace.exp : C(S, ℂ) → C(S, ℂ))
      (NormedSpace.expSeries ℂ C(S, ℂ)) (kappa 0) := by
    simpa only [hkappa0] using
      (NormedSpace.exp_hasFPowerSeriesAt_zero
        (𝕂 := ℂ) (𝔸 := C(S, ℂ)))
  have hq : HasFPowerSeriesAt
      (fun z ↦ NormedSpace.exp (kappa z)) q 0 := by
    simpa only [q, Function.comp_def] using hexp0.comp hpK
  let c : C(S, ℂ) := vertexFactor M g
  let Lc : C(S, ℂ) →L[ℂ] C(S, ℂ) :=
    ContinuousLinearMap.mul ℂ C(S, ℂ) c
  let h : ℂ → C(S, ℂ) := fun z ↦ c * NormedSpace.exp (kappa z)
  let r : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    Lc.compFormalMultilinearSeries q
  have hr : HasFPowerSeriesAt h r 0 := by
    obtain ⟨rho, hrho⟩ := hq
    refine ⟨rho, ?_⟩
    simpa only [h, r, Lc, Function.comp_def,
      ContinuousLinearMap.mul_apply'] using
      Lc.comp_hasFPowerSeriesOnBall hrho
  have hfixed : phi =ᶠ[𝓝 (0 : ℂ)] fun z ↦ z • h z := by
    filter_upwards [hres] with z hz
    have hz' : phi z = z • NormedSpace.exp
        (g - TreeCritical.degree M + K (phi z)) := by
      change phi z - z • NormedSpace.exp
        (g - TreeCritical.degree M + K (phi z)) = 0 at hz
      exact sub_eq_zero.mp hz
    calc
      phi z = z • NormedSpace.exp
          (g - TreeCritical.degree M + K (phi z)) := hz'
      _ = z • (NormedSpace.exp (g - TreeCritical.degree M) *
          NormedSpace.exp (K (phi z))) := by
        rw [NormedSpace.exp_add]
      _ = z • h z := rfl
  have hrhsDeriv : deriv (fun z ↦ z • h z) 0 = h 0 := by
    have hh := (hasDerivAt_id (0 : ℂ)).smul hr.hasDerivAt
    have hfun : (fun z : ℂ ↦ z • h z) = (id : ℂ → ℂ) • h := by
      funext z
      rfl
    rw [hfun]
    simpa only [id_eq, zero_smul, zero_add, one_smul] using hh.deriv
  have hphiDeriv : deriv phi 0 = h 0 := hfixed.deriv_eq.trans hrhsDeriv
  have hdslope : dslope phi 0 =ᶠ[𝓝 (0 : ℂ)] h := by
    filter_upwards [hfixed] with z hz
    by_cases hz0 : z = 0
    · subst z
      simpa only [dslope_same] using hphiDeriv
    · rw [dslope_of_ne _ hz0]
      rw [slope, sub_zero, hphi0, hz, vsub_eq_sub, sub_zero, ← mul_smul,
        inv_mul_cancel₀ hz0, one_smul]
  have hpSlope := hp.has_fpower_series_dslope_fslope
  have hpSlopeEq : p.fslope = r :=
    hpSlope.eq_formalMultilinearSeries_of_eventually hr hdslope
  have hqPower : oneDimensionalPowerSeries q =
      PowerSeries.subst (oneDimensionalPowerSeries pK)
        (PowerSeries.exp C(S, ℂ)) := by
    simpa only [q] using oneDimensionalPowerSeries_exp_comp hpK hpK0
  have hpKPower : oneDimensionalPowerSeries pK =
      M.complexKernelActionPowerSeries (oneDimensionalPowerSeries p) := by
    simpa only [pK, K] using M.oneDimensionalPowerSeries_kernelAction p
  have hformal : oneDimensionalPowerSeries p =
      formalRHS M g (oneDimensionalPowerSeries p) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        simp only [oneDimensionalPowerSeries_coeff, hp0,
          formalRHS_coeff_zero]
    | succ n =>
        have hcoeff' : p.coeff (n + 1) = c * q.coeff n := by
          rw [← FormalMultilinearSeries.coeff_fslope, hpSlopeEq]
          simp only [r, Lc, FormalMultilinearSeries.coeff,
            ContinuousLinearMap.compFormalMultilinearSeries_apply',
            ContinuousLinearMap.mul_apply']
        rw [formalRHS, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_C_mul]
        calc
          PowerSeries.coeff (n + 1) (oneDimensionalPowerSeries p) =
              p.coeff (n + 1) := oneDimensionalPowerSeries_coeff p (n + 1)
          _ = c * q.coeff n := hcoeff'
          _ = c * PowerSeries.coeff n (oneDimensionalPowerSeries q) := by
            rw [oneDimensionalPowerSeries_coeff]
          _ = c * PowerSeries.coeff n
                (PowerSeries.subst (oneDimensionalPowerSeries pK)
                  (PowerSeries.exp C(S, ℂ))) := by rw [hqPower]
          _ = c * PowerSeries.coeff n
                (PowerSeries.subst
                  (M.complexKernelActionPowerSeries
                    (oneDimensionalPowerSeries p))
                  (PowerSeries.exp C(S, ℂ))) := by rw [hpKPower]
          _ = vertexFactor M g * PowerSeries.coeff n
                (PowerSeries.subst
                  (M.complexKernelActionPowerSeries
                    (oneDimensionalPowerSeries p))
                  (PowerSeries.exp C(S, ℂ))) := rfl
  have hactual := formalRHS_fixedPoint_unique M g
    (oneDimensionalPowerSeries p)
    (by simpa only [oneDimensionalPowerSeries_constantCoeff] using hp0)
    hformal
  exact ⟨p, hp, hformal, hactual⟩

/-- The actual joint implicit branch therefore has, for every sufficiently
small complex field, precisely the finite labelled-tree Taylor coefficients.
This is the local enumerative germ needed for later continuation; it makes no
claim about convergence at the critical boundary. -/
theorem exists_joint_branch_with_field_labelledTreeTaylorSeries
    (M : CompactBJRModel S) :
    ∃ psi : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ psi (0, 0) ∧ psi (0, 0) = 0 ∧
      (∀ᶠ q in 𝓝 (0, (0 : C(S, ℂ))),
        TreeCritical.residual M (q, psi q) = 0) ∧
      ∀ᶠ g : C(S, ℂ) in 𝓝 0,
        ∃ p : FormalMultilinearSeries ℂ ℂ C(S, ℂ),
          HasFPowerSeriesAt (fun z ↦ psi (z, g)) p 0 ∧
          oneDimensionalPowerSeries p = series M g := by
  obtain ⟨psi, hpsi, hpsi0, hres, -⟩ :=
    TreeAnalytic.zero_tree_branch M.kernel M.mu (TreeCritical.degree M)
  have hgood : ∀ᶠ q : ℂ × C(S, ℂ) in 𝓝 (0, 0),
      AnalyticAt ℂ psi q ∧ TreeCritical.residual M (q, psi q) = 0 := by
    filter_upwards [hpsi.eventually_analyticAt, hres] with q hqa hrq
    exact ⟨hqa, hrq⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨psi, hpsi, hpsi0, hres, ?_⟩
  filter_upwards [Metric.eventually_nhds_iff.mpr
    ⟨ε / 2, by positivity, fun g hg ↦ hg⟩] with g hg
  have hg' : dist g 0 < ε / 2 := by simpa only [dist_zero_right] using hg
  have hpair : dist ((0 : ℂ), g) ((0 : ℂ), (0 : C(S, ℂ))) < ε := by
    rw [Prod.dist_eq]
    simp only [dist_self, max_lt_iff]
    exact ⟨hε, hg'.trans (half_lt_self hε)⟩
  have hpsia : AnalyticAt ℂ psi (0, g) := (hball hpair).1
  have hpsi0g : psi (0, g) = 0 := by
    have hr0 := (hball hpair).2
    change psi (0, g) - (0 : ℂ) •
      NormedSpace.exp
        (g - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (psi (0, g))) = 0 at hr0
    simpa only [zero_smul, sub_zero] using hr0
  have hresg : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M ((z, g), psi (z, g)) = 0 := by
    filter_upwards [Metric.eventually_nhds_iff.mpr
      ⟨ε / 2, by positivity, fun z hz ↦ hz⟩] with z hz
    have hz' : dist z 0 < ε / 2 := by simpa only [dist_zero_right] using hz
    apply (hball ?_).2
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz'.trans (half_lt_self hε),
      hg'.trans (half_lt_self hε)⟩
  obtain ⟨p, hp, -, hactual⟩ :=
    branch_taylorSeries_eq_series M g psi hpsia hpsi0g hresg
  exact ⟨p, hp, hactual⟩


end FieldRootedTree

end PerronWright


