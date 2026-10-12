import PerronWright.Enumeration.UnicyclicCoefficientReindex
import PerronWright.Analysis.FiniteIrreducibleProfileSimpleCyclePowerSeries
import PerronWright.Analysis.FiniteIrreducibleUnicyclicTailOrder
import PerronWright.Analysis.AnalyticCoeffOrder
import PerronWright.Enumeration.FieldRootedTreeAnalyticGerm

/-!
# The complete Taylor series of the unicyclic profile contribution

This module combines finite-cycle analytic realization, the genuine infinite
cycle tail estimate, and analyticity of the full cycle sum.  It proves that
the literal unicyclic profile-composition coefficients are exactly the Taylor
coefficients of the actual infinite simple-cycle series.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright.FiniteIrreducibleUnicyclicFullTaylor

open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual infinite simple-cycle series has the literal unicyclic
profile-composition series as its complete Taylor series. -/
theorem profileSimpleCycleSeries_hasFPowerSeriesAt_unicyclicComposition
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w => JointSimpleCycleEGF.profileSimpleCycleSeries M.bjrModel (tau w))
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.mk
          (unicyclicProfileCompositionCoeff M.bjrModel
            (oneDimensionalPowerSeries p)))) 0 := by
  have htau0 : tau 0 = 0 := by
    have h := hp.coeff_zero (1 : Fin 0 → ℂ)
    have h' : p.coeff 0 = tau 0 := by
      simpa only [FormalMultilinearSeries.coeff] using h
    exact h'.symm.trans hp0
  have hcycleAt : AnalyticAt ℂ
      (JointSimpleCycleEGF.profileSimpleCycleSeries M.bjrModel) (tau 0) := by
    rw [htau0]
    exact FiniteIrreducibleProfileSimpleCyclePowerSeries.profileSimpleCycleSeries_analyticOnNhd_unitBall
      M hM 0 (by simpa only [Metric.mem_ball, dist_self] using (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨pFull, hpFull⟩ := hcycleAt.comp_of_eq hp.analyticAt rfl
  have hcoeff : ∀ k : ℕ,
      pFull.coeff k = unicyclicProfileCompositionCoeff M.bjrModel
        (oneDimensionalPowerSeries p) k := by
    intro k
    let N : ℕ := k + 1
    let Q : PowerSeries ℂ :=
      ∑ n ∈ Finset.range N,
        (((n + 3).factorial : ℂ)⁻¹) •
          ∑ H : {H : SimpleGraph (Fin (n + 3)) //
              IsAdmissibleAttachmentCore (n + 3) 0 H},
            fixedCoreProfileCompositionSeries M.bjrModel
              (oneDimensionalPowerSeries p) H.1
    let pN : FormalMultilinearSeries ℂ ℂ ℂ :=
      ∑ n ∈ Finset.range N,
        oneDimensionalFormalMultilinearSeries
          ((((n + 3).factorial : ℂ)⁻¹) •
            ∑ H : {H : SimpleGraph (Fin (n + 3)) //
                IsAdmissibleAttachmentCore (n + 3) 0 H},
              fixedCoreProfileCompositionSeries M.bjrModel
                (oneDimensionalPowerSeries p) H.1)
    have hpN : HasFPowerSeriesAt
        (fun w ↦ ∑ n ∈ Finset.range N,
          JointSimpleCycleEGF.profileSimpleCycleTerm M.bjrModel (tau w) n)
        pN 0 := by
      simpa only [N, pN] using
        profileSimpleCycleSeries_partialSum_hasFPowerSeriesAt_fixedCoreSum M.bjrModel N hp hp0
    have hdiff := hpFull.sub hpN
    have htail :=
      FiniteIrreducibleJointSimpleCycleTail.profileSimpleCycleSeries_sub_partialSum_isBigO
        M hM N hp hp0
    have hzero : (pFull - pN).coeff k = 0 :=
      hdiff.coeff_eq_zero_of_isBigO_norm_pow htail (by dsimp [N]; omega)
    have hpNEq : pN = oneDimensionalFormalMultilinearSeries Q := by
      dsimp only [pN, Q]
      exact (oneDimensionalFormalMultilinearSeries_map_finset_sum
        (Finset.range N)
        (fun n ↦ (((n + 3).factorial : ℂ)⁻¹) •
          ∑ H : {H : SimpleGraph (Fin (n + 3)) //
              IsAdmissibleAttachmentCore (n + 3) 0 H},
            fixedCoreProfileCompositionSeries M.bjrModel
              (oneDimensionalPowerSeries p) H.1)).symm
    have hpNcoeff : pN.coeff k =
        unicyclicProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p) k := by
      have hQ := coeff_finite_cycle_sum_eq_unicyclicProfileCompositionCoeff M.bjrModel (oneDimensionalPowerSeries p) k
      rw [hpNEq, oneDimensionalFormalMultilinearSeries_coeff]
      simpa only [Q, N] using hQ
    change pFull.coeff k - pN.coeff k = 0 at hzero
    exact (sub_eq_zero.mp hzero).trans hpNcoeff
  have hpower : oneDimensionalPowerSeries pFull =
      PowerSeries.mk
        (unicyclicProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p)) := by
    apply PowerSeries.ext
    intro k
    simp only [oneDimensionalPowerSeries_coeff, PowerSeries.coeff_mk,
      hcoeff]
  have hpFullEq : pFull =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.mk
          (unicyclicProfileCompositionCoeff M.bjrModel
            (oneDimensionalPowerSeries p))) := by
    calc
      pFull = oneDimensionalFormalMultilinearSeries
          (oneDimensionalPowerSeries pFull) :=
        (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
          pFull).symm
      _ = _ := by rw [hpower]
  rw [← hpFullEq]
  exact hpFull

/-- Along any actual analytic field-rooted tree branch at activity zero, the
Taylor coefficients of the full simple-cycle series are the genuine
field-weighted connected unicyclic graph weights with labelled-EGF
normalization. -/
theorem profileSimpleCycleSeries_hasFPowerSeriesAt_connectedWeights
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) (psi : ℂ × C(S, ℂ) → C(S, ℂ))
    (hpsi : AnalyticAt ℂ psi (0, g))
    (hpsi0 : psi (0, g) = 0)
    (hres : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M.bjrModel ((z, g), psi (z, g)) = 0) :
    HasFPowerSeriesAt
      (fun w => JointSimpleCycleEGF.profileSimpleCycleSeries M.bjrModel (psi (w, g)))
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.mk (fun k =>
          M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ)))) 0 := by
  obtain ⟨p, hp, -, hpSeries⟩ :=
    FieldRootedTree.branch_taylorSeries_eq_series M.bjrModel g psi hpsi hpsi0 hres
  have hp0 : p.coeff 0 = 0 := by
    rw [← oneDimensionalPowerSeries_coeff p 0, hpSeries]
    exact FieldRootedTree.series_coeff_zero M.bjrModel g
  have hcycle :=
    profileSimpleCycleSeries_hasFPowerSeriesAt_unicyclicComposition
      M hM hp hp0
  have hpower :
      PowerSeries.mk
          (unicyclicProfileCompositionCoeff M.bjrModel
            (oneDimensionalPowerSeries p)) =
        PowerSeries.mk (fun k =>
          M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ)) := by
    apply PowerSeries.ext
    intro k
    simp only [PowerSeries.coeff_mk, hpSeries]
    exact (complexFieldConnectedWeight_div_factorial_eq_unicyclicProfileCompositionCoeff M.bjrModel g k).symm
  rw [hpower] at hcycle
  exact hcycle

end PerronWright.FiniteIrreducibleUnicyclicFullTaylor
