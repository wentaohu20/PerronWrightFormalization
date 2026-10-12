import PerronWright.Analysis.FiniteIrreducibleCubicProfileAnalytic
import PerronWright.Enumeration.PositiveSurplusCubicFixedDegreeAnalytic
import PerronWright.Analysis.FiniteIrreducibleCubicTailOrder
import PerronWright.Enumeration.PositiveSurplusCubicCoefficientReindex
import PerronWright.Analysis.AnalyticCoeffOrder

/-!
# The complete Taylor series of the positive-surplus cubic profile functional

This module combines the analytic finite inclusion--exclusion realization,
the exact fixed-degree Taylor series, the genuine infinite-tail estimate,
and the shifted cubic-core reindexing.  It identifies every Taylor
coefficient of the literal admissible cubic profile sum with the cubic part
of the fixed-surplus profile-composition coefficient.
-/

open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal positive-surplus cubic profile series has exactly the cubic
fixed-surplus profile-composition coefficients as its complete Taylor
series along every analytic one-variable profile germ with zero constant
term. -/
theorem positiveSurplusCubicProfileSeries_hasFPowerSeriesAt_cubicComposition
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusCubicProfileSeries M ell (tau w))
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.mk
          (cubicFixedSurplusProfileCompositionCoeff M.bjrModel
            (oneDimensionalPowerSeries p) ell))) 0 := by
  have htau0 : tau 0 = 0 := by
    have h := hp.coeff_zero (1 : Fin 0 → ℂ)
    have h' : p.coeff 0 = tau 0 := by
      simpa only [FormalMultilinearSeries.coeff] using h
    exact h'.symm.trans hp0
  have hfullAnalytic : AnalyticAt ℂ
      (fun w ↦ positiveSurplusCubicProfileSeries M ell (tau w)) 0 :=
    (positiveSurplusCubicProfileSeries_analyticAt_zero M hM ell).comp_of_eq
      hp.analyticAt htau0
  obtain ⟨pFull, hpFull⟩ := hfullAnalytic
  have hcoeff : ∀ k : ℕ,
      pFull.coeff k = cubicFixedSurplusProfileCompositionCoeff M.bjrModel
        (oneDimensionalPowerSeries p) ell k := by
    intro k
    let N : ℕ := k + 1
    let Q : PowerSeries ℂ :=
      ∑ d ∈ Finset.range N,
        positiveSurplusCubicFixedDegreeProfileSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell d
    let pN : FormalMultilinearSeries ℂ ℂ ℂ :=
      ∑ d ∈ Finset.range N,
        oneDimensionalFormalMultilinearSeries
          (positiveSurplusCubicFixedDegreeProfileSeries M.bjrModel
            (oneDimensionalPowerSeries p) ell d)
    have hpN : HasFPowerSeriesAt
        (fun w ↦ ∑ d ∈ Finset.range N,
          positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell d)
        pN 0 := by
      simpa only [N, pN] using
        positiveSurplusCubicAdmissibleProfileCoefficient_partialSum_hasFPowerSeriesAt M.bjrModel hell N hp hp0
    have hdiff := hpFull.sub hpN
    have htail :=
      positiveSurplusCubicProfileSeries_sub_partialSum_isBigO
        M hM hell N hp hp0
    have hzero : (pFull - pN).coeff k = 0 :=
      hdiff.coeff_eq_zero_of_isBigO_norm_pow htail
        (by dsimp only [N]; omega)
    have hpNEq : pN = oneDimensionalFormalMultilinearSeries Q := by
      dsimp only [pN, Q]
      exact (oneDimensionalFormalMultilinearSeries_map_finset_sum
        (Finset.range N)
        (fun d ↦ positiveSurplusCubicFixedDegreeProfileSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell d)).symm
    have hpNcoeff : pN.coeff k =
        cubicFixedSurplusProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p) ell k := by
      have hQ :=
        coeff_finite_cubic_core_sum_eq_cubicFixedSurplusProfileCompositionCoeff M.bjrModel (oneDimensionalPowerSeries p) hell k
      rw [hpNEq, oneDimensionalFormalMultilinearSeries_coeff]
      simpa only [Q, N, positiveSurplusCubicFixedDegreeProfileSeries] using hQ
    change pFull.coeff k - pN.coeff k = 0 at hzero
    exact (sub_eq_zero.mp hzero).trans hpNcoeff
  have hpower : oneDimensionalPowerSeries pFull =
      PowerSeries.mk
        (cubicFixedSurplusProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p) ell) := by
    apply PowerSeries.ext
    intro k
    simp only [oneDimensionalPowerSeries_coeff, PowerSeries.coeff_mk,
      hcoeff]
  have hpFullEq : pFull =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.mk
          (cubicFixedSurplusProfileCompositionCoeff M.bjrModel
            (oneDimensionalPowerSeries p) ell)) := by
    calc
      pFull = oneDimensionalFormalMultilinearSeries
          (oneDimensionalPowerSeries pFull) :=
        (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
          pFull).symm
      _ = _ := by rw [hpower]
  rw [← hpFullEq]
  exact hpFull

end PerronWright.FiniteIrreducibleKernelAmplitude
