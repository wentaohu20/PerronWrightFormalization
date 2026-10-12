import PerronWright.Enumeration.RootedTreeSeriesPhysical
import PerronWright.Enumeration.UnicyclicFullTaylor
import PerronWright.Enumeration.ZeroFieldUnicyclicCoefficientAsymptotic

/-!
# Zero-field unicyclic coefficients are the genuine connected weights

This module identifies the Taylor coefficients entering the zero-field
unicyclic singularity analysis with the labelled connected-graph weights.
The proof matches the local analytic tree branch used by the full unicyclic
Taylor theorem with the canonical rooted-tree Taylor sum.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright.ZeroFieldUnicyclicConnectedWeight

namespace ZF

export PerronWright.ZeroFieldUnicyclicSingularity
  (zeroFieldUnicyclicEGF)

end ZF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def zeroFieldLine :
    ℂ →L[ℂ] ℂ × C(S, ℂ) :=
  ContinuousLinearMap.inl ℂ ℂ C(S, ℂ)

/-- In one scalar variable, the formal series obtained from an ordinary
power series is the standard scalar formal multilinear series. -/
private theorem oneDimensionalFormalMultilinearSeries_mk_eq_ofScalars
    (c : ℕ → ℂ) :
    oneDimensionalFormalMultilinearSeries (PowerSeries.mk c) =
      FormalMultilinearSeries.ofScalars ℂ c := by
  have hpower :
      oneDimensionalPowerSeries
          (FormalMultilinearSeries.ofScalars ℂ c) =
        PowerSeries.mk c := by
    apply PowerSeries.ext
    intro n
    simp only [oneDimensionalPowerSeries_coeff,
      FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_mk]
  rw [← hpower]
  exact oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
    (FormalMultilinearSeries.ofScalars ℂ c)

/-- The genuine zero-field unicyclic EGF has, at the origin, the labelled
connected unicyclic weights divided by the vertex factorial as its complete
formal power series. -/
theorem zeroFieldUnicyclicEGF_hasFPowerSeriesAt_connectedWeights
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    HasFPowerSeriesAt (ZF.zeroFieldUnicyclicEGF M)
      (FormalMultilinearSeries.ofScalars ℂ (fun k ↦
        M.complexFieldConnectedWeight (0 : C(S, ℂ)) k 1 /
          (k.factorial : ℂ))) 0 := by
  obtain ⟨psi, hpsi, hpsi0, hres, hp⟩ :=
    M.exists_zeroTreeBranch_with_canonicalTaylorSeries

  have hline : ∀ᶠ z in nhds (0 : ℂ),
      TreeCritical.residual M
        ((z, (0 : C(S, ℂ))), psi (z, 0)) = 0 := by
    have ht : Filter.Tendsto (zeroFieldLine (S := S))
        (nhds (0 : ℂ))
        (nhds ((0 : ℂ), (0 : C(S, ℂ)))) := by
      have hz : zeroFieldLine (S := S) (0 : ℂ) =
          ((0 : ℂ), (0 : C(S, ℂ))) := by
        rw [map_zero]
        apply Prod.ext <;> rfl
      rw [← hz]
      exact (zeroFieldLine (S := S)).continuous.continuousAt
    simpa only [zeroFieldLine, ContinuousLinearMap.inl_apply, map_zero]
      using ht.eventually hres

  have hcycle :=
    GraphCore.profileSimpleCycleSeries_hasFPowerSeriesAt_connectedWeights
      M hM (0 : C(S, ℂ)) psi hpsi hpsi0 hline

  have hRadius : (1 : ℝ≥0∞) ≤
      M.complexTypeRootedTreeFMS.radius :=
    M.one_le_complexTypeRootedTreeFMS_radius
  have hRadiusPos : 0 < M.complexTypeRootedTreeFMS.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hRadius
  have hseries : HasFPowerSeriesAt M.rootedTreeSeries
      M.complexTypeRootedTreeFMS 0 := by
    change HasFPowerSeriesAt M.complexTypeRootedTreeFMS.sum
      M.complexTypeRootedTreeFMS 0
    exact (M.complexTypeRootedTreeFMS.hasFPowerSeriesOnBall
      hRadiusPos).hasFPowerSeriesAt
  have htreeEq : Filter.EventuallyEq (nhds (0 : ℂ))
      (fun z : ℂ ↦ psi (z, 0)) M.rootedTreeSeries := by
    filter_upwards [hp.eventually_hasSum_sub,
      hseries.eventually_hasSum_sub] with z hpsiSum htreeSum
    exact hpsiSum.unique htreeSum
  have hcycleEq : Filter.EventuallyEq (nhds (0 : ℂ))
      (fun z : ℂ ↦
        JointSimpleCycleEGF.profileSimpleCycleSeries M (psi (z, 0)))
      (ZF.zeroFieldUnicyclicEGF M) := by
    filter_upwards [htreeEq] with z hz
    simp only [ZF.zeroFieldUnicyclicEGF, hz]

  have hzero := hcycle.congr hcycleEq
  rw [oneDimensionalFormalMultilinearSeries_mk_eq_ofScalars] at hzero
  exact hzero

/-- Exact identification of each zero-field unicyclic Taylor coefficient
with the corresponding labelled connected weight. -/
theorem zeroFieldUnicyclic_taylorCoefficient_eq_connectedWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (k : ℕ) :
    Transfer.taylorCoefficient (ZF.zeroFieldUnicyclicEGF M) k =
      M.complexFieldConnectedWeight (0 : C(S, ℂ)) k 1 /
        (k.factorial : ℂ) :=
  Transfer.taylorCoefficient_eq_seriesCoefficient
    (zeroFieldUnicyclicEGF_hasFPowerSeriesAt_connectedWeights M hM) k

/-- The explicit Wright coefficient estimate, now stated directly for the
actual zero-field connected unicyclic weights. -/
theorem zeroFieldUnicyclic_connectedWeight_explicit_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      M.complexFieldConnectedWeight (0 : C(S, ℂ)) n 1 /
          (n.factorial : ℂ) -
        (1 / 4 : ℂ) * (n : ℂ)⁻¹) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  simpa only [zeroFieldUnicyclic_taylorCoefficient_eq_connectedWeight M hM]
    using
      PerronWright.ZeroFieldUnicyclicCoefficientAsymptotic.zeroFieldUnicyclic_taylorCoefficient_explicit_error_isBigO
        M hM

end PerronWright.ZeroFieldUnicyclicConnectedWeight
