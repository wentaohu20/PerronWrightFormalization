import PerronWright.Enumeration.UnicyclicFixedLengthAnalytic

/-!
# Finite cycle-length truncations of the unicyclic profile series

The infinite cycle-length sum is deliberately not taken here.  For every
finite cutoff, the already proved fixed-length Taylor realizations can be
summed without any convergence input.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem hasFPowerSeriesAt_finset_sum_local
    {ι A : Type*} [DecidableEq ι]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (s : Finset ι) (f : ι → ℂ → A)
    (p : ι → FormalMultilinearSeries ℂ ℂ A)
    (hp : ∀ i ∈ s, HasFPowerSeriesAt (f i) (p i) 0) :
    HasFPowerSeriesAt (fun z ↦ ∑ i ∈ s, f i z)
      (∑ i ∈ s, p i) 0 := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, constFormalMultilinearSeries_zero] using
        (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ)
          (F := A) (c := 0) (e := 0))
  | @insert i s hi ih =>
      have hiPower := hp i (Finset.mem_insert_self i s)
      have hsPower := ih (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))
      have hadd := hiPower.add hsPower
      have hfun :
          (f i) + (fun z ↦ ∑ j ∈ s, f j z) =
            fun z ↦ ∑ j ∈ insert i s, f j z := by
        funext z
        simp only [Pi.add_apply, Finset.sum_insert hi]
      rw [hfun] at hadd
      simpa only [Finset.sum_insert hi] using hadd

/-- Every finite initial segment of the actual simple-cycle profile series
has as Taylor series the corresponding finite sum of labelled fixed-core
profile-composition series.  No interchange of infinite sums is used. -/
theorem profileSimpleCycleSeries_partialSum_hasFPowerSeriesAt_fixedCoreSum
    (M : CompactBJRModel S) (N : ℕ)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ ∑ n ∈ Finset.range N,
        JointSimpleCycleEGF.profileSimpleCycleTerm M (tau w) n)
      (∑ n ∈ Finset.range N,
        oneDimensionalFormalMultilinearSeries
          ((((n + 3).factorial : ℂ)⁻¹) •
            ∑ H : {H : SimpleGraph (Fin (n + 3)) //
                IsAdmissibleAttachmentCore (n + 3) 0 H},
              fixedCoreProfileCompositionSeries M
                (oneDimensionalPowerSeries p) H.1)) 0 := by
  classical
  apply hasFPowerSeriesAt_finset_sum_local
  intro n hn
  simpa only [Nat.add_sub_cancel] using
    (profileSimpleCycleTerm_hasFPowerSeriesAt_fixedCoreSum
      M (q := n + 3) (by omega) hp hp0)

end GraphCore
end PerronWright
