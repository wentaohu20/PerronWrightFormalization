import PerronWright.Enumeration.FixedSurplusCubicNoncubicSplit
import PerronWright.Enumeration.UnicyclicFixedCoreAnalytic

/-!
# Analytic realization of the fixed-size noncubic core sum

The fixed-core realization proved in `UnicyclicFixedCoreAnalytic` is in fact
independent of surplus and of the cycle classification: it applies to every
finite simple graph.  Consequently, at one fixed core size, it can be summed
over all noncubic admissible cores of any fixed surplus.

This file records that finite analytic bridge.  It intentionally does not
sum over unbounded core sizes.  Such a sum is precisely where suppression of
degree-two paths and the bounded-kernel resolvent product are required.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Noncubic admissible ordered cores of one fixed size and surplus. -/
abbrev NoncubicAdmissibleAttachmentCore (q ell : ℕ) :=
  {H : SimpleGraph (Fin q) //
    IsNoncubicAdmissibleAttachmentCore q ell H}

/-- Actual finite sum of profile weights over all noncubic admissible cores
of one fixed size. -/
def fixedSurplusNoncubicCoreWeightSum
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell q : ℕ) : ℂ :=
  ∑ H : NoncubicAdmissibleAttachmentCore q ell,
    finiteComplexGraphWeight M tau H.1

/-- Formal profile-composition series corresponding to the preceding
fixed-size noncubic core sum. -/
def fixedSurplusNoncubicCoreProfileSeries
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q : ℕ) : PowerSeries ℂ :=
  ∑ H : NoncubicAdmissibleAttachmentCore q ell,
    fixedCoreProfileCompositionSeries M T H.1

private theorem hasFPowerSeriesAt_finset_sum_noncubic
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

/-- At each fixed core size, the actual noncubic finite sum has exactly the
sum of the literal fixed-core profile-composition series as its Taylor
series.  No surplus-zero property is used. -/
theorem fixedSurplusNoncubicCoreWeightSum_hasFPowerSeriesAt
    (M : CompactBJRModel S) (ell q : ℕ)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ fixedSurplusNoncubicCoreWeightSum M (tau w) ell q)
      (oneDimensionalFormalMultilinearSeries
        (fixedSurplusNoncubicCoreProfileSeries M
          (oneDimensionalPowerSeries p) ell q)) 0 := by
  classical
  let Core := NoncubicAdmissibleAttachmentCore q ell
  let F : Core → PowerSeries ℂ := fun H ↦
    fixedCoreProfileCompositionSeries M
      (oneDimensionalPowerSeries p) H.1
  have hcore : ∀ H : Core,
      HasFPowerSeriesAt
        (fun w ↦ finiteComplexGraphWeight M (tau w) H.1)
        (oneDimensionalFormalMultilinearSeries (F H)) 0 := by
    intro H
    exact finiteComplexGraphWeight_hasFPowerSeriesAt_profileComposition
      M H.1 hp hp0
  have hsumRaw := hasFPowerSeriesAt_finset_sum_noncubic
    (Finset.univ : Finset Core)
    (fun H w ↦ finiteComplexGraphWeight M (tau w) H.1)
    (fun H ↦ oneDimensionalFormalMultilinearSeries (F H))
    (fun H _ ↦ hcore H)
  simpa only [fixedSurplusNoncubicCoreWeightSum,
    fixedSurplusNoncubicCoreProfileSeries, Core, F,
    oneDimensionalFormalMultilinearSeries_map_finset_sum] using hsumRaw

end GraphCore
end PerronWright
