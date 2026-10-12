import PerronWright.Enumeration.UnicyclicFixedCoreAnalytic
import PerronWright.Enumeration.UnicyclicCycleWeightTrace

/-!
# Analytic realization at one fixed cycle length

For a fixed `q ≥ 3`, the admissible surplus-zero cores form a finite type.
This file sums the fixed-core analytic realizations over that finite type and
uses the proved cycle-core weight/trace identity to identify the resulting
analytic function with `profileSimpleCycleTerm`.  No infinite sum over cycle
lengths occurs here.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem hasFPowerSeriesAt_finset_sum
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

/-- At one fixed cycle length, the actual simple-cycle trace term has the
finite sum of literal fixed-core profile compositions as its Taylor series.
The factor `q!⁻¹` is exactly the labelled-EGF normalization. -/
theorem profileSimpleCycleTerm_hasFPowerSeriesAt_fixedCoreSum
    (M : CompactBJRModel S) {q : ℕ} (hq : 3 ≤ q)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ JointSimpleCycleEGF.profileSimpleCycleTerm
        M (tau w) (q - 3))
      (oneDimensionalFormalMultilinearSeries
        (((q.factorial : ℂ)⁻¹) •
          ∑ H : {H : SimpleGraph (Fin q) //
              IsAdmissibleAttachmentCore q 0 H},
            fixedCoreProfileCompositionSeries M
              (oneDimensionalPowerSeries p) H.1)) 0 := by
  classical
  let Core := {H : SimpleGraph (Fin q) //
    IsAdmissibleAttachmentCore q 0 H}
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
  have hsumRaw := hasFPowerSeriesAt_finset_sum
    (Finset.univ : Finset Core)
    (fun H w ↦ finiteComplexGraphWeight M (tau w) H.1)
    (fun H ↦ oneDimensionalFormalMultilinearSeries (F H))
    (fun H _ ↦ hcore H)
  have hsum :
      HasFPowerSeriesAt
        (fun w ↦ ∑ H : Core,
          finiteComplexGraphWeight M (tau w) H.1)
        (oneDimensionalFormalMultilinearSeries (∑ H : Core, F H)) 0 := by
    simpa only [oneDimensionalFormalMultilinearSeries_map_finset_sum] using
      hsumRaw
  let c : ℂ := (q.factorial : ℂ)⁻¹
  have hscaled := hsum.const_smul (c := c)
  have hfun :
      c • (fun w ↦ ∑ H : Core,
        finiteComplexGraphWeight M (tau w) H.1) =
        fun w ↦ JointSimpleCycleEGF.profileSimpleCycleTerm
          M (tau w) (q - 3) := by
    funext w
    change c * (∑ H : Core,
      finiteComplexGraphWeight M (tau w) H.1) = _
    simpa only [c, div_eq_mul_inv, mul_comm] using
      sum_admissibleAttachmentCore_zero_div_factorial_eq_profileSimpleCycleTerm
        M (tau w) hq
  have hseries :
      c • oneDimensionalFormalMultilinearSeries (∑ H : Core, F H) =
        oneDimensionalFormalMultilinearSeries
          (c • ∑ H : Core, F H) :=
    oneDimensionalFormalMultilinearSeries_map_smul c (∑ H : Core, F H)
  rw [hfun, hseries] at hscaled
  simpa only [c, Core, F] using hscaled

end GraphCore
end PerronWright
