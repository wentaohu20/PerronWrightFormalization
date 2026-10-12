import PerronWright.Enumeration.CubicActualAdmissibleCoefficientBridge
import PerronWright.Enumeration.UnicyclicFixedCoreAnalytic

/-!
# Fixed-degree analyticity of the positive-surplus cubic profile coefficient

For a fixed excess degree `d`, the admissible cubic profile coefficient is a
finite sum over the genuine cubic admissible cores on `2 * ell + d` labelled
vertices.  The fixed-core analytic realization therefore supplies its exact
one-dimensional formal power series after division by the labelled-EGF
factorial.

The auxiliary point of the type space required by the kernel-presentation
bridge is chosen internally from the nonzero probability measure.  It does
not occur in either the function or its formal power series.
-/

open MeasureTheory
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal fixed-degree cubic profile-composition power series.  It is
the finite sum over actual cubic admissible cores, with the exact
labelled-EGF factorial normalization. -/
def positiveSurplusCubicFixedDegreeProfileSeries
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell d : ℕ) : PowerSeries ℂ :=
  let k := 2 * ell + d
  ((k.factorial : ℂ)⁻¹) •
    ∑ G : CubicAdmissibleAttachmentCore k ell,
      fixedCoreProfileCompositionSeries M T G.1

private theorem hasFPowerSeriesAt_finset_sum_cubicFixedDegree
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

/-- For every fixed internal-length degree, the genuine admissible cubic
profile coefficient has the finite sum of actual fixed-core composition
series as its exact Taylor series. -/
theorem positiveSurplusCubicAdmissibleProfileCoefficient_hasFPowerSeriesAt
    (M : CompactBJRModel S) {ell d : ℕ} (hell : 0 < ell)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusCubicAdmissibleProfileCoefficient
        M (tau w) ell d)
      (oneDimensionalFormalMultilinearSeries
        (positiveSurplusCubicFixedDegreeProfileSeries M
          (oneDimensionalPowerSeries p) ell d)) 0 := by
  classical
  let k := 2 * ell + d
  let Core := CubicAdmissibleAttachmentCore k ell
  let F : Core → PowerSeries ℂ := fun G ↦
    fixedCoreProfileCompositionSeries M
      (oneDimensionalPowerSeries p) G.1
  have hcore : ∀ G : Core,
      HasFPowerSeriesAt
        (fun w ↦ finiteComplexGraphWeight M (tau w) G.1)
        (oneDimensionalFormalMultilinearSeries (F G)) 0 := by
    intro G
    exact finiteComplexGraphWeight_hasFPowerSeriesAt_profileComposition
      M G.1 hp hp0
  have hsumRaw := hasFPowerSeriesAt_finset_sum_cubicFixedDegree
    (Finset.univ : Finset Core)
    (fun G w ↦ finiteComplexGraphWeight M (tau w) G.1)
    (fun G ↦ oneDimensionalFormalMultilinearSeries (F G))
    (fun G _ ↦ hcore G)
  have hsum :
      HasFPowerSeriesAt
        (fun w ↦ ∑ G : Core,
          finiteComplexGraphWeight M (tau w) G.1)
        (oneDimensionalFormalMultilinearSeries (∑ G : Core, F G)) 0 := by
    simpa only [oneDimensionalFormalMultilinearSeries_map_finset_sum] using
      hsumRaw
  let c : ℂ := (k.factorial : ℂ)⁻¹
  have hscaled := hsum.const_smul (c := c)
  have hSuniv : (Set.univ : Set S).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero (μ := M.mu) (by simp)
  let s₀ : S := hSuniv.some
  have hfun :
      c • (fun w ↦ ∑ G : Core,
        finiteComplexGraphWeight M (tau w) G.1) =
        fun w ↦ positiveSurplusCubicAdmissibleProfileCoefficient
          M (tau w) ell d := by
    funext w
    change c * (∑ G : Core,
      finiteComplexGraphWeight M (tau w) G.1) = _
    have hbridge :=
      fixedSurplusCubicCoreProfileCoeff_div_factorial_eq_admissibleProfile
        M (tau w) (ell := ell) (d := d) hell s₀
    rw [fixedSurplusCubicCoreProfileCoeff_X_mul_C_eq_coreWeightSum]
      at hbridge
    simpa only [c, k, Core, div_eq_mul_inv, mul_comm] using hbridge
  have hseries :
      c • oneDimensionalFormalMultilinearSeries (∑ G : Core, F G) =
        oneDimensionalFormalMultilinearSeries
          (c • ∑ G : Core, F G) :=
    oneDimensionalFormalMultilinearSeries_map_smul c (∑ G : Core, F G)
  rw [hfun, hseries] at hscaled
  simpa only [positiveSurplusCubicFixedDegreeProfileSeries, c, k, Core, F]
    using hscaled

/-- A finite range of fixed degrees may be summed without any convergence
argument; its Taylor series is the corresponding finite sum of the exact
fixed-degree cubic core series. -/
theorem positiveSurplusCubicAdmissibleProfileCoefficient_partialSum_hasFPowerSeriesAt
    (M : CompactBJRModel S) {ell : ℕ} (hell : 0 < ell) (N : ℕ)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ ∑ d ∈ Finset.range N,
        positiveSurplusCubicAdmissibleProfileCoefficient M (tau w) ell d)
      (∑ d ∈ Finset.range N,
        oneDimensionalFormalMultilinearSeries
          (positiveSurplusCubicFixedDegreeProfileSeries M
            (oneDimensionalPowerSeries p) ell d)) 0 := by
  classical
  apply hasFPowerSeriesAt_finset_sum_cubicFixedDegree
  intro d _
  exact positiveSurplusCubicAdmissibleProfileCoefficient_hasFPowerSeriesAt
    M hell hp hp0

end PerronWright.GraphCore
