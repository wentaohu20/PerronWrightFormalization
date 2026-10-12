import PerronWright.SimpleCyclePrimitive
import PerronWright.Analysis.MarkedCycleSingularity
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Direct simple cycles and the marked-cycle resolvent derivative

This module fixes the normalization without invoking a Fredholm
determinant.  For a fixed real kernel, it differentiates the direct
simple-cycle trace series term by term and identifies the result with one
half of the raw cycle-resolvent trace series after deleting its length-one
and length-two terms.

For the actual joint compact-BJR fold, the same two finite terms are defined
directly from the marked-path kernel.  They are jointly analytic, so the
already proved residue `-1` of the raw marked-cycle derivative becomes the
exact residue `-1/2` of the simple-cycle derivative continuation.  No claim
that this continuation already equals the joint complex simple-cycle EGF is
made here; that last identity requires a separate profile-series bridge.
-/

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.SimpleCycleResolventBridge

namespace KC

export PerronWright.KernelCycle
  (cycleTrace norm_cycleTrace_le simpleUnicyclicTermC unicyclicTermC
   simpleUnicyclicSeriesC)

end KC

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM operatorKernelize pathOperator pathOperator_analytic)

end MPR

namespace MCS

export PerronWright.MarkedCycleSingularity
  (jointProfileVertical jointProfileVertical_analytic
   cycleResolventDerivative exists_cycleResolventDerivative_regularPart)

end MCS

/-! ## The fixed-kernel direct trace identity -/

section FixedKernel

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The scalar trace term in the raw resolvent expansion.  Index `n`
corresponds to the trace of the `(n+1)`-st kernel power. -/
def rawCycleTraceTerm (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) (n : ℕ) : ℂ :=
  w ^ n * (KC.cycleTrace mu a n : ℂ)

/-- The raw cycle-resolvent trace series. -/
def rawCycleTraceSeries (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) : ℂ :=
  ∑' n : ℕ, rawCycleTraceTerm mu a w n

private theorem summable_rawCycleTraceTerm
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    Summable (rawCycleTraceTerm mu a w) := by
  let c : ℝ := mu.real Set.univ * ‖a‖
  let q : ℝ := r * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by simpa [q, c, mul_assoc] using hsubcritical
  have hmajor : Summable (fun n : ℕ => c * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left c
  apply Summable.of_norm_bounded hmajor
  intro n
  calc
    ‖rawCycleTraceTerm mu a w n‖ =
        ‖w‖ ^ n * ‖KC.cycleTrace mu a n‖ := by
          simp [rawCycleTraceTerm, norm_pow]
    _ ≤ r ^ n * c ^ (n + 1) := by
      gcongr
      exact KC.norm_cycleTrace_le mu a n
    _ = c * q ^ n := by dsimp [q]; ring

private def simpleCycleDerivativeTerm
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 3) * w ^ (n + 2) *
      (KC.cycleTrace mu a (n + 2) : ℂ) /
    ((2 : ℂ) * ((n : ℂ) + 3))

omit [BorelSpace S] in
@[simp] private theorem simpleCycleDerivativeTerm_eq_half
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) (n : ℕ) :
    simpleCycleDerivativeTerm mu a w n =
      (1 / 2 : ℂ) * w ^ (n + 2) *
        (KC.cycleTrace mu a (n + 2) : ℂ) := by
  unfold simpleCycleDerivativeTerm
  have hn : (n : ℂ) + 3 ≠ 0 := by
    exact_mod_cast (by omega : n + 3 ≠ 0)
  have hden : (2 : ℂ) * ((n : ℂ) + 3) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hn
  have hratio :
      (((n : ℂ) + 3) / ((2 : ℂ) * ((n : ℂ) + 3))) = 1 / 2 := by
    apply (div_eq_iff hden).2
    ring
  calc
    (((n : ℂ) + 3) * w ^ (n + 2) *
          (KC.cycleTrace mu a (n + 2) : ℂ)) /
        ((2 : ℂ) * ((n : ℂ) + 3)) =
      ((((n : ℂ) + 3) /
          ((2 : ℂ) * ((n : ℂ) + 3))) *
        w ^ (n + 2) * (KC.cycleTrace mu a (n + 2) : ℂ)) := by ring
    _ = (1 / 2 : ℂ) * w ^ (n + 2) *
        (KC.cycleTrace mu a (n + 2) : ℂ) := by rw [hratio]

omit [BorelSpace S] in
private theorem simpleUnicyclicTermC_hasDerivAt'
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (n : ℕ) (w : ℂ) :
    HasDerivAt (fun z : ℂ => KC.simpleUnicyclicTermC mu a z n)
      (simpleCycleDerivativeTerm mu a w n) w := by
  have hpow : n + 1 + 2 = n + 3 := by omega
  have htrace : n + 1 + 1 = n + 2 := by omega
  have hderiv : n + 3 - 1 = n + 2 := by omega
  have hthree : (1 : ℂ) + 2 = 3 := by norm_num
  have h := ((((hasDerivAt_id w).pow (n + 3)).mul_const
    (KC.cycleTrace mu a (n + 2) : ℂ)).div_const
      ((2 : ℂ) * ((n : ℂ) + 3)))
  simpa [KC.simpleUnicyclicTermC, KC.unicyclicTermC,
    simpleCycleDerivativeTerm, hpow, htrace, hderiv, hthree, add_assoc] using h

omit [BorelSpace S] in
private theorem summable_simpleCycleDerivativeMajorant
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1) :
    Summable (fun n : ℕ =>
      ((mu.real Set.univ * ‖a‖) ^ 3 * r ^ 2 / 2) *
        (r * mu.real Set.univ * ‖a‖) ^ n) := by
  exact (summable_geometric_of_lt_one
    (by positivity : 0 ≤ r * mu.real Set.univ * ‖a‖)
    hsubcritical).mul_left _

private theorem norm_simpleCycleDerivativeTerm_le
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 ≤ r) (w : ℂ) (hw : ‖w‖ < r) (n : ℕ) :
    ‖simpleCycleDerivativeTerm mu a w n‖ ≤
      ((mu.real Set.univ * ‖a‖) ^ 3 * r ^ 2 / 2) *
        (r * mu.real Set.univ * ‖a‖) ^ n := by
  rw [simpleCycleDerivativeTerm_eq_half]
  have htrace := KC.norm_cycleTrace_le mu a (n + 2)
  rw [norm_mul, norm_mul, norm_div, norm_one]
  norm_num
  calc
    (1 / 2 : ℝ) * ‖w‖ ^ (n + 2) *
          |KC.cycleTrace mu a (n + 2)|
        ≤ (1 / 2 : ℝ) * r ^ (n + 2) *
          (mu.real Set.univ * ‖a‖) ^ (n + 3) := by
      gcongr
      simpa [Real.norm_eq_abs] using htrace
    _ = ((mu.real Set.univ * ‖a‖) ^ 3 * r ^ 2 / 2) *
        (r * mu.real Set.univ * ‖a‖) ^ n := by ring

private theorem simpleCycleSeries_deriv_eq_tsum
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 < r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ < r) :
    deriv (KC.simpleUnicyclicSeriesC mu a) w =
      ∑' n : ℕ, simpleCycleDerivativeTerm mu a w n := by
  let u : ℕ → ℝ := fun n =>
    ((mu.real Set.univ * ‖a‖) ^ 3 * r ^ 2 / 2) *
      (r * mu.real Set.univ * ‖a‖) ^ n
  have hu : Summable u :=
    summable_simpleCycleDerivativeMajorant mu a r hr.le hsubcritical
  have hterm : ∀ n z, z ∈ Metric.ball (0 : ℂ) r →
      HasDerivAt (fun y : ℂ => KC.simpleUnicyclicTermC mu a y n)
        (simpleCycleDerivativeTerm mu a z n) z := by
    intro n z hz
    exact simpleUnicyclicTermC_hasDerivAt' mu a n z
  have hbound : ∀ n z, z ∈ Metric.ball (0 : ℂ) r →
      ‖simpleCycleDerivativeTerm mu a z n‖ ≤ u n := by
    intro n z hz
    exact norm_simpleCycleDerivativeTerm_le mu a r hr.le z
      (by simpa [Metric.mem_ball, dist_zero_right] using hz) n
  have hzero : Summable (fun n : ℕ => KC.simpleUnicyclicTermC mu a 0 n) := by
    simp [KC.simpleUnicyclicTermC, KC.unicyclicTermC]
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu
    Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    hterm hbound (Metric.mem_ball_self hr) hzero
    (show w ∈ Metric.ball (0 : ℂ) r by
      simpa [Metric.mem_ball, dist_zero_right] using hw)
  exact hderiv.deriv

private theorem rawCycleTraceSeries_tail_two
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    rawCycleTraceSeries mu a w -
        (KC.cycleTrace mu a 0 : ℂ) -
        w * (KC.cycleTrace mu a 1 : ℂ) =
      ∑' n : ℕ, w ^ (n + 2) *
        (KC.cycleTrace mu a (n + 2) : ℂ) := by
  let f : ℕ → ℂ := rawCycleTraceTerm mu a w
  have hf : Summable f := summable_rawCycleTraceTerm mu a r hr hsubcritical w hw
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hfinite : ∑ i ∈ Finset.range 2, f i =
      (KC.cycleTrace mu a 0 : ℂ) +
        w * (KC.cycleTrace mu a 1 : ℂ) := by
    norm_num [f, rawCycleTraceTerm, Finset.sum_range_succ]
  change (∑' n : ℕ, f n) - _ - _ = _
  calc
    (∑' n : ℕ, f n) -
          (KC.cycleTrace mu a 0 : ℂ) -
          w * (KC.cycleTrace mu a 1 : ℂ) =
        ∑' n : ℕ, f (n + 2) := by
      rw [← hsplit]
      rw [hfinite]
      ring
    _ = ∑' n : ℕ, w ^ (n + 2) *
          (KC.cycleTrace mu a (n + 2) : ℂ) := by
      apply tsum_congr
      intro n
      rfl

private theorem tsum_simpleCycleDerivativeTerm_eq_half_tail
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    (∑' n : ℕ, simpleCycleDerivativeTerm mu a w n) =
      (1 / 2 : ℂ) *
        (rawCycleTraceSeries mu a w -
          (KC.cycleTrace mu a 0 : ℂ) -
          w * (KC.cycleTrace mu a 1 : ℂ)) := by
  rw [rawCycleTraceSeries_tail_two mu a r hr hsubcritical w hw]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [simpleCycleDerivativeTerm_eq_half]
  ring

/-- Exact fixed-kernel normalization: the derivative of the direct simple
cycle series is one half of the raw resolvent-trace series, with both its
length-one and length-two terms removed. -/
theorem deriv_simpleUnicyclicSeriesC_eq_rawCycleTraceSeries_corrections
    (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (r : ℝ) (hr : 0 < r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ < r) :
    deriv (KC.simpleUnicyclicSeriesC mu a) w =
      (1 / 2 : ℂ) *
        (rawCycleTraceSeries mu a w -
          (KC.cycleTrace mu a 0 : ℂ) -
          w * (KC.cycleTrace mu a 1 : ℂ)) := by
  rw [simpleCycleSeries_deriv_eq_tsum mu a r hr hsubcritical w hw]
  exact tsum_simpleCycleDerivativeTerm_eq_half_tail
    mu a r hr.le hsubcritical w hw.le

end FixedKernel

/-! ## The actual joint fold: analytic finite-length corrections -/

section JointFold

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev PathEnd (S : Type*) [MetricSpace S] [CompactSpace S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

/- Match the operator-space structures used by `MarkedPathResolvent`; this
avoids the bounded-convergence/op-norm topology diamond when composing its
analytic operator family with `operatorKernelize`. -/
local instance pathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance pathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance pathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance pathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance pathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance pathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private def diagonalMap : C(S, S × S) :=
  ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

private def diagonalRestrictionCLM : C(S × S, ℂ) →L[ℂ] C(S, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ diagonalMap

private def kernelProfilePairing (M : CompactBJRModel S)
    (k : C(S × S, ℂ)) (v : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M (diagonalRestrictionCLM k * v)

private theorem kernelProfilePairing_analytic
    (M : CompactBJRModel S) {k : C(S, ℂ) × ℂ → C(S × S, ℂ)}
    {v : C(S, ℂ) × ℂ → C(S, ℂ)}
    (hk : AnalyticAt ℂ k (0, 0)) (hv : AnalyticAt ℂ v (0, 0)) :
    AnalyticAt ℂ (fun q => kernelProfilePairing M (k q) (v q)) (0, 0) := by
  have hdiag : AnalyticAt ℂ
      (fun q => diagonalRestrictionCLM (k q)) (0, 0) :=
    (diagonalRestrictionCLM (S := S)).analyticAt _ |>.comp hk
  exact (MPR.scalarIntegralCLM M).analyticAt _ |>.comp (hdiag.mul hv)

/-- The length-one (loop) term in the raw marked-cycle derivative. -/
def lengthOneCorrection (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  kernelProfilePairing M
    (MPR.operatorKernelize M (1 : PathEnd S))
    (MCS.jointProfileVertical M hM q)

theorem lengthOneCorrection_analytic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (lengthOneCorrection M hM) (0, 0) := by
  apply kernelProfilePairing_analytic M analyticAt_const
  exact MCS.jointProfileVertical_analytic M hM

/-- The length-two double-edge term in the raw marked-cycle derivative. -/
def lengthTwoCorrection (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  kernelProfilePairing M
    (MPR.operatorKernelize M (MPR.pathOperator M hM q))
    (MCS.jointProfileVertical M hM q)

theorem lengthTwoCorrection_analytic (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (lengthTwoCorrection M hM) (0, 0) := by
  have hk : AnalyticAt ℂ
      (fun q => MPR.operatorKernelize M (MPR.pathOperator M hM q))
      (0, 0) :=
    (MPR.operatorKernelize M).analyticAt _ |>.comp
      (MPR.pathOperator_analytic M hM)
  exact kernelProfilePairing_analytic M hk
    (MCS.jointProfileVertical_analytic M hM)

/-- Candidate simple-cycle derivative continuation obtained directly from
the marked-path resolvent, after deleting cycles of lengths one and two. -/
def simpleCycleDerivativeContinuation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (MCS.cycleResolventDerivative M hM q -
      lengthOneCorrection M hM q - lengthTwoCorrection M hM q)

/-- The finite-length corrections are analytic, so the exact pole of the
candidate simple-cycle derivative continuation is `-1/(2X)`.  This theorem
asserts only the singular continuation, not yet its equality with the joint
complex direct simple-cycle EGF. -/
theorem exists_simpleCycleDerivativeContinuation_regularPart
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ B : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ B (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0), q.2 ≠ 0 →
        simpleCycleDerivativeContinuation M hM q =
          -(1 / 2 : ℂ) * q.2⁻¹ + B q := by
  obtain ⟨A, hAa, hsplit⟩ :=
    MCS.exists_cycleResolventDerivative_regularPart M hM
  let B : C(S, ℂ) × ℂ → ℂ := fun q =>
    (1 / 2 : ℂ) *
      (A q - lengthOneCorrection M hM q - lengthTwoCorrection M hM q)
  have hBa : AnalyticAt ℂ B (0, 0) :=
    analyticAt_const.mul
      ((hAa.sub (lengthOneCorrection_analytic M hM)).sub
        (lengthTwoCorrection_analytic M hM))
  refine ⟨B, hBa, ?_⟩
  filter_upwards [hsplit] with q hq
  intro hX
  rw [simpleCycleDerivativeContinuation, hq hX]
  dsimp [B]
  ring

/-- The analytic part of the simple-cycle derivative continuation has a
normalized joint primitive.  On any later chosen punctured logarithmic
sheet, adding `-(1/2) log X` to this primitive produces a local primitive of
the continuation; no logarithm is postulated in this theorem. -/
theorem exists_simpleCycleDerivativeContinuation_regularPrimitive
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ B H : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ B (0, 0) ∧
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0), q.2 ≠ 0 →
        simpleCycleDerivativeContinuation M hM q =
          -(1 / 2 : ℂ) * q.2⁻¹ + B q) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in nhds (0, 0),
        (fderiv ℂ H q) (0, 1) = B q := by
  obtain ⟨B, hBa, hsplit⟩ :=
    exists_simpleCycleDerivativeContinuation_regularPart M hM
  obtain ⟨H, hHa, hHaxis, hHderiv⟩ :=
    AnalyticVerticalPrimitive.analytic_vertical_primitive hBa
  exact ⟨B, H, hBa, hHa, hHaxis, hsplit, hHderiv⟩

end JointFold

end PerronWright.SimpleCycleResolventBridge
