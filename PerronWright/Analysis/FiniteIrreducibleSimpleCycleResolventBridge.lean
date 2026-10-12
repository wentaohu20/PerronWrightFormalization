import PerronWright.Analysis.FiniteIrreducibleMarkedCycleSingularity

/-!
# Actual finite simple-cycle resolvent corrections

Deleting the true length-one loop and length-two double-edge terms from the
literal finite marked-cycle pairing leaves the derivative continuation of
simple cycles of length at least three. Its residue is exactly -1/(2X).
This alone is not yet an identification with the original unicyclic EGF.
-/

open MeasureTheory PerronWright
open scoped Topology
noncomputable section

namespace PerronWright.FiniteIrreducibleSimpleCycleResolventBridge

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (scalarIntegralCLM operatorKernelize pathOperator pathOperator_analytic)
end MPR

namespace MCS
export PerronWright.FiniteIrreducibleMarkedCycleSingularity
  (jointProfileVertical jointProfileVertical_analytic
   cycleResolventDerivative exists_cycleResolventDerivative_regularPart)
end MCS

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev PathEnd (S : Type*) [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S] :=
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

private def kernelProfilePairing (M : FiniteIrreducibleModel S)
    (k : C(S × S, ℂ)) (v : C(S, ℂ)) : ℂ :=
  MPR.scalarIntegralCLM M (diagonalRestrictionCLM k * v)

private theorem kernelProfilePairing_analytic
    (M : FiniteIrreducibleModel S) {k : C(S, ℂ) × ℂ → C(S × S, ℂ)}
    {v : C(S, ℂ) × ℂ → C(S, ℂ)}
    (hk : AnalyticAt ℂ k (0, 0)) (hv : AnalyticAt ℂ v (0, 0)) :
    AnalyticAt ℂ (fun q => kernelProfilePairing M (k q) (v q)) (0, 0) := by
  have hdiag : AnalyticAt ℂ
      (fun q => diagonalRestrictionCLM (k q)) (0, 0) :=
    (diagonalRestrictionCLM (S := S)).analyticAt _ |>.comp hk
  exact (MPR.scalarIntegralCLM M).analyticAt _ |>.comp (hdiag.mul hv)

/-- The length-one (loop) term in the raw marked-cycle derivative. -/
def lengthOneCorrection (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  kernelProfilePairing M
    (MPR.operatorKernelize M (1 : PathEnd S))
    (MCS.jointProfileVertical M hM q)

theorem lengthOneCorrection_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    AnalyticAt ℂ (lengthOneCorrection M hM) (0, 0) := by
  apply kernelProfilePairing_analytic M analyticAt_const
  exact MCS.jointProfileVertical_analytic M hM

/-- The length-two double-edge term in the raw marked-cycle derivative. -/
def lengthTwoCorrection (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  kernelProfilePairing M
    (MPR.operatorKernelize M (MPR.pathOperator M hM q))
    (MCS.jointProfileVertical M hM q)

theorem lengthTwoCorrection_analytic (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
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
def simpleCycleDerivativeContinuation (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (q : C(S, ℂ) × ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (MCS.cycleResolventDerivative M hM q -
      lengthOneCorrection M hM q - lengthTwoCorrection M hM q)

/-- The finite-length corrections are analytic, so the exact pole of the
candidate simple-cycle derivative continuation is `-1/(2X)`.  This theorem
asserts only the singular continuation, not yet its equality with the joint
complex direct simple-cycle EGF. -/
theorem exists_simpleCycleDerivativeContinuation_regularPart
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
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
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
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



end PerronWright.FiniteIrreducibleSimpleCycleResolventBridge
