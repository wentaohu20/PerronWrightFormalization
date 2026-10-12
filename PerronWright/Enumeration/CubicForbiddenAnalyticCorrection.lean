import PerronWright.Enumeration.PositiveSurplusCubicIntegratedAmplitude
import PerronWright.Analysis.AnalyticVerticalDivision

/-!
# Analytic forbidden-pattern correction for cubic kernels

The unrestricted product of cubic path resolvents includes length
assignments which do not reconstruct a simple graph.  The finite witness
type in `CubicKernelForbiddenLengthCorrection` detects exactly those
assignments.  Here we apply finite inclusion--exclusion to intersections of
these witness events.

For one nonempty witness pattern, at least one edge length is fixed.  Its
pole-removed edge factor is therefore `X` times a fixed-length analytic path
kernel, while every unfixed edge uses the existing normalized resolvent
kernel.  Consequently every normalized forbidden intersection, and hence
their inclusion--exclusion sum, is jointly analytic and vanishes on the
whole horizontal slice `X = 0`.  Banach-valued vertical analytic division
then gives an explicit analytic factor `X`, with no additional hypothesis.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Finite forbidden patterns and their forced edge lengths -/

@[instance_reducible] noncomputable def cubicKernelShortLoopWitnessFintype
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype (CubicKernelShortLoopWitness H) := by
  apply Fintype.ofInjective (fun w ↦ (w.edge, w.length))
  intro a b h
  cases a
  cases b
  cases h
  rfl

@[instance_reducible] noncomputable def cubicKernelRepeatedZeroWitnessFintype
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype (CubicKernelRepeatedZeroWitness H) := by
  apply Fintype.ofInjective (fun w ↦ (w.first, w.second))
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- The witness type is genuinely finite; no orbit or compactness interface
is used here. -/
@[instance_reducible] noncomputable def cubicKernelForbiddenLengthWitnessFintype
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype (CubicKernelForbiddenLengthWitness H) := by
  letI := cubicKernelShortLoopWitnessFintype H
  letI := cubicKernelRepeatedZeroWitnessFintype H
  infer_instance

/-- The finite set of lengths which one witness forces on one edge. -/
def cubicForbiddenWitnessForcedValues
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H) (e : Fin (3 * ell)) :
    Finset ℕ :=
  match w with
  | Sum.inl w => if e = w.edge then {w.length.val} else ∅
  | Sum.inr w => if e = w.first ∨ e = w.second then {0} else ∅

/-- All lengths forced on an edge by an intersection pattern. -/
noncomputable def cubicForbiddenPatternForcedValues
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H))
    (e : Fin (3 * ell)) : Finset ℕ := by
  classical
  exact J.biUnion (fun w ↦ cubicForbiddenWitnessForcedValues w e)

/-- A witness intersection is compatible exactly when it never forces two
different lengths on the same edge. -/
def CubicForbiddenPatternCompatible
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H)) : Prop :=
  ∀ e, (cubicForbiddenPatternForcedValues J e).card ≤ 1

/-- Whether a pattern fixes the length of this edge. -/
def CubicForbiddenPatternForcesEdge
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H))
    (e : Fin (3 * ell)) : Prop :=
  (cubicForbiddenPatternForcedValues J e).Nonempty

/-- The unique forced length when the pattern is compatible and the edge is
forced.  Outside that case the default value is irrelevant. -/
noncomputable def cubicForbiddenPatternLength
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H))
    (e : Fin (3 * ell)) : ℕ :=
  if h : (cubicForbiddenPatternForcedValues J e).Nonempty then
    (cubicForbiddenPatternForcedValues J e).min' h
  else 0

private def cubicForbiddenWitnessAnchorEdge
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H) : Fin (3 * ell) :=
  match w with
  | Sum.inl w => w.edge
  | Sum.inr w => w.first

private def cubicForbiddenWitnessAnchorLength
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H) : ℕ :=
  match w with
  | Sum.inl w => w.length.val
  | Sum.inr _ => 0

private theorem cubicForbiddenWitnessAnchorLength_mem
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H) :
    cubicForbiddenWitnessAnchorLength w ∈
      cubicForbiddenWitnessForcedValues w
        (cubicForbiddenWitnessAnchorEdge w) := by
  rcases w with w | w
  · simp [cubicForbiddenWitnessAnchorLength,
      cubicForbiddenWitnessAnchorEdge, cubicForbiddenWitnessForcedValues]
  · simp [cubicForbiddenWitnessAnchorLength,
      cubicForbiddenWitnessAnchorEdge, cubicForbiddenWitnessForcedValues]

/-- Every nonempty witness intersection fixes at least one edge. -/
theorem cubicForbiddenPattern_exists_forcedEdge
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    {J : Finset (CubicKernelForbiddenLengthWitness H)}
    (hJ : J.Nonempty) :
    ∃ e : Fin (3 * ell), CubicForbiddenPatternForcesEdge J e := by
  classical
  obtain ⟨w, hw⟩ := hJ
  refine ⟨cubicForbiddenWitnessAnchorEdge w, ?_⟩
  unfold CubicForbiddenPatternForcesEdge cubicForbiddenPatternForcedValues
  refine ⟨cubicForbiddenWitnessAnchorLength w, ?_⟩
  exact Finset.mem_biUnion.mpr
    ⟨w, hw, cubicForbiddenWitnessAnchorLength_mem w⟩

/-! ## Analytic fixed-length edge kernels -/

/-- Kernel of one fixed path length along the joint fold chart. -/
def cubicFixedLengthPathKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (n : ℕ) (q : C(S, ℂ) × ℂ) : C(S × S, ℂ) :=
  PerronWright.MarkedPathResolvent.operatorKernelize M
    ((PerronWright.MarkedPathResolvent.pathOperator M hM q) ^ n)

theorem cubicFixedLengthPathKernel_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (n : ℕ) :
    AnalyticAt ℂ (cubicFixedLengthPathKernel M hM n) (0, 0) := by
  unfold cubicFixedLengthPathKernel
  exact (PerronWright.MarkedPathResolvent.operatorKernelize M).analyticAt _
    |>.comp_of_eq
      ((PerronWright.MarkedPathResolvent.pathOperator_analytic M hM).pow n) rfl

@[simp] theorem cubicFixedLengthPathKernel_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (n : ℕ) (q : C(S, ℂ) × ℂ) (a b : S) :
    cubicFixedLengthPathKernel M hM n q (a, b) =
      profilePathEdgeCoefficient M
        (PerronWright.MarkedPathResolvent.profile M hM q) a b n := by
  rfl

private def cubicForbiddenEdgeCoordinateMap {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C((Fin (2 * ell) → S), S × S) :=
  ⟨fun x ↦
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2),
    (continuous_apply (cubicKernelOrderedEndpoints K.graph e).1).prodMk
      (continuous_apply (cubicKernelOrderedEndpoints K.graph e).2)⟩

private def cubicForbiddenEdgePullbackCLM {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C(S × S, ℂ) →L[ℂ] C((Fin (2 * ell) → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (cubicForbiddenEdgeCoordinateMap K e)

/-- A fixed-length kernel pulled back to all cubic branch coordinates. -/
def cubicFixedLengthEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (n : ℕ) (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  cubicForbiddenEdgePullbackCLM K e
    (cubicFixedLengthPathKernel M hM n q)

theorem cubicFixedLengthEdgeFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (n : ℕ) :
    AnalyticAt ℂ (cubicFixedLengthEdgeFunction M hM K e n) (0, 0) := by
  unfold cubicFixedLengthEdgeFunction
  exact (cubicForbiddenEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (cubicFixedLengthPathKernel_analytic M hM n) rfl

/-- On a strict-subcritical profile ball the whole continuous-function
sequence of fixed-length edge kernels is absolutely summable. -/
theorem cubicFixedLengthEdgeFunction_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖PerronWright.MarkedPathResolvent.profile M hM q y‖ ≤ r) :
    Summable (fun n : ℕ ↦ cubicFixedLengthEdgeFunction M hM K e n q) := by
  have hs := summable_profilePathEdgeCoefficientKernel M hM
    (PerronWright.MarkedPathResolvent.profile M hM q)
    r hr hr1 hprofile
  change Summable (fun n : ℕ ↦ cubicForbiddenEdgePullbackCLM K e
    (profilePathEdgeCoefficientKernel M
      (PerronWright.MarkedPathResolvent.profile M hM q) n))
  refine (hs.map (cubicForbiddenEdgePullbackCLM K e)
    (cubicForbiddenEdgePullbackCLM K e).continuous).congr ?_
  intro n
  rfl

@[simp] theorem cubicFixedLengthEdgeFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (n : ℕ) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) :
    cubicFixedLengthEdgeFunction M hM K e n q x =
      profilePathEdgeCoefficient M
        (PerronWright.MarkedPathResolvent.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n := by
  rfl

/-! ## One normalized forbidden intersection -/

/-- Edge factor in a pole-removed witness intersection.  A forced edge gets
the explicit factor `X`; an unforced edge retains the existing normalized
resolvent factor. -/
def cubicForbiddenNormalizedPatternEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternForcesEdge J e then
    q.2 • cubicFixedLengthEdgeFunction M hM K e
      (cubicForbiddenPatternLength J e) q
  else
    cubicForbiddenEdgePullbackCLM K e
      (boundedNormalizedPathKernel M hM q)

theorem cubicForbiddenNormalizedPatternEdgeFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) :
    AnalyticAt ℂ
      (cubicForbiddenNormalizedPatternEdgeFunction M hM K J e) (0, 0) := by
  classical
  unfold cubicForbiddenNormalizedPatternEdgeFunction
  split_ifs with he
  · exact analyticAt_snd.smul
      (cubicFixedLengthEdgeFunction_analytic M hM K e
        (cubicForbiddenPatternLength J e))
  · exact (cubicForbiddenEdgePullbackCLM K e).analyticAt _ |>.comp
      (boundedNormalizedPathKernel_analytic M hM)

/-- Continuous-function-valued normalized intersection cylinder.  An
incompatible collection of forced values has empty intersection and is
represented by zero. -/
def cubicForbiddenNormalizedIntersectionFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternCompatible J then
    cubicKernelBranchProfileFunction M hM (ell := ell) q *
      ∏ e : Fin (3 * ell),
        cubicForbiddenNormalizedPatternEdgeFunction M hM K J e q
  else 0

theorem cubicForbiddenNormalizedIntersectionFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
    AnalyticAt ℂ
      (cubicForbiddenNormalizedIntersectionFunction M hM K J) (0, 0) := by
  classical
  unfold cubicForbiddenNormalizedIntersectionFunction
  split_ifs
  · apply (cubicKernelBranchProfileFunction_analytic M hM ell).mul
    exact (Finset.univ : Finset (Fin (3 * ell))).analyticAt_fun_prod
      (fun e _ ↦
        cubicForbiddenNormalizedPatternEdgeFunction_analytic M hM K J e)
  · exact analyticAt_const

/-- Every nonempty normalized intersection vanishes identically on the
horizontal field slice `X = 0`. -/
theorem cubicForbiddenNormalizedIntersectionFunction_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (hJ : J.Nonempty) (g : C(S, ℂ)) :
    cubicForbiddenNormalizedIntersectionFunction M hM K J (g, 0) = 0 := by
  classical
  by_cases hcompat : CubicForbiddenPatternCompatible J
  · obtain ⟨e, he⟩ := cubicForbiddenPattern_exists_forcedEdge hJ
    have hedge :
        cubicForbiddenNormalizedPatternEdgeFunction M hM K J e (g, 0) = 0 := by
      simp [cubicForbiddenNormalizedPatternEdgeFunction, he]
    unfold cubicForbiddenNormalizedIntersectionFunction
    rw [if_pos hcompat]
    rw [Finset.prod_eq_zero (Finset.mem_univ e) hedge]
    simp
  · simp [cubicForbiddenNormalizedIntersectionFunction, hcompat]

/-- Integrated normalized intersection cylinder. -/
def cubicKernelIntegratedForbiddenIntersection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelIntegralCLM M ell
    (cubicForbiddenNormalizedIntersectionFunction M hM K J q)

theorem cubicKernelIntegratedForbiddenIntersection_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
    AnalyticAt ℂ (cubicKernelIntegratedForbiddenIntersection M hM K J)
      (0, 0) :=
  (cubicKernelIntegralCLM M ell).analyticAt _ |>.comp
    (cubicForbiddenNormalizedIntersectionFunction_analytic M hM K J)

theorem cubicKernelIntegratedForbiddenIntersection_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (hJ : J.Nonempty) (g : C(S, ℂ)) :
    cubicKernelIntegratedForbiddenIntersection M hM K J (g, 0) = 0 := by
  unfold cubicKernelIntegratedForbiddenIntersection
  rw [cubicForbiddenNormalizedIntersectionFunction_axis M hM K J hJ g]
  exact map_zero (cubicKernelIntegralCLM M ell)

/-! ## Inclusion--exclusion correction and the extra `X` -/

/-- Finite inclusion--exclusion sum of all nonempty forbidden witness
intersections for one labelled cubic kernel. -/
def cubicKernelIntegratedForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ := by
  letI := cubicKernelForbiddenLengthWitnessFintype K.graph
  exact Finset.sum
    ((Finset.univ :
      Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
        Finset.Nonempty)
    (fun J ↦ (-1 : ℂ) ^ (J.card + 1) *
      cubicKernelIntegratedForbiddenIntersection M hM K J q)

theorem cubicKernelIntegratedForbiddenCorrection_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    AnalyticAt ℂ (cubicKernelIntegratedForbiddenCorrection M hM K)
      (0, 0) := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  unfold cubicKernelIntegratedForbiddenCorrection
  let s := (Finset.univ :
    Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
      Finset.Nonempty
  let F : Finset (CubicKernelForbiddenLengthWitness K.graph) →
      (C(S, ℂ) × ℂ → ℂ) := fun J q ↦
    (-1 : ℂ) ^ (J.card + 1) *
      cubicKernelIntegratedForbiddenIntersection M hM K J q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ J ∈ s, F J q) (0, 0)
  have hsum : AnalyticAt ℂ (∑ J ∈ s, F J) (0, 0) := by
    apply Finset.analyticAt_sum
    intro J hJ
    exact analyticAt_const.mul
      (cubicKernelIntegratedForbiddenIntersection_analytic M hM K J)
  have hfun : (∑ J ∈ s, F J) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ J ∈ s, F J q) := by
    funext q
    exact Finset.sum_apply q s F
  rw [← hfun]
  exact hsum

theorem cubicKernelIntegratedForbiddenCorrection_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (g : C(S, ℂ)) :
    cubicKernelIntegratedForbiddenCorrection M hM K (g, 0) = 0 := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  unfold cubicKernelIntegratedForbiddenCorrection
  apply Finset.sum_eq_zero
  intro J hJ
  have hne : J.Nonempty := by
    have hmem : J ⊆ Finset.univ ∧ J.Nonempty := by
      simpa only [Finset.mem_filter, Finset.mem_powerset] using hJ
    exact hmem.2
  rw [cubicKernelIntegratedForbiddenIntersection_axis M hM K J hne g,
    mul_zero]

/-- The forbidden correction has one extra factor of the fold coordinate.
The analytic remainder is produced by the proved Banach-valued vertical
division theorem, not postulated as an interface. -/
theorem cubicKernelIntegratedForbiddenCorrection_eq_X_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    ∃ R : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ R (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        cubicKernelIntegratedForbiddenCorrection M hM K q = q.2 * R q := by
  obtain ⟨R, hRa, hR⟩ :=
    PerronWright.AnalyticVerticalDivision.analytic_vertical_division_smul
      (cubicKernelIntegratedForbiddenCorrection_analytic M hM K)
      (Filter.Eventually.of_forall
        (cubicKernelIntegratedForbiddenCorrection_axis M hM K))
  refine ⟨R, hRa, ?_⟩
  filter_upwards [hR] with q hq
  simpa only [smul_eq_mul] using hq

/-! ## Punctured interpretation of the inclusion--exclusion cylinders -/

/-- Raw edge factor in a forbidden intersection: a forced edge has its
fixed-length kernel, while an unforced edge has the full path resolvent. -/
def cubicForbiddenRawPatternEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ) :
    C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternForcesEdge J e then
    cubicFixedLengthEdgeFunction M hM K e
      (cubicForbiddenPatternLength J e) q
  else
    cubicForbiddenEdgePullbackCLM K e
      (CKRA_MPR.pathResolventKernel M hM q)

/-- On the punctured germ, every normalized pattern edge is `X` times its
raw fixed-length/resolvent factor. -/
theorem cubicForbiddenNormalizedPatternEdgeFunction_eq_X_smul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicForbiddenNormalizedPatternEdgeFunction M hM K J e q =
        q.2 • cubicForbiddenRawPatternEdgeFunction M hM K J e q := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · simp [cubicForbiddenNormalizedPatternEdgeFunction,
      cubicForbiddenRawPatternEdgeFunction, he]
  · unfold cubicForbiddenNormalizedPatternEdgeFunction
      cubicForbiddenRawPatternEdgeFunction
    rw [if_neg he, if_neg he]
    exact congrArg (cubicForbiddenEdgePullbackCLM K e) (hq hX)

/-- Raw continuous-function-valued intersection cylinder. -/
def cubicForbiddenRawIntersectionFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) : C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternCompatible J then
    cubicKernelBranchProfileFunction M hM (ell := ell) q *
      ∏ e : Fin (3 * ell),
        cubicForbiddenRawPatternEdgeFunction M hM K J e q
  else 0

/-- A normalized intersection is `X ^ (3 * ell)` times its raw cylinder on
the punctured germ. -/
theorem cubicForbiddenNormalizedIntersectionFunction_eq_pow_smul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicForbiddenNormalizedIntersectionFunction M hM K J q =
        q.2 ^ (3 * ell) •
          cubicForbiddenRawIntersectionFunction M hM K J q := by
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ e : Fin (3 * ell), q.2 ≠ 0 →
          cubicForbiddenNormalizedPatternEdgeFunction M hM K J e q =
            q.2 • cubicForbiddenRawPatternEdgeFunction M hM K J e q := by
    rw [Filter.eventually_all]
    intro e
    exact cubicForbiddenNormalizedPatternEdgeFunction_eq_X_smul_raw
      M hM K J e
  filter_upwards [hall] with q hq
  intro hX
  classical
  by_cases hcompat : CubicForbiddenPatternCompatible J
  · unfold cubicForbiddenNormalizedIntersectionFunction
      cubicForbiddenRawIntersectionFunction
    rw [if_pos hcompat, if_pos hcompat]
    have hprod :
        (∏ e : Fin (3 * ell),
            cubicForbiddenNormalizedPatternEdgeFunction M hM K J e q) =
          q.2 ^ (3 * ell) •
            ∏ e : Fin (3 * ell),
              cubicForbiddenRawPatternEdgeFunction M hM K J e q := by
      ext x
      simp only [ContinuousMap.prod_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      have hedge (e : Fin (3 * ell)) := congrArg
        (fun f : C((Fin (2 * ell) → S), ℂ) ↦ f x) (hq e hX)
      simp only [ContinuousMap.smul_apply, smul_eq_mul] at hedge
      simp_rw [hedge]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    ring
  · simp [cubicForbiddenNormalizedIntersectionFunction,
      cubicForbiddenRawIntersectionFunction, hcompat]

/-- Integrated raw intersection cylinder. -/
def cubicKernelIntegratedRawForbiddenIntersection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelIntegralCLM M ell
    (cubicForbiddenRawIntersectionFunction M hM K J q)

theorem cubicKernelIntegratedForbiddenIntersection_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelIntegratedForbiddenIntersection M hM K J q =
        q.2 ^ (3 * ell) *
          cubicKernelIntegratedRawForbiddenIntersection M hM K J q := by
  filter_upwards
    [cubicForbiddenNormalizedIntersectionFunction_eq_pow_smul_raw
      M hM K J] with q hq
  intro hX
  unfold cubicKernelIntegratedForbiddenIntersection
    cubicKernelIntegratedRawForbiddenIntersection
  rw [hq hX, map_smul]
  simp only [smul_eq_mul]

/-- Raw inclusion--exclusion correction for one labelled cubic kernel. -/
def cubicKernelIntegratedRawForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ := by
  letI := cubicKernelForbiddenLengthWitnessFintype K.graph
  exact Finset.sum
    ((Finset.univ :
      Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
        Finset.Nonempty)
    (fun J ↦ (-1 : ℂ) ^ (J.card + 1) *
      cubicKernelIntegratedRawForbiddenIntersection M hM K J q)

/-- The pole-removed inclusion--exclusion correction is exactly the cubic
power times its raw counterpart on the punctured germ. -/
theorem cubicKernelIntegratedForbiddenCorrection_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelIntegratedForbiddenCorrection M hM K q =
        q.2 ^ (3 * ell) *
          cubicKernelIntegratedRawForbiddenCorrection M hM K q := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ J : Finset (CubicKernelForbiddenLengthWitness K.graph),
          q.2 ≠ 0 →
          cubicKernelIntegratedForbiddenIntersection M hM K J q =
            q.2 ^ (3 * ell) *
              cubicKernelIntegratedRawForbiddenIntersection M hM K J q := by
    rw [Filter.eventually_all]
    intro J
    exact cubicKernelIntegratedForbiddenIntersection_eq_pow_mul_raw
      M hM K J
  filter_upwards [hall] with q hq
  intro hX
  unfold cubicKernelIntegratedForbiddenCorrection
    cubicKernelIntegratedRawForbiddenCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [hq J hX]
  ring

/-! ## Global correction and the admissible cubic singular function -/

/-- Exact inverse-multiplicity sum of the analytic forbidden corrections. -/
def positiveSurplusCubicForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedForbiddenCorrection M hM K q

theorem positiveSurplusCubicForbiddenCorrection_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusCubicForbiddenCorrection M hM ell)
      (0, 0) := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicForbiddenCorrection
  let F : LabelledConnectedCubicKernel ell →
      (C(S, ℂ) × ℂ → ℂ) := fun K q ↦
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedForbiddenCorrection M hM K q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) (0, 0)
  have hsum : AnalyticAt ℂ (∑ K, F K) (0, 0) := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (cubicKernelIntegratedForbiddenCorrection_analytic M hM K)
  have hfun : (∑ K, F K) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) := by
    funext q
    exact Fintype.sum_apply q F
  rw [← hfun]
  exact hsum

theorem positiveSurplusCubicForbiddenCorrection_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (g : C(S, ℂ)) :
    positiveSurplusCubicForbiddenCorrection M hM ell (g, 0) = 0 := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicForbiddenCorrection
  apply Finset.sum_eq_zero
  intro K _
  rw [cubicKernelIntegratedForbiddenCorrection_axis M hM K g, mul_zero]

/-- The complete forbidden contribution loses at least one cubic pole. -/
theorem positiveSurplusCubicForbiddenCorrection_eq_X_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    ∃ R : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ R (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        positiveSurplusCubicForbiddenCorrection M hM ell q = q.2 * R q := by
  obtain ⟨R, hRa, hR⟩ :=
    PerronWright.AnalyticVerticalDivision.analytic_vertical_division_smul
      (positiveSurplusCubicForbiddenCorrection_analytic M hM ell)
      (Filter.Eventually.of_forall
        (positiveSurplusCubicForbiddenCorrection_axis M hM ell))
  refine ⟨R, hRa, ?_⟩
  filter_upwards [hR] with q hq
  simpa only [smul_eq_mul] using hq

/-- Exact inverse-multiplicity sum of the raw forbidden corrections. -/
def positiveSurplusCubicRawForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedRawForbiddenCorrection M hM K q

theorem positiveSurplusCubicForbiddenCorrection_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      positiveSurplusCubicForbiddenCorrection M hM ell q =
        q.2 ^ (3 * ell) *
          positiveSurplusCubicRawForbiddenCorrection M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ K : LabelledConnectedCubicKernel ell, q.2 ≠ 0 →
          cubicKernelIntegratedForbiddenCorrection M hM K q =
            q.2 ^ (3 * ell) *
              cubicKernelIntegratedRawForbiddenCorrection M hM K q := by
    rw [Filter.eventually_all]
    intro K
    exact cubicKernelIntegratedForbiddenCorrection_eq_pow_mul_raw M hM K
  filter_upwards [hall] with q hq
  intro hX
  unfold positiveSurplusCubicForbiddenCorrection
    positiveSurplusCubicRawForbiddenCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [hq K hX]
  ring

/-- Pole-removed admissible cubic amplitude: unrestricted analytic amplitude
minus the explicit inclusion--exclusion correction. -/
def positiveSurplusCubicAdmissibleIntegratedAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  positiveSurplusCubicIntegratedAmplitude M hM ell q -
    positiveSurplusCubicForbiddenCorrection M hM ell q

theorem positiveSurplusCubicAdmissibleIntegratedAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    AnalyticAt ℂ
      (positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell)
      (0, 0) :=
  (positiveSurplusCubicIntegratedAmplitude_analytic M hM ell).sub
    (positiveSurplusCubicForbiddenCorrection_analytic M hM ell)

theorem positiveSurplusCubicAdmissibleIntegratedAmplitude_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell (0, 0) =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  rw [positiveSurplusCubicAdmissibleIntegratedAmplitude,
    positiveSurplusCubicForbiddenCorrection_axis,
    sub_zero, positiveSurplusCubicIntegratedAmplitude_base]

/-- Raw admissible cubic resolvent sum obtained by the same exact
inclusion--exclusion subtraction. -/
def positiveSurplusCubicAdmissibleResolventSum
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  positiveSurplusCubicIntegratedResolventSum M hM ell q -
    positiveSurplusCubicRawForbiddenCorrection M hM ell q

/-- Exact local singular representation of the admissible cubic sum. -/
theorem positiveSurplusCubicAdmissibleIntegratedAmplitude_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell q =
        q.2 ^ (3 * ell) *
          positiveSurplusCubicAdmissibleResolventSum M hM ell q := by
  filter_upwards
    [positiveSurplusCubicIntegratedAmplitude_eq_pow_mul_resolventSum M hM ell,
      positiveSurplusCubicForbiddenCorrection_eq_pow_mul_raw M hM ell]
      with q htotal hforbidden
  intro hX
  rw [positiveSurplusCubicAdmissibleIntegratedAmplitude,
    positiveSurplusCubicAdmissibleResolventSum,
    htotal hX, hforbidden hX]
  ring

/-- A no-interface local singular formula for the admissible positive-surplus
cubic contribution.  The unrestricted normalized amplitude is analytic and
has the stated EGF value at the fold point, while the entire explicit
forbidden correction is `X` times an analytic function.  Hence, on the
punctured germ, the raw admissible sum is an order-`3 * ell` pole whose
correction loses at least one singular edge factor. -/
theorem exists_positiveSurplusCubicAdmissibleSingularNumerator
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    ∃ R : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ R (0, 0) ∧
      positiveSurplusCubicIntegratedAmplitude M hM ell (0, 0) =
        positiveSurplusCubicEGFConstant ell *
          (Real.sqrt (M.beta hM) : ℂ) ^ ell ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
        positiveSurplusCubicAdmissibleResolventSum M hM ell q =
          (q.2 ^ (3 * ell))⁻¹ *
            (positiveSurplusCubicIntegratedAmplitude M hM ell q -
              q.2 * R q) := by
  obtain ⟨R, hRa, hR⟩ :=
    positiveSurplusCubicForbiddenCorrection_eq_X_mul M hM ell
  refine ⟨R, hRa, positiveSurplusCubicIntegratedAmplitude_base M hM ell, ?_⟩
  filter_upwards
    [hR,
      positiveSurplusCubicAdmissibleIntegratedAmplitude_eq_pow_mul_raw
        M hM ell]
      with q hcorrection hadmissible
  intro hX
  have hpow : q.2 ^ (3 * ell) ≠ 0 := pow_ne_zero _ hX
  calc
    positiveSurplusCubicAdmissibleResolventSum M hM ell q =
        (q.2 ^ (3 * ell))⁻¹ *
          (q.2 ^ (3 * ell) *
            positiveSurplusCubicAdmissibleResolventSum M hM ell q) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
    _ = (q.2 ^ (3 * ell))⁻¹ *
        positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell q := by
      rw [hadmissible hX]
    _ = (q.2 ^ (3 * ell))⁻¹ *
        (positiveSurplusCubicIntegratedAmplitude M hM ell q -
          q.2 * R q) := by
      rw [positiveSurplusCubicAdmissibleIntegratedAmplitude, hcorrection]

end PerronWright.GraphCore
