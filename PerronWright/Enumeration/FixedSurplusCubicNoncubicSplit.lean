import PerronWright.Enumeration.FixedSurplusCompositionCoeff
import PerronWright.Enumeration.CubicSubdivisionClassification
import PerronWright.Enumeration.KernelTotalEdges
import PerronWright.Analysis.AnalyticFiniteAmplitude

/-!
# Cubic/noncubic splitting at fixed positive surplus

This file separates the exact finite admissible-core sum into its cubic and
noncubic parts before any singularity analysis is performed.  It also turns
the intrinsic degree-excess dichotomy into the strict suppressed-edge gap

`# kernel edges < 3 * ell`

for every noncubic admissible core.  Consequently, whenever a fixed-core
contribution has already been written as `X ^ (-e)` times an analytic
amplitude, normalization by the cubic pole order leaves a genuine factor
`X` in the noncubic case.  No graph-to-amplitude representation is assumed
or introduced here.
-/

open scoped Classical ENNReal NNReal Topology
open MeasureTheory

noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- An admissible ordered core which fails the cubic branch-degree
condition.  Degree-two subdivision vertices remain part of the core. -/
def IsNoncubicAdmissibleAttachmentCore (k ell : ℕ)
    (G : SimpleGraph (Fin k)) : Prop :=
  IsAdmissibleAttachmentCore k ell G ∧
    ¬∀ v ∈ branchingVertices G, G.degree v = 3

/-- Every admissible ordered core belongs to exactly one side of the
cubic/noncubic dichotomy. -/
theorem isCubic_or_isNoncubic_of_isAdmissible
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (hG : IsAdmissibleAttachmentCore k ell G) :
    IsCubicAdmissibleAttachmentCore k ell G ∨
      IsNoncubicAdmissibleAttachmentCore k ell G := by
  classical
  by_cases hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3
  · exact Or.inl ⟨hG, hcubic⟩
  · exact Or.inr ⟨hG, hcubic⟩

/-- The cubic and noncubic alternatives are disjoint. -/
theorem not_isCubic_of_isNoncubic
    {k ell : ℕ} {G : SimpleGraph (Fin k)}
    (hG : IsNoncubicAdmissibleAttachmentCore k ell G) :
    ¬IsCubicAdmissibleAttachmentCore k ell G := by
  intro hcubic
  exact hG.2 hcubic.2

/-- A noncubic positive-surplus core has strictly fewer than the extremal
`3 * ell` suppressed kernel edges. -/
theorem kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (hG : IsNoncubicAdmissibleAttachmentCore k ell G) :
    Nat.card (KernelEdgeLabel G) < 3 * ell := by
  classical
  have hmin : ∀ v, 2 ≤ G.degree v :=
    minDegree_two_of_isTwoCore_univ hG.1.2.1
  have hs : G.edgeFinset.card = Fintype.card (Fin k) + ell := by
    simpa only [Fintype.card_fin] using hG.1.2.2
  have hle : Nat.card (KernelEdgeLabel G) ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus
      G hG.1.1 hmin hell hs
  have hne : Nat.card (KernelEdgeLabel G) ≠ 3 * ell := by
    intro heq
    have hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3 :=
      (kernelEdgeLabel_card_eq_three_surplus_iff_cubic
        G hG.1.1 hmin hell hs).mp heq
    exact hG.2 hcubic
  omega

/-- Equivalently, among admissible positive-surplus cores, failure of the
cubic condition is exactly the strict suppressed-edge gap. -/
theorem not_cubic_iff_kernelEdgeLabel_card_lt_three_surplus
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (hG : IsAdmissibleAttachmentCore k ell G) :
    (¬∀ v ∈ branchingVertices G, G.degree v = 3) ↔
      Nat.card (KernelEdgeLabel G) < 3 * ell := by
  classical
  have hmin : ∀ v, 2 ≤ G.degree v :=
    minDegree_two_of_isTwoCore_univ hG.2.1
  have hs : G.edgeFinset.card = Fintype.card (Fin k) + ell := by
    simpa only [Fintype.card_fin] using hG.2.2
  constructor
  · intro hnoncubic
    exact kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic
      hell ⟨hG, hnoncubic⟩
  · intro hlt hcubic
    have heq : Nat.card (KernelEdgeLabel G) = 3 * ell :=
      (kernelEdgeLabel_card_eq_three_surplus_iff_cubic
        G hG.1 hmin hell hs).mpr hcubic
    omega

/-- The fixed-size profile coefficient summed only over cubic admissible
ordered cores.  The ambient subtype is kept unchanged, so the splitting is
a literal finite partition and introduces no quotient or representative. -/
def fixedSurplusCubicCoreProfileCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q k : ℕ) : ℂ :=
  ∑ H : {H : SimpleGraph (Fin q) //
      IsAdmissibleAttachmentCore q ell H},
    if IsCubicAdmissibleAttachmentCore q ell H.1 then
      PowerSeries.coeff k (fixedCoreProfileCompositionSeries M T H.1)
    else 0

/-- The complementary fixed-size profile coefficient summed over
noncubic admissible ordered cores. -/
def fixedSurplusNoncubicCoreProfileCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q k : ℕ) : ℂ :=
  ∑ H : {H : SimpleGraph (Fin q) //
      IsAdmissibleAttachmentCore q ell H},
    if IsCubicAdmissibleAttachmentCore q ell H.1 then 0
    else PowerSeries.coeff k
      (fixedCoreProfileCompositionSeries M T H.1)

/-- Exact finite cubic/noncubic split at one core size. -/
theorem sum_fixedCoreProfileCompositionSeries_coeff_eq_cubic_add_noncubic
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell q k : ℕ) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q ell H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) =
      fixedSurplusCubicCoreProfileCoeff M T ell q k +
        fixedSurplusNoncubicCoreProfileCoeff M T ell q k := by
  classical
  unfold fixedSurplusCubicCoreProfileCoeff
    fixedSurplusNoncubicCoreProfileCoeff
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro H
  by_cases hH : IsCubicAdmissibleAttachmentCore q ell H.1
  · simp [hH]
  · simp [hH]

/-- The cubic part of the literal fixed-surplus rooted-profile composition
coefficient, with the same antidiagonal and factorial normalization as the
unsplit coefficient. -/
def cubicFixedSurplusProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) : ℂ :=
  ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    fixedSurplusCubicCoreProfileCoeff M T ell p.1.1 k /
      (p.1.1.factorial : ℂ)

/-- The noncubic part of the literal fixed-surplus rooted-profile
composition coefficient. -/
def noncubicFixedSurplusProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) : ℂ :=
  ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    fixedSurplusNoncubicCoreProfileCoeff M T ell p.1.1 k /
      (p.1.1.factorial : ℂ)

/-- Exact cubic/noncubic decomposition of the full fixed-surplus
composition coefficient. -/
theorem fixedSurplusProfileCompositionCoeff_eq_cubic_add_noncubic
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) :
    fixedSurplusProfileCompositionCoeff M T ell k =
      cubicFixedSurplusProfileCompositionCoeff M T ell k +
        noncubicFixedSurplusProfileCompositionCoeff M T ell k := by
  classical
  unfold fixedSurplusProfileCompositionCoeff
    cubicFixedSurplusProfileCompositionCoeff
    noncubicFixedSurplusProfileCompositionCoeff
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro p
  calc
    (∑ H : {H : SimpleGraph (Fin p.1.1) //
          IsAdmissibleAttachmentCore p.1.1 ell H},
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M T H.1)) /
          (p.1.1.factorial : ℂ) =
        (fixedSurplusCubicCoreProfileCoeff M T ell p.1.1 k +
          fixedSurplusNoncubicCoreProfileCoeff M T ell p.1.1 k) /
            (p.1.1.factorial : ℂ) := by
      rw [sum_fixedCoreProfileCompositionSeries_coeff_eq_cubic_add_noncubic]
    _ = fixedSurplusCubicCoreProfileCoeff M T ell p.1.1 k /
          (p.1.1.factorial : ℂ) +
        fixedSurplusNoncubicCoreProfileCoeff M T ell p.1.1 k /
          (p.1.1.factorial : ℂ) := by
      rw [add_div]

/-- The literal complex connected weight, after labelled-EGF
normalization, inherits the same exact cubic/noncubic decomposition. -/
theorem complexFieldConnectedWeight_div_factorial_eq_cubic_add_noncubic
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) / (k.factorial : ℂ) =
      cubicFixedSurplusProfileCompositionCoeff M
          (FieldRootedTree.series M g) ell k +
        noncubicFixedSurplusProfileCompositionCoeff M
          (FieldRootedTree.series M g) ell k := by
  rw [complexFieldConnectedWeight_div_factorial_eq_fixedSurplusProfileCompositionCoeff]
  exact fixedSurplusProfileCompositionCoeff_eq_cubic_add_noncubic
    M (FieldRootedTree.series M g) ell k

/-- The strict graph-theoretic edge gap supplies the promised extra factor
`X` once a noncubic fixed-core contribution has an analytic amplitude. -/
theorem isNoncubic_normalizedAmplitude_eq_X_mul
    {k ell : ℕ} (hell : 0 < ell) {G : SimpleGraph (Fin k)}
    (hG : IsNoncubicAdmissibleAttachmentCore k ell G)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R 0 ∧
      ∀ X,
        X ^ (3 * ell - Nat.card (KernelEdgeLabel G)) * F X =
          X * R X := by
  exact
    AnalyticFiniteAmplitude.noncubic_normalizedAmplitude_eq_X_mul
      (kernelEdgeLabel_card_lt_three_surplus_of_isNoncubic hell hG)
      F hF

end GraphCore
end PerronWright
