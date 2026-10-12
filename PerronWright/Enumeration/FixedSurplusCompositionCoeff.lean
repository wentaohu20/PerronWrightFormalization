import PerronWright.Enumeration.UnicyclicCompositionCoeff

/-!
# Fixed-surplus rooted-profile composition coefficients

This file records the direct fixed-surplus extension of the unicyclic
composition-coefficient identity.  The core profile series itself is
independent of the surplus; only the finite subtype of admissible ordered
cores changes from surplus zero to surplus `ell`.
-/

open scoped Classical ENNReal NNReal Topology
open MeasureTheory

noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The size-`k` coefficient of the literal rooted-profile composition over
all admissible ordered cores of attachment surplus `ell`.

The antidiagonal subtype records the unique split of the labels into core and
off-core vertices.  Division by the core factorial is the labelled-EGF
normalization left after the core-label choice and forest factorial cancel.
-/
def fixedSurplusProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    (ell k : ℕ) : ℂ :=
  ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    (∑ H : {H : SimpleGraph (Fin p.1.1) //
        IsAdmissibleAttachmentCore p.1.1 ell H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) /
      (p.1.1.factorial : ℂ)

/-- Exact cancellation between the choice of the core labels, the factorial
from the labelled attached forest, and the total labelled-EGF factorial. -/
private theorem choose_mul_offFactorial_div_totalFactorial_fixedSurplus
    {k q n : ℕ} (hqn : q + n = k) :
    ((Nat.choose k q : ℂ) * (n.factorial : ℂ)) /
        (k.factorial : ℂ) =
      1 / (q.factorial : ℂ) := by
  have hqk : q ≤ k := by omega
  have hsub : k - q = n := by omega
  have hnat := Nat.choose_mul_factorial_mul_factorial hqk
  rw [hsub] at hnat
  have hcast :
      (Nat.choose k q : ℂ) * (q.factorial : ℂ) *
          (n.factorial : ℂ) =
        (k.factorial : ℂ) := by
    exact_mod_cast hnat
  have hqfac : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero q
  have hkfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hqfac, hkfac]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast

/-- The explicit off-core factorial in the labelled-forest formula factors
out of the finite admissible-core sum and the core-profile integral. -/
private theorem fixedSurplusCoreAttachmentFactorial_extract
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell q n : ℕ) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q ell H},
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) H.1 roots *
          ((n.factorial : ℂ) * PowerSeries.coeff n
            (PowerSeries.subst
              (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ)))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu)) =
      (n.factorial : ℂ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q ell H},
          ∫ roots : Fin q → S,
            finiteComplexGraphIntegrand M
                (FieldRootedTree.vertexFactor M g) H.1 roots *
              PowerSeries.coeff n
                (PowerSeries.subst
                  (M.complexCoreBranchActionSeries g roots)
                  (PowerSeries.exp ℂ))
            ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro H
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with roots
  ring

/-- The genuine complex fixed-size, fixed-surplus connected weight, after
labelled-EGF normalization, is exactly the corresponding coefficient of the
literal rooted-profile composition evaluated at the genuine field-rooted
tree series.

Here `ell` is the attachment-core surplus, so the connected-weight parameter
is `ell + 1` in the paper's `edges = vertices + r - 1` convention.
-/
theorem complexFieldConnectedWeight_div_factorial_eq_fixedSurplusProfileCompositionCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) / (k.factorial : ℂ) =
      fixedSurplusProfileCompositionCoeff M
        (FieldRootedTree.series M g) ell k := by
  rw [complexFieldConnectedWeight_eq_coreAttachmentCoeff M g k ell]
  unfold fixedSurplusProfileCompositionCoeff
  rw [Finset.sum_div]
  apply Fintype.sum_congr
  intro p
  have hqn : p.1.1 + p.1.2 = k := mem_coreOffSizePairs.mp p.2
  rw [fixedSurplusCoreAttachmentFactorial_extract]
  have hfactor :=
    choose_mul_offFactorial_div_totalFactorial_fixedSurplus
      (k := k) (q := p.1.1) (n := p.1.2) hqn
  let A : ℂ :=
    ∑ H : {H : SimpleGraph (Fin p.1.1) //
        IsAdmissibleAttachmentCore p.1.1 ell H},
      ∫ roots : Fin p.1.1 → S,
        finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) H.1 roots *
          PowerSeries.coeff p.1.2
            (PowerSeries.subst
              (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ))
        ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu)
  calc
    ((Nat.choose k p.1.1 : ℂ) * ((p.1.2.factorial : ℂ) * A)) /
          (k.factorial : ℂ) =
        (((Nat.choose k p.1.1 : ℂ) * (p.1.2.factorial : ℂ)) /
          (k.factorial : ℂ)) * A := by ring
    _ = (1 / (p.1.1.factorial : ℂ)) * A := by rw [hfactor]
    _ = A / (p.1.1.factorial : ℂ) := by ring
    _ = (∑ H : {H : SimpleGraph (Fin p.1.1) //
          IsAdmissibleAttachmentCore p.1.1 ell H},
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M
            (FieldRootedTree.series M g) H.1)) /
          (p.1.1.factorial : ℂ) := by
      apply congrArg (fun z : ℂ ↦ z / (p.1.1.factorial : ℂ))
      dsimp only [A]
      apply Fintype.sum_congr
      intro H
      exact (fixedCoreProfileCompositionSeries_actual_coeff
        M g H.1 hqn).symm

end GraphCore
end PerronWright
