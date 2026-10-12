import PerronWright.Probability.CompactAnnealedFactorialSequence
import PerronWright.Analysis.CompactSequentialUniform
import PerronWright.Probability.FactorialWindowMass

/-! # Uniform local factorial asymptotics for the actual compact graph law

This closes the annealed regular compact, bounded-surplus local factorial
formula under the paper's literal B1/B2 and QP assumptions. Identification
of the limiting point-process law with Aldous remains a distinct result.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CompactAnnealedFactorialUniform

open CompactAnnealedFactorialLocal CompactAnnealedFactorialSequence FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Uniformity in the literal real component-size coordinates is proved
by actual moving-floor sequence limits and compactness, not assumed. -/
theorem factorial_uniform_sizeWindow (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun n x ↦ localExpectation M lambda n x r)
      (fun x ↦ density (M.alpha hM) (M.beta hM) lambda x r) atTop (sizeWindow q a b) := by
  apply CompactSequentialUniform.uniform_of_diagonal_sequences isCompact_Icc
    _ _ (density_continuousOn_sizeWindow _ _ _ r ha)
  intro N hN hNt x hx s hs hxs
  have hxa (m) (i) : a ≤ x m i := (mem_sizeWindow.mp (hx m) i).1
  have hxb (m) (i) : x m i ≤ b := (mem_sizeWindow.mp (hx m) i).2
  have hspos (i) : 0 < s i := ha.trans_le (mem_sizeWindow.mp hs i).1
  exact factorial_sequence_tendsto_positive_sizes M hM hQP hq r N hN hNt
    x lambda a b ha (ha.le.trans hab) hxa hxb s hspos
    (fun i ↦ (tendsto_pi_nhds.mp hxs) i)

/-- The actual compact-model local factorial formula, uniformly over
the entire fixed positive size window and every bounded surplus tuple. -/
theorem factorial_uniform_bounded_surplus (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ x ∈ sizeWindow q a b,
        |localExpectation M lambda n x r - density (M.alpha hM) (M.beta hM) lambda x r| < ε := by
  intro ε hε
  have hall : ∀ rr : Fin q → Fin (R+1), ∀ᶠ n in atTop, ∀ x ∈ sizeWindow q a b,
      dist (density (M.alpha hM) (M.beta hM) lambda x (fun i ↦ (rr i).val))
        (localExpectation M lambda n x (fun i ↦ (rr i).val)) < ε := by
    intro rr
    exact Metric.tendstoUniformlyOn_iff.mp
      (factorial_uniform_sizeWindow M hM hQP hq (fun i ↦ (rr i).val) lambda a b ha hab) ε hε
  filter_upwards [Filter.eventually_all.mpr hall] with n hn r hr x hx
  let rr : Fin q → Fin (R+1) := fun i ↦ ⟨r i,Nat.lt_succ_of_le (hr i)⟩
  have he := hn rr x hx
  simpa only [rr,Real.dist_eq,abs_sub_comm] using he

end PerronWright.CompactAnnealedFactorialUniform
