import PerronWright.Probability.CompactAnnealedMarkedFactorialSequence
import PerronWright.Analysis.CompactSequentialUniform
import PerronWright.Probability.FactorialWindowMass

/-! # Actual marked local factorial limits uniformly on compact windows -/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactAnnealedMarkedFactorialUniform

open CompactAnnealedMarkedFactorialLocal CompactAnnealedMarkedFactorialSequence
  AnnealedMarkedResidualConcentration FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Genuine marked counts, uniformly in their literal moving-floor size
coordinates. The limiting mark evaluation is the actual Perron mark. -/
theorem marked_factorial_uniform_sizeWindow (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    TendstoUniformlyOn (fun n x ↦ localMarkedExpectation M lambda n x r Ψ)
      (fun x ↦ density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q))
        atTop (sizeWindow q a b) := by
  apply CompactSequentialUniform.uniform_of_diagonal_sequences isCompact_Icc _ _
    ((density_continuousOn_sizeWindow _ _ _ r ha).mul continuousOn_const)
  intro N hN hNt x hx s hs hxs
  have hxa (m) (i) : a ≤ x m i := (mem_sizeWindow.mp (hx m) i).1
  have hxb (m) (i) : x m i ≤ b := (mem_sizeWindow.mp (hx m) i).2
  have hspos (i) : 0 < s i := ha.trans_le (mem_sizeWindow.mp hs i).1
  exact marked_factorial_sequence_tendsto_positive_sizes M hM hQP hq r N hN hNt x lambda a b ha
    (ha.le.trans hab) hxa hxb s hspos (fun i ↦ (tendsto_pi_nhds.mp hxs) i) Ψ hΨ

/-- Uniformity also holds simultaneously over the finite bounded
surplus tuple range, for every fixed coupled continuous joint mark test. -/
theorem marked_factorial_uniform_bounded_surplus (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ x ∈ sizeWindow q a b,
        |localMarkedExpectation M lambda n x r Ψ -
          density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)| < ε := by
  intro ε hε
  have hall : ∀ rr : Fin q → Fin (R+1), ∀ᶠ n in atTop, ∀ x ∈ sizeWindow q a b,
      dist (density (M.alpha hM) (M.beta hM) lambda x (fun i ↦ (rr i).val) * Ψ (perronMarks M hM q))
        (localMarkedExpectation M lambda n x (fun i ↦ (rr i).val) Ψ) < ε := by
    intro rr
    exact Metric.tendstoUniformlyOn_iff.mp
      (marked_factorial_uniform_sizeWindow M hM hQP hq (fun i ↦ (rr i).val) lambda a b ha hab Ψ hΨ) ε hε
  filter_upwards [Filter.eventually_all.mpr hall] with n hn r hr x hx
  let rr : Fin q → Fin (R+1) := fun i ↦ ⟨r i,Nat.lt_succ_of_le (hr i)⟩
  have he := hn rr x hx
  simpa only [rr,Real.dist_eq,abs_sub_comm] using he

end PerronWright.CompactAnnealedMarkedFactorialUniform
