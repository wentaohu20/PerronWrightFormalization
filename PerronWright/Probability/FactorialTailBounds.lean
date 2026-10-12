import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The next factorial moment controls observable tails

These are the literal tail inequalities used in the local factorial
criterion.  They apply to changing probability spaces and laws as well as
to a common probability space.  Uniform integrability is not supplied as
an external interface.
-/

open MeasureTheory Filter
open scoped Classical

noncomputable section

namespace PerronWright.FactorialTailBounds

theorem factorial_le_next_div {n q H : ℕ} (hq : q < H) (hn : H < n) :
    (n.descFactorial q : ℝ) ≤ (n.descFactorial (q + 1) : ℝ) /
      ((H : ℝ) - (q : ℝ)) := by
  have hd : 0 < (H : ℝ) - (q : ℝ) := sub_pos.mpr (by exact_mod_cast hq)
  apply (le_div_iff₀ hd).mpr
  have hnat : (H - q) * n.descFactorial q ≤ n.descFactorial (q + 1) := by
    rw [Nat.descFactorial_succ]
    exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hn.le q)
  have hc : ((H : ℝ) - (q : ℝ)) * (n.descFactorial q : ℝ) ≤
      (n.descFactorial (q + 1) : ℝ) := by
    have hcast : ((H - q : ℕ) : ℝ) * (n.descFactorial q : ℝ) ≤
        (n.descFactorial (q + 1) : ℝ) := by exact_mod_cast hnat
    simpa only [Nat.cast_sub hq.le] using hcast
  simpa only [mul_comm] using hc

/-- A nonnegative degree-`q` count observable can exceed `(H)_q` only if
the literal total count exceeds `H`. -/
theorem observable_exceeds_implies_count_exceeds {q H n : ℕ} {y : ℝ}
    (hy : y ≤ (n.descFactorial q : ℝ))
    (ht : (H.descFactorial q : ℝ) < y) : H < n := by
  by_contra hn
  have hmono : (n.descFactorial q : ℝ) ≤ (H.descFactorial q : ℝ) := by
    exact_mod_cast Nat.descFactorial_le q (Nat.le_of_not_gt hn)
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact next-moment bound for the actual observable tail. -/
theorem integral_observable_tail_le (μ : Measure Ω) (N : Ω → ℕ) (Y : Ω → ℝ)
    (q H : ℕ) (hq : q < H) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hYq : ∀ ω, Y ω ≤ ((N ω).descFactorial q : ℝ))
    (hintq : Integrable (fun ω ↦ ((N ω).descFactorial q : ℝ)) μ)
    (hintnext : Integrable (fun ω ↦ ((N ω).descFactorial (q + 1) : ℝ)) μ) :
    (∫ ω, {ω | (H.descFactorial q : ℝ) < Y ω}.indicator Y ω ∂μ) ≤
      (∫ ω, ((N ω).descFactorial (q + 1) : ℝ) ∂μ) /
        ((H : ℝ) - (q : ℝ)) := by
  have hYi : Integrable Y μ := hintq.mono_nonneg hY.aestronglyMeasurable
    (Eventually.of_forall hY0) (Eventually.of_forall hYq)
  have hset : MeasurableSet {ω | (H.descFactorial q : ℝ) < Y ω} :=
    measurableSet_lt measurable_const hY
  have hd : 0 < (H : ℝ) - (q : ℝ) := sub_pos.mpr (by exact_mod_cast hq)
  rw [← integral_div]
  apply integral_mono (hYi.indicator hset) (hintnext.div_const _)
  intro ω
  by_cases ht : (H.descFactorial q : ℝ) < Y ω
  · rw [Set.indicator_of_mem
      (show ω ∈ {ω | (H.descFactorial q : ℝ) < Y ω} from ht)]
    exact (hYq ω).trans (factorial_le_next_div hq
      (observable_exceeds_implies_count_exceeds (hYq ω) ht))
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | (H.descFactorial q : ℝ) < Y ω} from ht)]
    positivity

/-- One uniform `(q+1)`-st moment bound makes all degree-`q` observable
tails uniformly small, even when the underlying laws vary with the index. -/
theorem exists_uniform_observable_tail_cutoff {ι : Type*}
    (μ : ι → Measure Ω) (N : ι → Ω → ℕ) (Y : ι → Ω → ℝ) (q : ℕ)
    (hY : ∀ i, Measurable (Y i)) (hY0 : ∀ i ω, 0 ≤ Y i ω)
    (hYq : ∀ i ω, Y i ω ≤ ((N i ω).descFactorial q : ℝ))
    (hintq : ∀ i, Integrable (fun ω ↦ ((N i ω).descFactorial q : ℝ)) (μ i))
    (hintnext : ∀ i, Integrable (fun ω ↦ ((N i ω).descFactorial (q + 1) : ℝ)) (μ i))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, (∫ ω, ((N i ω).descFactorial (q + 1) : ℝ) ∂μ i) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, q < H ∧ ∀ i,
      (∫ ω, {ω | (H.descFactorial q : ℝ) < Y i ω}.indicator (Y i) ω ∂μ i) < ε := by
  obtain ⟨H, hH⟩ := exists_nat_gt ((q : ℝ) + M / ε)
  have hd0 : (q : ℝ) < (H : ℝ) := by
    have hp : 0 ≤ M / ε := div_nonneg hM hε.le
    linarith
  have hq : q < H := by exact_mod_cast hd0
  have hd : 0 < (H : ℝ) - (q : ℝ) := sub_pos.mpr hd0
  have hcut : M / ((H : ℝ) - (q : ℝ)) < ε := by
    apply (div_lt_iff₀ hd).mpr
    have hm : M / ε < (H : ℝ) - (q : ℝ) := by linarith
    have hm' := (div_lt_iff₀ hε).mp hm
    nlinarith
  refine ⟨H, hq, fun i ↦ ?_⟩
  exact (integral_observable_tail_le (μ i) (N i) (Y i) q H hq
    (hY i) (hY0 i) (hYq i) (hintq i) (hintnext i)).trans_lt
    ((div_le_div_of_nonneg_right (hbound i) hd.le).trans_lt hcut)

end PerronWright.FactorialTailBounds
