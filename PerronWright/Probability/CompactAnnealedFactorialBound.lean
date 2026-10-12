import PerronWright.Probability.CompactAnnealedFactorialUniform

/-! # Uniform bounds for actual integer-size factorial expectations -/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 700000

namespace PerronWright.CompactAnnealedFactorialBound

open CompactAnnealedFactorialLocal CompactAnnealedFactorialUniform FactorialDensity

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem exists_uniform_scaled_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ x ∈ sizeWindow q a b, |localExpectation M lambda n x r| ≤ B := by
  obtain ⟨C,hC,hbound⟩ := exists_density_window_bound (b := b) (M.beta_pos hM) ha R
  let B₀ := C^q * Real.exp (-M.beta hM*(a*q)^3/24)
  refine ⟨1+B₀,by dsimp only [B₀]; positivity,?_⟩
  filter_upwards [factorial_uniform_bounded_surplus M hM hQP hq R lambda a b ha hab 1 zero_lt_one]
    with n hn r hr x hx
  have hxi := mem_sizeWindow.mp hx
  have hd := hbound q (M.alpha hM) lambda x r hxi hr
  have hp := density_pos (M.alpha hM) lambda (M.beta_pos hM) x r
    (fun i ↦ ha.trans_le (hxi i).1)
  calc
    |localExpectation M lambda n x r| =
        |(localExpectation M lambda n x r-density (M.alpha hM) (M.beta hM) lambda x r) +
          density (M.alpha hM) (M.beta hM) lambda x r| := by congr 1; ring
    _ ≤ |localExpectation M lambda n x r-density (M.alpha hM) (M.beta hM) lambda x r| +
        |density (M.alpha hM) (M.beta hM) lambda x r| := abs_add_le _ _
    _ ≤ 1+B₀ := by rw [abs_of_pos hp]; exact add_le_add (hn r hr x hx).le hd

/-- The normalized integer coordinate gives back its exact floor,
without a rounding approximation or additional size premise. -/
theorem size_normalized_integer {n k : ℕ} (hn : 0 < n) :
    CriticalScaling.size ((k : ℝ)/(n : ℝ)^(2/3 : ℝ)) n = k := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold CriticalScaling.size
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnR _).ne']
  simp

/-- A genuine graph factorial moment bound for arbitrary integer tuples
whose normalized sizes lie in the actual fixed window. -/
theorem exists_integer_tuple_expectation_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ (n : ℕ) in atTop, ∀ k r : Fin q → ℕ, (∀ i, r i ≤ R) →
      (∀ i, (k i : ℝ)/(n : ℝ)^(2/3 : ℝ) ∈ Set.Icc a b) →
      (∫ G, (ComponentCounts.count G k r : ℝ)
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n) (CriticalScaling.time_nonneg lambda n) n) ≤
        B/(n : ℝ)^(2*(q : ℝ)/3) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_scaled_bound M hM hQP hq R lambda a b ha hab
  refine ⟨B,hB,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with n hn hnp k r hr hkr
  have hnpos : 0 < n := by omega
  have hp : (0 : ℝ) < (n : ℝ)^(2*(q : ℝ)/3) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) _
  let x i := (k i : ℝ)/(n : ℝ)^(2/3 : ℝ)
  have hs : (fun i ↦ CriticalScaling.size (x i) n) = k :=
    funext (fun _ ↦ size_normalized_integer hnpos)
  have hh := (le_abs_self (localExpectation M lambda n x r)).trans
    (hn r hr x (mem_sizeWindow.mpr hkr))
  unfold localExpectation at hh
  rw [hs] at hh
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)

end PerronWright.CompactAnnealedFactorialBound
