import PerronWright.Probability.BrownianEntranceCountableLaw

/-! # Proved unbounded-moment transfer to the constructed entrance law

Every nonnegative Borel test is truncated at integer levels. Its genuine
finite-source bounded-test limit bounds each truncated expectation, and
monotone convergence removes the truncation. Upper envelopes may converge
to a constant; no uniform-integrability hypothesis is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceMomentTransfer

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianEntranceCountableLaw

theorem iSup_integer_truncation (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  calc
    _ = min x (⨆ n : ℕ, (n : ℝ≥0∞)) := by
      exact (inf_iSup_eq x (fun n : ℕ ↦ (n : ℝ≥0∞))).symm
    _ = x := by rw [ENNReal.iSup_natCast]; exact min_eq_left le_top

/-- Genuine finite-source Borel convergence implies the indicated upper
moment bound, even for an unbounded test. This is a proved transfer lemma,
not an input regularity assertion for the constructed process. -/
theorem lintegral_le_of_actual_upper_limit (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) (Φ : (J → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ)
    (b : ℝ → ℝ≥0∞) (C : ℝ≥0∞) (hb : Tendsto b (𝓝[>] 0) (𝓝 C))
    (hactual : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f, Φ (sampleEval T σ J f) ∂positiveBridgeLaw a T) ≤ b a) :
    (∫⁻ x, Φ (J.restrict x) ∂law T hT σ) ≤ C := by
  have hm : Measurable (fun x : ℕ → ℝ ↦ Φ (J.restrict x)) :=
    hΦ.comp (Finset.measurable_restrict J)
  have hlevel (n : ℕ) : (∫⁻ x, min (Φ (J.restrict x)) (n : ℝ≥0∞) ∂law T hT σ) ≤ C := by
    have ht := actual_law_finite_bounded_test_tendsto T hT σ J (n : ℝ)
      (fun v ↦ min (Φ v) (n : ℝ≥0∞)) (hΦ.min measurable_const)
      (fun v ↦ by simpa only [ENNReal.ofReal_natCast] using min_le_right (Φ v) (n : ℝ≥0∞))
    apply le_of_tendsto_of_tendsto ht hb
    filter_upwards [hactual] with a ha
    exact (lintegral_mono (fun f ↦ min_le_left (Φ (sampleEval T σ J f)) (n : ℝ≥0∞))).trans ha
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, min (Φ (J.restrict x)) (n : ℝ≥0∞) ∂law T hT σ :=
      lintegral_congr (fun x ↦ (iSup_integer_truncation _).symm)
    _ = ⨆ n : ℕ, ∫⁻ x, min (Φ (J.restrict x)) (n : ℝ≥0∞) ∂law T hT σ := by
      apply lintegral_iSup
      · exact fun n ↦ hm.min measurable_const
      · intro n m hnm x
        exact min_le_min_left _ (Nat.cast_le.mpr hnm)
    _ ≤ C := iSup_le hlevel

theorem lintegral_le_of_actual_bound (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) (Φ : (J → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ)
    (C : ℝ≥0∞) (hactual : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f, Φ (sampleEval T σ J f) ∂positiveBridgeLaw a T) ≤ C) :
    (∫⁻ x, Φ (J.restrict x) ∂law T hT σ) ≤ C :=
  lintegral_le_of_actual_upper_limit T hT σ J Φ hΦ (fun _ ↦ C) C tendsto_const_nhds hactual

def paddedValue (T t : ℝ≥0) (f : Path) : ℝ := if 0 < t ∧ t < T then f t else 0

theorem measurable_paddedValue (T t : ℝ≥0) : Measurable (paddedValue T t) := by
  by_cases h : 0 < t ∧ t < T
  · have he : paddedValue T t = (fun f : Path ↦ f t) := funext (fun _ ↦ if_pos h)
    rw [he]
    exact (continuous_eval_const t).measurable
  · have he : paddedValue T t = (fun _ : Path ↦ (0 : ℝ)) := funext (fun _ ↦ if_neg h)
    rw [he]
    exact measurable_const

theorem fourth_increment_le_of_actual_upper_limit (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (i j : ℕ) (b : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hb : Tendsto b (𝓝[>] 0) (𝓝 C))
    (hactual : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f, ENNReal.ofReal (‖paddedValue T (σ j) f-paddedValue T (σ i) f‖^4)
        ∂positiveBridgeLaw a T) ≤ b a) :
    (∫⁻ x, ENNReal.ofReal (‖x j-x i‖^4) ∂law T hT σ) ≤ C := by
  let J : Finset ℕ := {i,j}
  let u : J := ⟨i,by simp [J]⟩
  let v : J := ⟨j,by simp [J]⟩
  have hm : Measurable (fun z : J → ℝ ↦ ENNReal.ofReal (‖z v-z u‖^4)) := by fun_prop
  exact lintegral_le_of_actual_upper_limit T hT σ J _ hm b C hb hactual

end PerronWright.BrownianEntranceMomentTransfer
