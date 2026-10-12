import PerronWright.Probability.ConnectedTypePositivity
import PerronWright.Probability.ConnectedTypeTails

/-!
# Field domination and genuine connected-law normalizers

Finite graph integrands give exponential domination under every real
continuous field tilt.  This proves positivity of all field normalizers
from the already proved zero-field Perron--Wright theorem.  The crude
domination in this file is not the scale-matched centered Laplace estimate
needed for the probability main theorem.
-/

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
theorem typeSum_norm_le {k : ℕ} (f : C(S, ℝ)) (x : Fin k → S) :
    ‖typeSum f x‖ ≤ (k : ℝ) * ‖f‖ := by
  calc
    _ ≤ ∑ i : Fin k, ‖f (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, ‖f‖ :=
      Finset.sum_le_sum (fun i _ ↦ f.norm_coe_le_norm (x i))
    _ = _ := by simp

/-- Pointwise upper and lower domination of the literal finite connected
graph density under a continuous field tilt. -/
theorem weight_field_domination (M : CompactBJRModel S) (g f : C(S, ℝ))
    (k r : ℕ) (p : State S k) :
    Real.exp (-(k : ℝ) * ‖f‖) * weight M g k r p ≤ weight M (g + f) k r p ∧
    weight M (g + f) k r p ≤ Real.exp ((k : ℝ) * ‖f‖) * weight M g k r p := by
  have hb := typeSum_norm_le f p.1
  rw [Real.norm_eq_abs] at hb
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  have hn := weight_nonneg M g k r p
  rw [← weight_tilt]
  constructor
  · calc
      _ = weight M g k r p * Real.exp (-(k : ℝ) * ‖f‖) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hn
  · calc
      _ ≤ weight M g k r p * Real.exp ((k : ℝ) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hn
      _ = _ := mul_comm _ _

/-- The same domination holds for the actual normalizing enumerator. -/
theorem normalizer_field_domination (M : CompactBJRModel S) (g f : C(S, ℝ))
    (k r : ℕ) :
    Real.exp (-(k : ℝ) * ‖f‖) * M.fieldConnectedWeight g k r ≤
        M.fieldConnectedWeight (g + f) k r ∧
    M.fieldConnectedWeight (g + f) k r ≤
        Real.exp ((k : ℝ) * ‖f‖) * M.fieldConnectedWeight g k r := by
  have hi := weight_integrable M g k r
  have hj := weight_integrable M (g + f) k r
  constructor
  · calc
      _ = ∫ p, Real.exp (-(k : ℝ) * ‖f‖) * weight M g k r p
          ∂(AnnealedGraph.typeLaw M k).prod Measure.count := by
        rw [integral_const_mul, integral_weight]
      _ ≤ ∫ p, weight M (g + f) k r p
          ∂(AnnealedGraph.typeLaw M k).prod Measure.count :=
        integral_mono (hi.const_mul _) hj (fun p ↦ (weight_field_domination M g f k r p).1)
      _ = _ := integral_weight M (g + f) k r
  · calc
      _ = ∫ p, weight M (g + f) k r p
          ∂(AnnealedGraph.typeLaw M k).prod Measure.count := (integral_weight M (g + f) k r).symm
      _ ≤ ∫ p, Real.exp ((k : ℝ) * ‖f‖) * weight M g k r p
          ∂(AnnealedGraph.typeLaw M k).prod Measure.count :=
        integral_mono hj (hi.const_mul _) (fun p ↦ (weight_field_domination M g f k r p).2)
      _ = _ := by rw [integral_const_mul, integral_weight]

/-- Every real continuous field has a positive normalizer exactly when
the zero field has one; no small-field positivity assumption is added. -/
theorem normalizer_pos_iff_zero_field (M : CompactBJRModel S) (g : C(S, ℝ))
    (k r : ℕ) :
    0 < M.fieldConnectedWeight g k r ↔ 0 < M.fieldConnectedWeight 0 k r := by
  constructor
  · intro hg
    have h := (normalizer_field_domination M g (-g) k r).1
    simpa only [add_neg_cancel] using
      lt_of_lt_of_le (mul_pos (Real.exp_pos _) hg) h
  · intro h0
    have h := (normalizer_field_domination M 0 g k r).1
    simpa only [zero_add] using
      lt_of_lt_of_le (mul_pos (Real.exp_pos _) h0) h

/-- The bounded-surplus size threshold is uniform over all real continuous
fields.  The threshold comes from the proved zero-field enumeration. -/
theorem eventually_all_field_normalizers_pos (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ r ≤ R, ∀ g : C(S, ℝ),
      0 < M.fieldConnectedWeight g k r := by
  filter_upwards [eventually_zero_field_normalizer_pos M hM R] with k hk
  intro r hr g
  exact (normalizer_pos_iff_zero_field M g k r).mpr (hk r hr)

/-- Exact Laplace transform with a proved finite-size domination bound. -/
theorem laplace_le_exp_norm (M : CompactBJRModel S) (g f : C(S, ℝ))
    (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r) :
    (∫ p, Real.exp (typeSum f p.1) ∂law M g k r hC) ≤
      Real.exp ((k : ℝ) * ‖f‖) := by
  rw [laplace_eq_enumerator_ratio]
  apply (div_le_iff₀ hC).mpr
  exact (normalizer_field_domination M g f k r).2

end PerronWright.ConnectedTypeLaw
