import PerronWright.Probability.ConnectedTypeLaw
import Mathlib.Probability.Moments.Basic

/-!
# Exact connected-profile Chernoff estimates

All exponential type sums are integrable under the proved connected type
law.  Consequently its enumerator ratios give literal probability tail
bounds, not only formal generating-function identities.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The fixed-size connected law assigns full probability to the literal
connected, fixed-surplus graph event. -/
theorem eligible_ae (M : CompactBJRModel S) (g : C(S, ℝ)) (k r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) :
    ∀ᵐ p ∂law M g k r hC, Eligible r p.2 := by
  rw [ae_iff]
  have hm : MeasurableSet {p : State S k | ¬Eligible r p.2} :=
    (Set.toFinite {H : SimpleGraph (Fin k) | ¬Eligible r H}).measurableSet.preimage
      measurable_snd
  rw [law, withDensity_apply _ hm]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hm] with p hp
  simp only [weight, if_neg hp, zero_div, ENNReal.ofReal_zero, Pi.zero_apply]

/-- Exponential type observables are genuinely integrable for every
continuous real test field, without a small-field restriction. -/
theorem integrable_exp_typeSum (M : CompactBJRModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r) :
    Integrable (fun p : State S k ↦ Real.exp (typeSum f p.1)) (law M g k r hC) := by
  have hd : Measurable (fun p : State S k ↦
      ENNReal.ofReal (weight M g k r p / M.fieldConnectedWeight g k r)) :=
    ENNReal.measurable_ofReal.comp ((weight_measurable M g k r).div_const _)
  unfold law
  apply (integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mpr
  have he (p : State S k) :
      (ENNReal.ofReal (weight M g k r p / M.fieldConnectedWeight g k r)).toReal •
          Real.exp (typeSum f p.1) =
        weight M (g + f) k r p / M.fieldConnectedWeight g k r := by
    rw [ENNReal.toReal_ofReal (div_nonneg (weight_nonneg M g k r p) hC.le)]
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, weight_tilt]
  simp_rw [he]
  exact (weight_integrable M (g + f) k r).div_const _

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem typeSum_smul {k : ℕ} (f : C(S, ℝ)) (s : ℝ) (x : Fin k → S) :
    typeSum (s • f) x = s * typeSum f x := by
  simp only [typeSum, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Literal upper-tail probability in terms of the connected enumerator. -/
theorem upper_tail_le_enumerator_ratio (M : CompactBJRModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r)
    (z s : ℝ) (hs : 0 ≤ s) :
    (law M g k r hC).real {p | z ≤ typeSum f p.1} ≤
      Real.exp (-s * z) *
        (M.fieldConnectedWeight (g + s • f) k r / M.fieldConnectedWeight g k r) := by
  have hi : Integrable (fun p : State S k ↦ Real.exp (s * typeSum f p.1))
      (law M g k r hC) := by
    simpa only [typeSum_smul] using integrable_exp_typeSum M g (s • f) k r hC
  have hb := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := fun p : State S k ↦ typeSum f p.1) (μ := law M g k r hC) z hs hi
  have he : ProbabilityTheory.mgf (fun p : State S k ↦ typeSum f p.1)
      (law M g k r hC) s =
        M.fieldConnectedWeight (g + s • f) k r / M.fieldConnectedWeight g k r := by
    simpa only [ProbabilityTheory.mgf, typeSum_smul] using
      laplace_eq_enumerator_ratio M g (s • f) k r hC
  rwa [he] at hb

/-- Literal lower-tail probability, using a nonpositive exponential tilt. -/
theorem lower_tail_le_enumerator_ratio (M : CompactBJRModel S)
    (g f : C(S, ℝ)) (k r : ℕ) (hC : 0 < M.fieldConnectedWeight g k r)
    (z s : ℝ) (hs : s ≤ 0) :
    (law M g k r hC).real {p | typeSum f p.1 ≤ z} ≤
      Real.exp (-s * z) *
        (M.fieldConnectedWeight (g + s • f) k r / M.fieldConnectedWeight g k r) := by
  have hi : Integrable (fun p : State S k ↦ Real.exp (s * typeSum f p.1))
      (law M g k r hC) := by
    simpa only [typeSum_smul] using integrable_exp_typeSum M g (s • f) k r hC
  have hb := ProbabilityTheory.measure_le_le_exp_mul_mgf
    (X := fun p : State S k ↦ typeSum f p.1) (μ := law M g k r hC) z hs hi
  have he : ProbabilityTheory.mgf (fun p : State S k ↦ typeSum f p.1)
      (law M g k r hC) s =
        M.fieldConnectedWeight (g + s • f) k r / M.fieldConnectedWeight g k r := by
    simpa only [ProbabilityTheory.mgf, typeSum_smul] using
      laplace_eq_enumerator_ratio M g (s • f) k r hC
  rwa [he] at hb

end PerronWright.ConnectedTypeLaw
