import PerronWright.Analysis.FiniteIrreducibleCubicFieldWeightAsymptotic
import PerronWright.Analysis.FiniteIrreducibleNoncubicFieldWeightAsymptotic
import PerronWright.Analysis.ScalarFieldBridge

/-!
# The actual total positive-surplus finite connected-graph asymptotic

The model is the literal symmetric nonnegative irreducible finite matrix with
positive type law and spectral radius one. The proof adds the genuine cubic
and noncubic labelled-graph contributions. It uses no primitivity or B2
hypothesis, and permits a negative peripheral eigenvalue.

The field-uniform theorem keeps the actual analytic critical radius in the
normalization. Converting this to the explicit scalar critical-window
Gaussian factor requires the separate second-order scalar radius response.
-/

open Filter Topology Asymptotics
open scoped Classical Topology BigOperators Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleConnectedFieldAsymptotic

open GraphCore FiniteIrreducibleKernelAmplitude

namespace Cubic
export PerronWright.FiniteIrreducibleCubicFieldWeightAsymptotic
  (complexFieldCubicPartConnectedWeight
   complexFieldCubicPartConnectedWeight_eq
   exists_complexFieldCubicPartConnectedWeight_local_relative_bound)
end Cubic

namespace Noncubic
export PerronWright.FiniteIrreducibleNoncubicFieldWeightAsymptotic
  (complexFieldNoncubicPartConnectedWeight
   complexFieldNoncubicPartConnectedWeight_eq
   exists_complexFieldNoncubicPartConnectedWeight_cubicMain_bound)
end Noncubic

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Exact partition of the actual labelled connected-graph weight. -/
theorem complexFieldConnectedWeight_eq_cubic_add_noncubic
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    M.bjrModel.complexFieldConnectedWeight g k (ell + 1) =
      Cubic.complexFieldCubicPartConnectedWeight M g ell k +
        Noncubic.complexFieldNoncubicPartConnectedWeight M g ell k := by
  have hsplit :=
    complexFieldConnectedWeight_div_factorial_eq_cubic_add_noncubic
      M.bjrModel g ell k
  have hfact : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  rw [Cubic.complexFieldCubicPartConnectedWeight_eq,
    Noncubic.complexFieldNoncubicPartConnectedWeight_eq]
  calc
    M.bjrModel.complexFieldConnectedWeight g k (ell + 1) =
        (k.factorial : ℂ) *
          (M.bjrModel.complexFieldConnectedWeight g k (ell + 1) /
            (k.factorial : ℂ)) := by field_simp [hfact]
    _ = _ := by rw [hsplit]; ring

/-- Uniform Perron--Wright estimate for the total actual connected weight at
every fixed positive surplus, on a genuine complex field ball. -/
theorem exists_complexFieldConnectedWeight_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ k : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k (ell + 1) /
            ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
              positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
          K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨ec, Kc, hec, hKc, hc⟩ :=
    Cubic.exists_complexFieldCubicPartConnectedWeight_local_relative_bound
      M hM hell
  obtain ⟨en, Kn, hen, hKn, hn⟩ :=
    Noncubic.exists_complexFieldNoncubicPartConnectedWeight_cubicMain_bound
      M hM hell
  refine ⟨min ec en, Kc + Kn, lt_min hec hen, add_pos hKc hKn, ?_⟩
  filter_upwards [hc, hn] with k hkc hkn
  intro g hg
  have hcBound := hkc g (hg.trans (min_le_left ec en))
  have hnBound := hkn g (hg.trans (min_le_right ec en))
  let D : ℂ := (Real.sqrt (M.beta hM) : ℂ) ^ ell *
    positiveSurplusCubicFactorialMain ell k
  have heq :
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          M.bjrModel.complexFieldConnectedWeight g k (ell + 1) / D - 1 =
        ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          Cubic.complexFieldCubicPartConnectedWeight M g ell k / D - 1) +
        (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          Noncubic.complexFieldNoncubicPartConnectedWeight M g ell k / D := by
    rw [complexFieldConnectedWeight_eq_cubic_add_noncubic]
    ring
  change ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
    M.bjrModel.complexFieldConnectedWeight g k (ell + 1) / D - 1‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans
    ((add_le_add hcBound hnBound).trans_eq (by ring))

/-- At zero field the actual radius is one, giving the critical total
connected-graph coefficient estimate without any radius factor. -/
theorem exists_complexFieldConnectedWeight_zero_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ‖M.bjrModel.complexFieldConnectedWeight 0 k (ell + 1) /
          ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
            positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
        K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨epsilon, K, hepsilon, hK, hbound⟩ :=
    exists_complexFieldConnectedWeight_local_relative_bound M hM hell
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with k hk
  simpa only [FiniteIrreducibleRadiusResponse.radius_base, one_pow,
    one_mul, norm_zero, zero_add] using hk 0 (by simpa using hepsilon.le)

/-- The relative zero-field error is genuinely of half-step order. -/
theorem complexFieldConnectedWeight_zero_relative_error_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    (fun k : ℕ ↦
      M.bjrModel.complexFieldConnectedWeight 0 k (ell + 1) /
        ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
          positiveSurplusCubicFactorialMain ell k) - 1) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_complexFieldConnectedWeight_zero_relative_bound M hM hell
  apply IsBigO.of_bound K
  filter_upwards [hbound] with k hk
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)] using hk

end PerronWright.FiniteIrreducibleConnectedFieldAsymptotic
