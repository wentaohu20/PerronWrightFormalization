import PerronWright.Probability.FiniteIrreducibleRawResidualTerminal
import PerronWright.Probability.FiniteIrreducibleCriticalPrefactorScaling

/-! # Uniform actual residual averaging on the integer critical window

A quantitative Pearson moment bound is derived for the genuine native
connected-product laws. It yields one vanishing error covering every
integer component-size tuple in a positive bounded normalized window,
all bounded surplus tuples, and arbitrary O(1)-rounded populations.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FiniteIrreducibleRawResidualUniform

open FiniteIrreducibleRawResidualAveraging FiniteIrreducibleRawResidualTerminal
open FiniteIrreducibleResidualNormalization FiniteIrreducibleNativeProfileAveraging
open FiniteIrreducibleIsolationBounds FiniteIrreduciblePearsonProfile
open FiniteIrreducibleProfileFiniteCollection FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleDeterministicConnectedLawFormula (connectedProductLaw)
open FiniteIrreducibleProfileLaplace (eventually_all_field_normalizers_pos)
open FiniteIrreduciblePerronCountExpansion (mainExponent)
open FiniteIrreducibleDeterministicResidualWeights (residual)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Quantitative moments at the literal A/n coefficient, uniform on the
entire actual component-state product space, with no B2 hypothesis. -/
theorem exists_uniform_native_pearson_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q) (lambda A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      ∀ _hk : ∀ i, 0 < k i, ∀ _hr : ∀ i, r i ≤ R,
      ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
      (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
      0 ≤ (∫ p, Real.exp ((A / (n : ℝ)) * pearson M hM k p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) - 1 ∧
      (∫ p, Real.exp ((A / (n : ℝ)) * pearson M hM k p)
        ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) - 1 ≤
          D / Real.sqrt (∑ i, (k i : ℝ)) := by
  obtain ⟨L, hL, hf⟩ := exists_native_scalarField_bound M lambda C hC
  obtain ⟨D, hD, hb⟩ := exists_uniform_pearson_square_bound M hM R q hq L
    (A * C ^ (3 / 2 : ℝ)) hL (mul_nonneg hA (Real.rpow_nonneg hC _))
  refine ⟨D, hD, ?_⟩
  filter_upwards [hf, eventually_ge_atTop (1 : ℕ)] with n hfn hn1
  intro k r hk hr pos hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hK := totalSize_pos hq k hk
  have hsqrt := Real.sqrt_pos.mpr hK
  let a : ℝ := A * (∑ i, (k i : ℝ)) / (n : ℝ) * Real.sqrt (∑ i, (k i : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have har : a ≤ A * C ^ (3 / 2 : ℝ) := by
    exact (le_div_iff₀ hsqrt).mp (ProfileScaleMatched.coefficient_bounds hK hnR hC hA hs).2
  have hg : ∀ i, Real.sqrt (k i : ℝ) *
      ‖M.bjrModel.scalarField (CriticalScaling.time lambda n)‖ ≤ L := fun i ↦
    hfn (k i) ((Finset.single_le_sum (fun j _ ↦ Nat.cast_nonneg (k j)) (Finset.mem_univ i)).trans hs)
  have he := hb k r hk hr (fun _ ↦ M.bjrModel.scalarField (CriticalScaling.time lambda n)) hg
    a ha har pos
  have heq (p : StateFamily (S := S) k) :
      (A / (n : ℝ)) * pearson M hM k p =
        (a / Real.sqrt (∑ i, (k i : ℝ))) *
          ∑ b, (perronMass M hM b)⁻¹ * (pooledSum M hM k (coordinateTest b) p) ^ 2 := by
    rw [pearson_eq_coordinate_squares M hM hq k hk p]
    dsimp only [a]
    field_simp [hsqrt.ne']
  simpa only [← heq, productLaw_constant_eq_native] using he

/-- A true common L1 error estimate for all native tuples. -/
theorem exists_uniform_native_residual_L1_envelope
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda : ℝ) (c : ℕ → S → ℕ) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hround : ∀ᶠ n in atTop, ∀ a, |(c n a : ℝ) - (n : ℝ) * M.weight a| ≤ D) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
        ∀ _hk : ∀ i, 0 < k i, ∀ _hr : ∀ i, r i ≤ R,
        ∀ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
          (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
        (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) →
        (∫ p, |normalizedResidual M hM lambda n (c n) p - 1|
          ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) ≤
            Real.exp |err n| * (1 + B / Real.sqrt (∑ i, (k i : ℝ))) - 1 := by
  obtain ⟨err, herr, hb⟩ := exists_uniform_native_residual_exponent_bound M hM lambda R q c D C hD hC hround
  obtain ⟨B, hB, hp⟩ := exists_uniform_native_pearson_bound M hM R q hq lambda
    (isolationBudget M hM C 2) C (isolationBudget_nonneg M hM hC (by norm_num)) hC
  refine ⟨err, herr, B, hB, ?_⟩
  filter_upwards [hb, hp] with n hn hpn
  intro k r hk hr pos hs
  have hdom := (hn k r pos hr hs).2
  have heq := (hn k r pos hr hs).1
  have hm := (hpn k r hk hr pos hs).2
  have hh := integral_mono_ae (μ := connectedProductLaw M
    (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)
    (f := fun p ↦ |normalizedResidual M hM lambda n (c n) p - 1|)
    (g := fun p ↦ Real.exp ((isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p) *
      Real.exp |err n| - 1) Integrable.of_finite Integrable.of_finite (by
        filter_upwards [hdom] with p hd
        rw [heq p, ← Real.exp_add]
        exact (BoundedConcentrationTransfer.abs_exp_sub_one_le_exp_abs_sub_one _).trans
          (sub_le_sub_right (Real.exp_le_exp.mpr (hd.trans
            (add_le_add le_rfl (le_abs_self _)))) 1))
  rw [integral_sub Integrable.of_finite (integrable_const 1), integral_mul_const, integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  have hm' : (∫ p, Real.exp ((isolationBudget M hM C 2 / (n : ℝ)) * pearson M hM k p)
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) ≤
      1 + B / Real.sqrt (∑ i, (k i : ℝ)) := by linarith
  exact hh.trans (by nlinarith [Real.exp_pos |err n|])

/-- Model-only, full integer-window residual limit. Normalizer positivity,
the actual L1 estimate, and its mean-ratio consequence are all proved. -/
theorem eventually_uniform_native_rawResidual_limits
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R q : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      (∀ i, a ≤ normalizedSize n (k i)) →
      (∀ i, normalizedSize n (k i) ≤ b) → (∀ i, r i ≤ R) →
      ∃ pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
        (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i),
        (∫ p, |normalizedResidual M hM lambda n (c n) p - 1|
          ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) ≤ ε ∧
        |(∫ p, residual M (CriticalScaling.time lambda n) n (c n) p
            ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) /
          Real.exp (mainExponent M hM (n : ℝ) (∑ i, (k i : ℝ)) (CriticalScaling.time lambda n)) - 1| ≤ ε := by
  let C : ℝ := (q : ℝ) * b
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg q) hb
  obtain ⟨err, herr, B, hB, he⟩ := exists_uniform_native_residual_L1_envelope M hM R q hq lambda c D C hD hC hround
  have hpow : Tendsto (fun n : ℕ ↦ a * (n : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have hz : Tendsto (fun n : ℕ ↦ B / Real.sqrt (a * (n : ℝ) ^ (2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hpow)).const_mul B
  have hexp : Tendsto (fun n ↦ Real.exp |err n|) atTop (𝓝 1) := by
    simpa only [Function.comp_def, abs_zero, Real.exp_zero] using
      Real.continuous_exp.tendsto (|(0 : ℝ)|) |>.comp herr.abs
  have hfinal : Tendsto (fun n : ℕ ↦ Real.exp |err n| *
      (1 + B / Real.sqrt (a * (n : ℝ) ^ (2 / 3 : ℝ))) - 1) atTop (𝓝 0) := by
    simpa only [add_zero, mul_one, sub_self] using (hexp.mul (hz.const_add 1)).sub_const 1
  obtain ⟨K₀, hpos⟩ := Filter.eventually_atTop.mp (eventually_all_field_normalizers_pos M hM R)
  filter_upwards [he, eventually_all_sizes_ge a ha (max K₀ 1), eventually_ge_atTop (1 : ℕ),
    hfinal.eventually (Iio_mem_nhds hε)] with n hen hsize1 hn1 hsmall
  intro k r hka hkb hr
  have hn : 0 < n := by omega
  have hk : ∀ i, 0 < k i := fun i ↦ by have := hsize1 (k i) (hka i); omega
  have hsize : (∑ i, (k i : ℝ)) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ ∑ i : Fin q, b * (n : ℝ) ^ (2 / 3 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ size_upper_of_normalized hn (hkb i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, C]; ring
  have hlower : a * (n : ℝ) ^ (2 / 3 : ℝ) ≤ ∑ i, (k i : ℝ) :=
    (size_lower_of_normalized hn (hka ⟨0, hq⟩)).trans
      (Finset.single_le_sum (fun i _ ↦ Nat.cast_nonneg (k i)) (Finset.mem_univ (⟨0, hq⟩ : Fin q)))
  have hapos : 0 < Real.sqrt (a * (n : ℝ) ^ (2 / 3 : ℝ)) := by positivity
  have hden := Real.sqrt_le_sqrt hlower
  have hBr : B / Real.sqrt (∑ i, (k i : ℝ)) ≤
      B / Real.sqrt (a * (n : ℝ) ^ (2 / 3 : ℝ)) :=
    div_le_div_of_nonneg_left hB.le hapos hden
  have pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight
      (M.bjrModel.scalarField (CriticalScaling.time lambda n)) (k i) (r i) := by
    intro i
    exact hpos (k i) (by have := hsize1 (k i) (hka i); omega) (r i) (hr i) _
  have hu : Real.exp |err n| * (1 + B / Real.sqrt (∑ i, (k i : ℝ))) - 1 ≤
      Real.exp |err n| * (1 + B / Real.sqrt (a * (n : ℝ) ^ (2 / 3 : ℝ))) - 1 := by
    gcongr
  have hL : (∫ p, |normalizedResidual M hM lambda n (c n) p - 1|
      ∂connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos) ≤ ε :=
    (hen k r hk hr pos hsize).trans (hu.trans hsmall.le)
  refine ⟨pos, hL, ?_⟩
  have h := abs_integral_le_integral_abs
      (μ := connectedProductLaw M (M.bjrModel.scalarField (CriticalScaling.time lambda n)) k r pos)
      (f := fun p ↦ normalizedResidual M hM lambda n (c n) p - 1)
  rw [integral_sub Integrable.of_finite (integrable_const 1), integral_const,
    integral_normalizedResidual] at h
  simpa only [probReal_univ, smul_eq_mul, one_mul] using h.trans hL

end PerronWright.FiniteIrreducibleRawResidualUniform
