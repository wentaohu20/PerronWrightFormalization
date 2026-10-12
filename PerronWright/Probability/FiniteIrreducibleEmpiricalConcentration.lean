import PerronWright.Probability.FiniteIrreducibleProfileLaplace
import PerronWright.Probability.EmpiricalMarkConcentration
import PerronWright.Probability.EmpiricalWeakNeighborhood

/-! # Actual finite irreducible Perron empirical-profile concentration

The empirical marks are the genuine probability measures of the sampled
vertex types. Only actual finite criticality is assumed. The exponential
bounds come from the complete finite arbitrary-field coefficient estimates;
no compact B2, graph placement, or profile interface is imposed.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleEmpiricalConcentration

open FiniteIrreducibleConnectedTypeLaw (State law perronLaw typeVectorLaw)
open FiniteIrreducibleProfileLaplace
open ConnectedTypeLaw (typeSum typeSum_continuous)
open EmpiricalMarkConcentration (connectedMark connectedMark_integral typesMark)
open EmpiricalWeakNeighborhood

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def testDeviation (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (p : State S k) : ℝ :=
    (∫ y, f y ∂(connectedMark hk p : Measure S)) - ∫ y, f y ∂(perronLaw M hM : Measure S)

omit [DiscreteTopology S] in
/-- The actual empirical-measure discrepancy is exactly the normalized
centered type sum, with the literal Perron-law center. -/
theorem testDeviation_eq_centered_div (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (p : State S k) :
    testDeviation M hM hk f p = centeredSum M hM f p / (k : ℝ) := by
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [testDeviation, connectedMark_integral, centeredSum]
  field_simp

theorem testDeviation_measurable (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) : Measurable (testDeviation M hM hk f) := by
  have he : testDeviation M hM hk f = fun p ↦
      (k : ℝ)⁻¹ * typeSum f p.1 - ∫ y, f y ∂(perronLaw M hM : Measure S) := by
    funext p
    rw [testDeviation, connectedMark_integral]
  rw [he]
  exact (measurable_const.mul ((typeSum_continuous f).measurable.comp measurable_fst)).sub measurable_const

omit [DiscreteTopology S] in
theorem testDeviation_smul (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (a : ℝ) (p : State S k) :
    testDeviation M hM hk (a • f) p = a * testDeviation M hM hk f p := by
  rw [testDeviation_eq_centered_div, centeredSum_smul, testDeviation_eq_centered_div]
  ring

/-- Gaussian concentration of a literal empirical probability-measure
test, in the expanding deviation range justified by the analytic proof. -/
theorem exists_empirical_gaussian_tail_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.bjrModel.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
          ∀ x : ℝ, 0 ≤ x → x ≤ η * Real.sqrt (k : ℝ) →
          ∀ hC : 0 < M.bjrModel.fieldConnectedWeight g k r,
          (law M g k r hC).real {p | x / Real.sqrt (k : ℝ) ≤ |testDeviation M hM hk f p|} ≤
            2 * Real.exp (-x ^ 2 / (4 * C) + L * x / 2 + Real.log 3) := by
  obtain ⟨η, C, hη, hC, hb⟩ := exists_criticalWindow_gaussian_tail_bound M hM R L hL
  refine ⟨η, C, hη, hC, ?_⟩
  filter_upwards [hb] with k hk
  refine ⟨hk.1, ?_⟩
  intro r hr
  refine ⟨(hk.2 r hr).1, ?_⟩
  intro g f hg hf x hx hxrange hCg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hsqpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkreal
  have hsqrtSq := Real.sq_sqrt hkreal.le
  have heq : (x / Real.sqrt (k : ℝ)) * (k : ℝ) = x * Real.sqrt (k : ℝ) := by
    calc
      _ = (x / Real.sqrt (k : ℝ)) * Real.sqrt (k : ℝ) ^ 2 := by rw [hsqrtSq]
      _ = _ := by field_simp [hsqpos.ne']
  have hsets : {p : State S k | x / Real.sqrt (k : ℝ) ≤ |testDeviation M hM hk.1 f p|} =
      {p | x * Real.sqrt (k : ℝ) ≤ |centeredSum M hM f p|} := by
    ext p
    simp only [Set.mem_ofPred_eq, testDeviation_eq_centered_div, abs_div, abs_of_pos hkreal]
    rw [le_div_iff₀ hkreal, heq]
  rw [hsets]
  exact (hk.2 r hr).2 g f hg hf x hx hxrange hCg

/-- Fixed deviations of unit-norm continuous tests have an actual
uniform exponential-in-size probability bound. -/
theorem exists_unit_test_exponential_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g f : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
        ∀ hC : 0 < M.bjrModel.fieldConnectedWeight g k r,
        (law M g k r hC).real {p | ε ≤ |testDeviation M hM hk f p|} ≤
          D * Real.exp (-c * (k : ℝ)) := by
  obtain ⟨η, C, hη, hC, hb⟩ := exists_empirical_gaussian_tail_bound M hM R L hL
  let b : ℝ := min ε η
  have hbpos : 0 < b := lt_min hε hη
  have hbε : b ≤ ε := min_le_left _ _
  have hbη : b ≤ η := min_le_right _ _
  let c : ℝ := b ^ 2 / (8 * C)
  let D : ℝ := 2 * Real.exp (C * L ^ 2 / 2 + Real.log 3)
  refine ⟨c, D, by dsimp only [c]; positivity, by dsimp only [D]; positivity, ?_⟩
  filter_upwards [hb] with k hk
  obtain ⟨hkpos, hkb⟩ := hk
  refine ⟨hkpos, ?_⟩
  intro r hr g f hg hf hCg
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkreal
  have hsqrtSq := Real.sq_sqrt hkreal.le
  have hxrange : b * Real.sqrt (k : ℝ) ≤ η * Real.sqrt (k : ℝ) :=
    mul_le_mul_of_nonneg_right hbη hsqrt.le
  have he := (hkb r hr).2 g f hg hf (b * Real.sqrt (k : ℝ))
    (mul_nonneg hbpos.le hsqrt.le) hxrange hCg
  rw [mul_div_cancel_right₀ _ hsqrt.ne'] at he
  have hmono : (law M g k r hCg).real {p | ε ≤ |testDeviation M hM hkpos f p|} ≤
      (law M g k r hCg).real {p | b ≤ |testDeviation M hM hkpos f p|} :=
    measureReal_mono (fun p hp ↦ hbε.trans hp)
  have hbsq : (b * Real.sqrt (k : ℝ)) ^ 2 = b ^ 2 * (k : ℝ) := by rw [mul_pow, hsqrtSq]
  have hyoung := sq_nonneg (b * Real.sqrt (k : ℝ) - 2 * C * L)
  have hcoeff : -2 * b ^ 2 * (k : ℝ) + 4 * C * L * b * Real.sqrt (k : ℝ) ≤
      -b ^ 2 * (k : ℝ) + 4 * C ^ 2 * L ^ 2 := by nlinarith only [hyoung, hbsq]
  have hnumeric : -(b * Real.sqrt (k : ℝ)) ^ 2 / (4 * C) +
      L * (b * Real.sqrt (k : ℝ)) / 2 + Real.log 3 ≤
      -c * (k : ℝ) + (C * L ^ 2 / 2 + Real.log 3) := by
    rw [hbsq]
    calc
      _ = (-2 * b ^ 2 * (k : ℝ) + 4 * C * L * b * Real.sqrt (k : ℝ)) / (8 * C) + Real.log 3 := by
        field_simp [hC.ne']
        ring
      _ ≤ (-b ^ 2 * (k : ℝ) + 4 * C ^ 2 * L ^ 2) / (8 * C) + Real.log 3 :=
        add_le_add (div_le_div_of_nonneg_right hcoeff (by positivity)) (le_refl _)
      _ = _ := by dsimp only [c]; field_simp [hC.ne']; ring
  exact (hmono.trans he).trans (by
    have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnumeric) (by norm_num : (0 : ℝ) ≤ 2)
    convert hm using 1
    simp only [Real.exp_add, D]
    ring)

/-- The same actual exponential bound for an arbitrary fixed continuous
test, obtained by legitimate norm normalization of the test field. -/
theorem exists_test_exponential_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε)
    (f : C(S, ℝ)) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ∀ hC : 0 < M.bjrModel.fieldConnectedWeight g k r,
        (law M g k r hC).real {p | ε ≤ |testDeviation M hM hk f p|} ≤
          D * Real.exp (-c * (k : ℝ)) := by
  let F : ℝ := ‖f‖ + 1
  have hF : 0 < F := by dsimp only [F]; positivity
  let f₀ : C(S, ℝ) := F⁻¹ • f
  have hf₀ : ‖f₀‖ ≤ 1 := by
    simp only [f₀, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hF)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hF).mpr (by dsimp only [F]; linarith)
  obtain ⟨c, D, hc, hD, hb⟩ := exists_unit_test_exponential_bound M hM R L (ε / F) hL (by positivity)
  refine ⟨c, D, hc, hD, ?_⟩
  filter_upwards [hb] with k hk
  obtain ⟨hkpos, hkb⟩ := hk
  refine ⟨hkpos, ?_⟩
  intro r hr g hg hC
  have he := hkb r hr g f₀ hg hf₀ hC
  have hsets : {p : State S k | ε / F ≤ |testDeviation M hM hkpos f₀ p|} =
      {p | ε ≤ |testDeviation M hM hkpos f p|} := by
    ext p
    simp only [Set.mem_ofPred_eq, f₀, testDeviation_smul, abs_mul, abs_of_pos (inv_pos.mpr hF)]
    rw [← div_eq_inv_mul, div_le_div_iff_of_pos_right hF]
  rwa [hsets] at he

/-- The exponential bound is uniform over finite families of unit-norm
tests; the sole family-size dependence is the union-bound prefactor. -/
theorem exists_finite_unit_tests_exponential_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ∀ F : Finset C(S, ℝ),
        (∀ f ∈ F, ‖f‖ ≤ 1) → ∀ hC : 0 < M.bjrModel.fieldConnectedWeight g k r,
        (law M g k r hC).real {p | ∃ f ∈ F, ε ≤ |testDeviation M hM hk f p|} ≤
          (F.card : ℝ) * D * Real.exp (-c * (k : ℝ)) := by
  classical
  obtain ⟨c, D, hc, hD, hb⟩ := exists_unit_test_exponential_bound M hM R L ε hL hε
  refine ⟨c, D, hc, hD, ?_⟩
  filter_upwards [hb] with k hk
  obtain ⟨hkpos, hkb⟩ := hk
  refine ⟨hkpos, ?_⟩
  intro r hr g hg F hF hC
  have hsets : {p : State S k | ∃ f ∈ F, ε ≤ |testDeviation M hM hkpos f p|} =
      ⋃ f ∈ F, {p | ε ≤ |testDeviation M hM hkpos f p|} := by ext p; simp
  rw [hsets]
  calc
    _ ≤ ∑ f ∈ F, (law M g k r hC).real {p | ε ≤ |testDeviation M hM hkpos f p|} :=
      measureReal_biUnion_finset_le F _
    _ ≤ ∑ _f ∈ F, D * Real.exp (-c * (k : ℝ)) :=
      Finset.sum_le_sum (fun f hf ↦ hkb r hr g f hg (hF f hf) hC)
    _ = _ := by simp; ring

/-- Concentration for the actual connected-law empirical mark, along
any sequence of sizes tending to infinity and uniformly bounded
critical-window fields. The surplus is only required to stay bounded. -/
theorem test_probability_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.bjrModel.fieldConnectedWeight (g n) (k n) (r n))
    (hkTop : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (f : C(S, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (law M (g n) (k n) (r n) (hC n)).real
      {p | ε ≤ |testDeviation M hM (hk n) f p|}) atTop (𝓝 0) := by
  obtain ⟨c, D, hc, _hD, hb⟩ := exists_test_exponential_bound M hM R L ε hL hε f
  have hupper : ∀ᶠ n in atTop,
      (law M (g n) (k n) (r n) (hC n)).real
        {p | ε ≤ |testDeviation M hM (hk n) f p|} ≤ D * Real.exp (-c * (k n : ℝ)) := by
    filter_upwards [hkTop.eventually hb, hr, hg] with n hn hnr hng
    obtain ⟨hkn, hnb⟩ := hn
    exact hnb (r n) hnr (g n) hng (hC n)
  have ht : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hkTop
  have hexp : Tendsto (fun n ↦ Real.exp (-c * (k n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by linarith))
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hupper
    (by simpa using hexp.const_mul D)

/-- A fixed finite family of continuous tests concentrates jointly;
this is an actual probability bound under the connected type laws. -/
theorem finite_tests_probability_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.bjrModel.fieldConnectedWeight (g n) (k n) (r n))
    (hkTop : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (F : Finset C(S, ℝ)) (ε : C(S, ℝ) → ℝ) (hε : ∀ f ∈ F, 0 < ε f) :
    Tendsto (fun n ↦ (law M (g n) (k n) (r n) (hC n)).real
      {p | ∃ f ∈ F, ε f ≤ |testDeviation M hM (hk n) f p|}) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ ∑ f ∈ F,
      (law M (g n) (k n) (r n) (hC n)).real
        {p | ε f ≤ |testDeviation M hM (hk n) f p|}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum F (fun f hf ↦
      test_probability_tendsto_zero M hM R L hL k r hk g hC hkTop hr hg f (ε f) (hε f hf))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hsum
  exact Eventually.of_forall (fun n ↦ by
    have hs : {p : State S (k n) | ∃ f ∈ F, ε f ≤ |testDeviation M hM (hk n) f p|} =
        ⋃ f ∈ F, {p | ε f ≤ |testDeviation M hM (hk n) f p|} := by ext p; simp
    rw [hs]
    exact measureReal_biUnion_finset_le F _)


/-- Actual weak-topology concentration follows from the proved finite
continuous tests, centered at the literal finite Perron probability measure. -/
theorem connectedMark_probability_outside_weak_nhds_tendsto_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.bjrModel.fieldConnectedWeight (g n) (k n) (r n))
    (hkTop : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronLaw M hM)) :
    Tendsto (fun n ↦ (law M (g n) (k n) (r n) (hC n)).real
      {p | connectedMark (hk n) p ∉ U}) atTop (𝓝 0) := by
  have : ∀ n, IsFiniteMeasure (law M (g n) (k n) (r n) (hC n)) := fun _ ↦ inferInstance
  apply probability_outside_nhds_tendsto_zero
    (fun n ↦ law M (g n) (k n) (r n) (hC n))
    (fun n ↦ connectedMark (hk n)) (perronLaw M hM) _ U hU
  intro f ε hε
  exact test_probability_tendsto_zero M hM R L hL k r hk g hC hkTop hr hg
    f.toContinuousMap ε hε

/-- The same genuine weak concentration for the actual type-vector
marginal itself, rather than only for the joint graph/type state. -/
theorem typeVectorLaw_probability_outside_weak_nhds_tendsto_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.bjrModel.fieldConnectedWeight (g n) (k n) (r n))
    (hkTop : Tendsto k atTop atTop) (hr : ∀ᶠ n in atTop, r n ≤ R)
    (hg : ∀ᶠ n in atTop, Real.sqrt (k n : ℝ) * ‖g n‖ ≤ L)
    (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronLaw M hM)) :
    Tendsto (fun n ↦ (typeVectorLaw M (g n) (k n) (r n) (hC n)).toMeasure.real
      {x | typesMark (hk n) x ∉ U}) atTop (𝓝 0) := by
  have heq : (fun n ↦ (typeVectorLaw M (g n) (k n) (r n) (hC n)).toMeasure.real
      {x | typesMark (hk n) x ∉ U}) =
      (fun n ↦ (law M (g n) (k n) (r n) (hC n)).real
        {p | connectedMark (hk n) p ∉ U}) := by
    funext n
    rw [typeVectorLaw, ProbabilityMeasure.toMeasure_map,
      map_measureReal_apply measurable_fst (MeasurableSet.of_discrete)]
    rfl
  rw [heq]
  exact connectedMark_probability_outside_weak_nhds_tendsto_zero
    M hM R L hL k r hk g hC hkTop hr hg U hU

/-- A model-only terminal: the actual laws are defined at every shifted
size by positivity derived from enumeration, not by a supplied profile
or normalizer assumption. Every genuine weak Perron neighborhood
concentrates along all bounded-surplus, bounded critical-field sequences. -/
theorem exists_actual_connectedMark_weak_concentration
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℕ, ∃ hk : ∀ n : ℕ, 0 < K + n,
      ∃ hC : ∀ n r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g (K + n) r,
      ∀ r : ℕ → ℕ, ∀ hr : ∀ n, r n ≤ R, ∀ g : ℕ → C(S, ℝ),
        (∀ᶠ n in atTop, Real.sqrt ((K + n : ℕ) : ℝ) * ‖g n‖ ≤ L) →
        ∀ U : Set (ProbabilityMeasure S), U ∈ 𝓝 (perronLaw M hM) →
          Tendsto (fun n ↦ (law M (g n) (K + n) (r n) (hC n (r n) (hr n) (g n))).real
            {p | connectedMark (hk n) p ∉ U}) atTop (𝓝 0) := by
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp
    (eventually_all_field_normalizers_pos M hM R)
  let K := max K₀ 1
  have hk : ∀ n : ℕ, 0 < K + n := fun n ↦ by dsimp only [K]; omega
  have hC : ∀ n r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
      0 < M.bjrModel.fieldConnectedWeight g (K + n) r :=
    fun n r hr g ↦ hK₀ (K + n) (by dsimp only [K]; omega) r hr g
  refine ⟨K, hk, hC, ?_⟩
  intro r hr g hg U hU
  have htop : Tendsto (fun n : ℕ ↦ K + n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  exact connectedMark_probability_outside_weak_nhds_tendsto_zero M hM R L hL
    (fun n ↦ K + n) r hk g (fun n ↦ hC n (r n) (hr n) (g n)) htop
    (Eventually.of_forall hr) hg U hU

/-- Model-only concentration under the actual weighted type-vector law:
all normalizers are proved positive on the chosen shifted size sequence. -/
theorem exists_actual_typeVectorLaw_weak_concentration
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℕ, ∃ hk : ∀ n : ℕ, 0 < K + n,
      ∃ hC : ∀ n r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        0 < M.bjrModel.fieldConnectedWeight g (K + n) r,
      ∀ r : ℕ → ℕ, ∀ hr : ∀ n, r n ≤ R, ∀ g : ℕ → C(S, ℝ),
        (∀ᶠ n in atTop, Real.sqrt ((K + n : ℕ) : ℝ) * ‖g n‖ ≤ L) →
        ∀ U : Set (ProbabilityMeasure S), U ∈ 𝓝 (perronLaw M hM) →
          Tendsto (fun n ↦
            (typeVectorLaw M (g n) (K + n) (r n) (hC n (r n) (hr n) (g n))).toMeasure.real
              {x | typesMark (hk n) x ∉ U}) atTop (𝓝 0) := by
  obtain ⟨K, hk, hC, _⟩ := exists_actual_connectedMark_weak_concentration M hM R L hL
  refine ⟨K, hk, hC, ?_⟩
  intro r hr g hg U hU
  have htop : Tendsto (fun n : ℕ ↦ K + n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  exact typeVectorLaw_probability_outside_weak_nhds_tendsto_zero M hM R L hL
    (fun n ↦ K + n) r hk g (fun n ↦ hC n (r n) (hr n) (g n)) htop
    (Eventually.of_forall hr) hg U hU

end PerronWright.FiniteIrreducibleEmpiricalConcentration
