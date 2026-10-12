import PerronWright.Probability.ProfileLaplace
import PerronWright.Probability.EmpiricalTypeMarks
import PerronWright.Probability.ProjectiveFiniteCollection

/-!
# Concentration of actual empirical component marks

The random marks are genuine `ProbabilityMeasure` values. Their
continuous tests are identified with the centered connected-profile
statistics before any probability estimate is applied.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.EmpiricalMarkConcentration

open ConnectedTypeLaw EmpiricalTypeMarks ProfileLaplace ProfileSquareMoment
open ProfileFiniteCollection ProjectiveFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The empirical probability measure of every sampled vertex. -/
def typesMark {k : ℕ} (hk : 0 < k) (x : Fin k → S) : ProbabilityMeasure S := by
  let : NeZero k := ⟨hk.ne'⟩
  exact empiricalProbability x Finset.univ Finset.univ_nonempty

/-- The actual empirical mark under a connected type law. -/
def connectedMark {k : ℕ} (hk : 0 < k) (p : State S k) : ProbabilityMeasure S :=
  typesMark hk p.1

omit [CompactSpace S] in
theorem typesMark_integral {k : ℕ} (hk : 0 < k) (x : Fin k → S) (f : C(S, ℝ)) :
    (∫ y, f y ∂(typesMark hk x : Measure S)) = (k : ℝ)⁻¹ * typeSum f x := by
  unfold typesMark empiricalProbability
  rw [ProbabilityMeasure.coe_mk, empiricalMeasure_integral]
  simp [typeSum]

omit [CompactSpace S] in
theorem connectedMark_integral {k : ℕ} (hk : 0 < k) (p : State S k) (f : C(S, ℝ)) :
    (∫ y, f y ∂(connectedMark hk p : Measure S)) = (k : ℝ)⁻¹ * typeSum f p.1 :=
  typesMark_integral hk p.1 f

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem typesMark_measurable {k : ℕ} (hk : 0 < k) : Measurable (typesMark (S := S) hk) := by
  unfold typesMark
  exact empiricalProbability_measurable _ _

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem connectedMark_measurable {k : ℕ} (hk : 0 < k) :
    Measurable (connectedMark (S := S) hk) := (typesMark_measurable hk).comp measurable_fst

/-- Continuity is into the genuine weak topology of probability measures. -/
theorem typesMark_continuous {k : ℕ} (hk : 0 < k) : Continuous (typesMark (S := S) hk) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  simp_rw [typesMark_integral]
  exact continuous_const.mul (typeSum_continuous f)

/-- Weak-open mark events are measurable on the genuine sampling
space; no identification of the weak and Giry Borel structures is needed. -/
theorem connectedMark_open_event_measurable {k : ℕ} (hk : 0 < k)
    (U : Set (ProbabilityMeasure S)) (hU : IsOpen U) :
    MeasurableSet {p : State S k | connectedMark hk p ∈ U} :=
  (hU.preimage (typesMark_continuous hk)).measurableSet.preimage measurable_fst

def testDeviation (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (p : State S k) : ℝ :=
    (∫ y, f y ∂(connectedMark hk p : Measure S)) - ∫ y, f y ∂M.perronLaw hM

/-- The actual empirical-measure discrepancy is exactly the normalized
centered type sum, with the literal Perron-law center. -/
theorem testDeviation_eq_centered_div (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (p : State S k) :
    testDeviation M hM hk f p = centeredSum M hM f p / (k : ℝ) := by
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [testDeviation, connectedMark_integral, centeredSum]
  field_simp

theorem testDeviation_measurable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) : Measurable (testDeviation M hM hk f) := by
  have he : testDeviation M hM hk f = fun p ↦
      (k : ℝ)⁻¹ * typeSum f p.1 - ∫ y, f y ∂M.perronLaw hM := by
    funext p
    rw [testDeviation, connectedMark_integral]
  rw [he]
  exact (measurable_const.mul ((typeSum_continuous f).measurable.comp measurable_fst)).sub measurable_const

theorem testDeviation_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (f : C(S, ℝ)) (a : ℝ) (p : State S k) :
    testDeviation M hM hk (a • f) p = a * testDeviation M hM hk f p := by
  rw [testDeviation_eq_centered_div, centeredSum_smul, testDeviation_eq_centered_div]
  ring

/-- Gaussian concentration of a literal empirical probability-measure
test, in the expanding deviation range justified by the analytic proof. -/
theorem exists_empirical_gaussian_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R →
        (∀ g : C(S, ℝ), 0 < M.fieldConnectedWeight g k r) ∧
        ∀ g f : C(S, ℝ), Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
          ∀ x : ℝ, 0 ≤ x → x ≤ η * Real.sqrt (k : ℝ) →
          ∀ hC : 0 < M.fieldConnectedWeight g k r,
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

/-- The actual empirical mark of all sampled types in a finite
independent component collection. -/
def pooledMark {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) : ProbabilityMeasure S :=
  typesMark (pooled_card_pos hq k hk) (pooledTypes k p)

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem pooledTypes_measurable {q : ℕ} (k : Fin q → ℕ) :
    Measurable (pooledTypes (S := S) k) := by
  apply measurable_pi_lambda
  intro v
  let w := (Fintype.equivFin ((i : Fin q) × Fin (k i))).symm v
  exact (measurable_pi_apply w.2).comp (measurable_fst.comp (measurable_pi_apply w.1))

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem pooledMark_measurable {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    Measurable (pooledMark (S := S) hq k hk) :=
  (typesMark_measurable _).comp (pooledTypes_measurable k)

theorem pooledMark_open_event_measurable {q : ℕ} (hq : 0 < q)
    (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (U : Set (ProbabilityMeasure S)) (hU : IsOpen U) :
    MeasurableSet {p : StateFamily (S := S) k | pooledMark hq k hk p ∈ U} :=
  (hU.preimage (typesMark_continuous _)).measurableSet.preimage (pooledTypes_measurable k)

omit [CompactSpace S] in
theorem pooledMark_integral {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) (f : C(S, ℝ)) :
    (∫ y, f y ∂(pooledMark hq k hk p : Measure S)) =
      (∑ i, (k i : ℝ))⁻¹ * ∑ i, typeSum f (p i).1 := by
  rw [pooledMark, typesMark_integral, pooled_card_real, typeSum_pooledTypes]

def pooledTestDeviation (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f : C(S, ℝ)) (p : StateFamily (S := S) k) : ℝ :=
  (∫ y, f y ∂(pooledMark hq k hk p : Measure S)) - ∫ y, f y ∂M.perronLaw hM

theorem pooledTestDeviation_eq_scaled_div (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f : C(S, ℝ)) (p : StateFamily (S := S) k) :
    pooledTestDeviation M hM hq k hk f p = pooledSum M hM k f p / Real.sqrt (∑ i, (k i : ℝ)) := by
  have hK := totalSize_pos hq k hk
  have hsqrt : 0 < Real.sqrt (∑ i, (k i : ℝ)) := Real.sqrt_pos.mpr hK
  have hsqrtSq := Real.sq_sqrt hK.le
  rw [pooledTestDeviation, pooledMark_integral, pooledSum]
  simp only [centeredSum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp [hsqrt.ne', hK.ne']
  rw [hsqrtSq]
  ring

/-- Fixed deviations of unit-norm continuous tests have an actual
uniform exponential-in-size probability bound. -/
theorem exists_unit_test_exponential_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g f : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ‖f‖ ≤ 1 →
        ∀ hC : 0 < M.fieldConnectedWeight g k r,
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
theorem exists_test_exponential_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε)
    (f : C(S, ℝ)) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ∀ hC : 0 < M.fieldConnectedWeight g k r,
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
theorem exists_finite_unit_tests_exponential_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∃ hk : 0 < k, ∀ r : ℕ, r ≤ R → ∀ g : C(S, ℝ),
        Real.sqrt (k : ℝ) * ‖g‖ ≤ L → ∀ F : Finset C(S, ℝ),
        (∀ f ∈ F, ‖f‖ ≤ 1) → ∀ hC : 0 < M.fieldConnectedWeight g k r,
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
theorem test_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n))
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
theorem finite_tests_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → ℕ) (hk : ∀ n, 0 < k n) (g : ℕ → C(S, ℝ))
    (hC : ∀ n, 0 < M.fieldConnectedWeight (g n) (k n) (r n))
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

theorem pooledTestDeviation_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {q : ℕ} (hq : 0 < q) (k : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f : C(S, ℝ)) (a : ℝ) (p : StateFamily (S := S) k) :
    pooledTestDeviation M hM hq k hk (a • f) p =
      a * pooledTestDeviation M hM hq k hk f p := by
  rw [pooledTestDeviation_eq_scaled_div, pooledSum_smul, pooledTestDeviation_eq_scaled_div]
  ring

/-- Actual pooled empirical-test concentration, uniformly over all
positive component sizes. Thus bounded-size components are included,
and only the total pooled size needs to diverge. -/
theorem exists_unit_pooled_test_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
      (∀ i, r i ≤ R) → ∀ g : Fin q → C(S, ℝ),
      (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ f : C(S, ℝ), ‖f‖ ≤ 1 → ∀ ε : ℝ,
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      (productLaw M k r g hC).real {p | ε ≤ |pooledTestDeviation M hM hq k hk f p|} ≤
        D * Real.exp (-ε * Real.sqrt (∑ i, (k i : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_pooled_laplace_bound M hM R q L 1 hL (by norm_num)
  refine ⟨2 * B, by positivity, ?_⟩
  intro k r hk hr g hg f hf ε hC
  let μ := productLaw M k r g hC
  let X := pooledSum M hM k f
  have hm : Measurable X := pooledSum_measurable M hM k f
  have hX (p) : |X p| ≤ 2 * Real.sqrt (∑ i, (k i : ℝ)) := by
    exact (pooledSum_abs_le M hM hq k hk f p).trans
      (mul_le_of_le_one_right (by positivity) hf)
  have hint (s : ℝ) : Integrable (fun p ↦ Real.exp (s * X p)) μ := by
    apply integrable_of_measurable_abs_le μ (hm.const_mul s).exp
    intro p
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hX p) (abs_nonneg s))
  have hmabs : Measurable (fun p ↦ |X p|) := by simpa only [Real.norm_eq_abs] using hm.norm
  have hiabs : Integrable (fun p ↦ Real.exp |X p|) μ := by
    apply integrable_of_measurable_abs_le μ hmabs.exp
    intro p
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hX p)
  have hp := hb k r hk hr g hg f hf hC
  have hn := hb k r hk hr g hg (-f) (by simpa only [norm_neg] using hf) hC
  simp only [one_mul, pooledSum_neg] at hp hn
  have hiLinear : Integrable (fun p ↦ Real.exp (X p) + Real.exp (-X p)) μ := by
    apply integrable_of_measurable_abs_le μ (hm.exp.add hm.neg.exp)
      (B := Real.exp (2 * Real.sqrt (∑ i, (k i : ℝ))) +
        Real.exp (2 * Real.sqrt (∑ i, (k i : ℝ))))
    intro p
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [abs_of_nonneg (add_nonneg (Real.exp_pos (X p)).le (Real.exp_pos (-X p)).le)]
    exact add_le_add (Real.exp_le_exp.mpr ((le_abs_self _).trans (hX p)))
      (Real.exp_le_exp.mpr ((neg_le_abs _).trans (hX p)))
  have hmgf : (∫ p, Real.exp |X p| ∂μ) ≤ 2 * B := by
    calc
      _ ≤ ∫ p, Real.exp (X p) + Real.exp (-X p) ∂μ := by
        apply integral_mono hiabs hiLinear
        intro p
        simpa only [one_mul, neg_one_mul] using exp_abs_le_exp_add_exp_neg 1 (X p)
      _ = (∫ p, Real.exp (X p) ∂μ) + ∫ p, Real.exp (-X p) ∂μ :=
        integral_add (by simpa only [one_mul] using hint 1)
          (by simpa only [neg_one_mul] using hint (-1))
      _ ≤ _ := by dsimp only [X, μ]; linarith
  have he := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := fun p ↦ |X p|) (μ := μ) (t := 1)
    (ε * Real.sqrt (∑ i, (k i : ℝ))) (by norm_num)
    (by simpa only [one_mul] using hiabs)
  simp only [ProbabilityTheory.mgf, one_mul, neg_one_mul] at he
  have htotal := totalSize_pos hq k hk
  have hsqrt := Real.sqrt_pos.mpr htotal
  have hsets : {p | ε ≤ |pooledTestDeviation M hM hq k hk f p|} =
      {p | ε * Real.sqrt (∑ i, (k i : ℝ)) ≤ |X p|} := by
    ext p
    simp only [Set.mem_ofPred_eq, pooledTestDeviation_eq_scaled_div, abs_div,
      abs_of_pos hsqrt]
    exact le_div_iff₀ hsqrt
  rw [hsets]
  exact he.trans (by
    have he' := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (-ε * Real.sqrt (∑ i, (k i : ℝ)))).le
    simpa only [neg_mul, mul_comm] using he')

/-- Uniform finite-family pooled concentration under the genuine
independent product law, for every positive component-size vector. -/
theorem exists_finite_unit_pooled_tests_tail_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ k r : Fin q → ℕ, ∀ hk : ∀ i, 0 < k i,
      (∀ i, r i ≤ R) → ∀ g : Fin q → C(S, ℝ),
      (∀ i, Real.sqrt (k i : ℝ) * ‖g i‖ ≤ L) →
      ∀ F : Finset C(S, ℝ), (∀ f ∈ F, ‖f‖ ≤ 1) → ∀ ε : ℝ,
      ∀ hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i),
      (productLaw M k r g hC).real
        {p | ∃ f ∈ F, ε ≤ |pooledTestDeviation M hM hq k hk f p|} ≤
          (F.card : ℝ) * D * Real.exp (-ε * Real.sqrt (∑ i, (k i : ℝ))) := by
  classical
  obtain ⟨D, hD, hb⟩ := exists_unit_pooled_test_tail_bound M hM R q hq L hL
  refine ⟨D, hD, ?_⟩
  intro k r hk hr g hg F hF ε hC
  have hsets : {p : StateFamily (S := S) k | ∃ f ∈ F,
      ε ≤ |pooledTestDeviation M hM hq k hk f p|} =
        ⋃ f ∈ F, {p | ε ≤ |pooledTestDeviation M hM hq k hk f p|} := by ext p; simp
  rw [hsets]
  calc
    _ ≤ ∑ f ∈ F, (productLaw M k r g hC).real
        {p | ε ≤ |pooledTestDeviation M hM hq k hk f p|} := measureReal_biUnion_finset_le F _
    _ ≤ ∑ _f ∈ F, D * Real.exp (-ε * Real.sqrt (∑ i, (k i : ℝ))) :=
      Finset.sum_le_sum (fun f hf ↦ hb k r hk hr g hg f (hF f hf) ε hC)
    _ = _ := by simp; ring

/-- Fixed continuous tests concentrate under the actual independent
product law whenever the total pooled size tends to infinity. -/
theorem pooled_test_probability_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S, ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (f : C(S, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | ε ≤ |pooledTestDeviation M hM hq (k n) (hk n) f p|}) atTop (𝓝 0) := by
  let F : ℝ := ‖f‖ + 1
  have hF : 0 < F := by dsimp only [F]; positivity
  let f₀ : C(S, ℝ) := F⁻¹ • f
  have hf₀ : ‖f₀‖ ≤ 1 := by
    simp only [f₀, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hF)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hF).mpr (by dsimp only [F]; linarith)
  obtain ⟨D, _hD, hb⟩ := exists_unit_pooled_test_tail_bound M hM R q hq L hL
  have hupper : ∀ᶠ n in atTop,
      (productLaw M (k n) (r n) (g n) (hC n)).real
        {p | ε ≤ |pooledTestDeviation M hM hq (k n) (hk n) f p|} ≤
          D * Real.exp (-(ε / F) * Real.sqrt (∑ i, (k n i : ℝ))) := by
    filter_upwards [hr, hg] with n hnr hng
    have he := hb (k n) (r n) (hk n) hnr (g n) hng f₀ hf₀ (ε / F) (hC n)
    have hsets : {p | ε / F ≤ |pooledTestDeviation M hM hq (k n) (hk n) f₀ p|} =
        {p | ε ≤ |pooledTestDeviation M hM hq (k n) (hk n) f p|} := by
      ext p
      simp only [Set.mem_ofPred_eq, f₀, pooledTestDeviation_smul, abs_mul,
        abs_of_pos (inv_pos.mpr hF)]
      rw [← div_eq_inv_mul, div_le_div_iff_of_pos_right hF]
    rwa [hsets] at he
  have hεF : 0 < ε / F := div_pos hε hF
  have hexp : Tendsto (fun n ↦ Real.exp (-(ε / F) * Real.sqrt (∑ i, (k n i : ℝ))))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
    ((Real.tendsto_sqrt_atTop.comp hKTop).const_mul_atTop_of_neg (by linarith))
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hupper
    (by simpa using hexp.const_mul D)

end PerronWright.EmpiricalMarkConcentration
