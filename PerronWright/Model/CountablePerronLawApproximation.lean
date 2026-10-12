import PerronWright.Kernel.CountableApproximationEmpirical

/-!
# Actual atomic Perron-law convergence

The finite-law Perron mark is the literal atomic probability measure
with masses `w(a) f_w(a)`.  Full atomic variation of the input laws,
the proved pointwise Perron convergence, and boundedness imply full
atomic variation of the Perron marks.  No convergence of mark measures
is assumed as an interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

namespace PerronWright.CountableKernel

theorem atomic_product_error_le (M : CountableKernel) (w : ℕ → ℝ)
    (_hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (f g : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ C)
    (hg : ∀ a, 0 ≤ g a ∧ g a ≤ C) :
    (∑' a, |w a * f a - M.mu.real {a} * g a|) ≤
      C * ∑' a, |w a - M.mu.real {a}| + ∫ a, |f a - g a| ∂M.mu := by
  have hvar := (hs.summable.sub M.atomMass_hasSum.summable).abs
  have hdiff (a : ℕ) : |f a - g a| ≤ 2 * C := by
    rw [abs_le]
    constructor <;> linarith [(hf a).1, (hf a).2, (hg a).1, (hg a).2]
  have hd : Summable (fun a ↦ M.mu.real {a} * |f a - g a|) := by
    apply (M.atomMass_hasSum.summable.mul_left (2 * C)).of_nonneg_of_le
      (fun a ↦ mul_nonneg (M.atomMass_pos a).le (abs_nonneg _))
    intro a
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hdiff a) (M.atomMass_pos a).le
  have hsum := (hvar.mul_left C).add hd
  have hb (a : ℕ) : |w a * f a - M.mu.real {a} * g a| ≤
      C * |w a - M.mu.real {a}| + M.mu.real {a} * |f a - g a| := by
    calc
      _ = |(w a - M.mu.real {a}) * f a + M.mu.real {a} * (f a - g a)| := by ring_nf
      _ ≤ |(w a - M.mu.real {a}) * f a| + |M.mu.real {a} * (f a - g a)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hf a).1,
          abs_of_nonneg (M.atomMass_pos a).le]
        exact add_le_add (by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hf a).2 (abs_nonneg _)) le_rfl
  have herr : Summable (fun a ↦ |w a * f a - M.mu.real {a} * g a|) :=
    hsum.of_nonneg_of_le (fun a ↦ abs_nonneg _) hb
  calc
    _ ≤ ∑' a, (C * |w a - M.mu.real {a}| + M.mu.real {a} * |f a - g a|) :=
      herr.tsum_le_tsum hb hsum
    _ = _ := by
      rw [(hvar.mul_left C).tsum_add hd, tsum_mul_left, M.integral_eq_tsum_atom]

theorem atomic_product_error_tendsto (M : CountableKernel) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (𝓝 0))
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n a, 0 ≤ f n a ∧ f n a ≤ C)
    (hg : ∀ a, 0 ≤ g a ∧ g a ≤ C)
    (ht : ∀ a, Tendsto (fun n ↦ f n a) atTop (𝓝 (g a))) :
    Tendsto (fun n ↦ ∑' a, |w n a * f n a - M.mu.real {a} * g a|)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n ↦ ∫ a, |f n a - g a| ∂M.mu) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := M.mu) (fun _ : ℕ ↦ 2 * C)
      (fun n ↦ (measurable_of_countable (fun a ↦ |f n a - g a|)).aestronglyMeasurable)
      (integrable_const (2 * C : ℝ))
      (fun n ↦ Eventually.of_forall (fun a ↦ show ‖|f n a - g a|‖ ≤ 2 * C from by
        rw [Real.norm_of_nonneg (abs_nonneg _), abs_le]
        constructor <;> linarith [(hf n a).1, (hf n a).2, (hg a).1, (hg a).2]))
      (Eventually.of_forall (fun a ↦ show Tendsto (fun n ↦ |f n a - g a|) atTop (𝓝 (0 : ℝ)) from by
        simpa only [sub_self, abs_zero] using ((ht a).sub_const (g a)).abs))
    simpa only [integral_zero] using h
  apply squeeze_zero (fun n ↦ tsum_nonneg (fun _ ↦ abs_nonneg _))
    (fun n ↦ M.atomic_product_error_le (w n) (hw n) (hs n) (f n) g hC (hf n) hg)
  simpa only [mul_zero, zero_add] using (herr.const_mul C).add hi

/-- The actual finite Perron-law mass, extended by zero outside its
retained support through the input weights. -/
def finitePerronLaw (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : Measure ℕ :=
  Measure.sum (fun a ↦ ENNReal.ofReal (w a *
    M.finitePerronFunction w hw hs s hzero hlower hlo a) • Measure.dirac a)

theorem finitePerronLaw_atom (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    (M.finitePerronLaw w hw hs s hzero hlower hlo).real {a} =
      w a * M.finitePerronFunction w hw hs s hzero hlower hlo a := by
  rw [measureReal_def, finitePerronLaw, Measure.sum_smul_dirac_singleton,
    ENNReal.toReal_ofReal]
  exact mul_nonneg (hw a) (M.finitePerronFunction_bounds w hw hs s hzero hlower hlo a).1.le

instance finitePerronLaw_isProbability (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    IsProbabilityMeasure (M.finitePerronLaw w hw hs s hzero hlower hlo) := by
  constructor
  rw [finitePerronLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun a ↦ mul_nonneg (hw a) (M.finitePerronFunction_bounds w hw hs s hzero hlower hlo a).1.le)
    (M.finitePerronFunction_hasSum_one w hw hs s hzero hlower hlo).summable,
    (M.finitePerronFunction_hasSum_one w hw hs s hzero hlower hlo).tsum_eq]
  norm_num

theorem perronLaw_atom (M : CountableKernel) (hM : M.IsRegularCritical) (a : ℕ) :
    (M.perronLaw hM).real {a} = M.mu.real {a} * M.perronVector hM a := by
  rw [measureReal_def, perronLaw, withDensity_apply _ (measurableSet_singleton a),
    lintegral_singleton, ENNReal.toReal_mul]
  rw [ENNReal.coe_toReal]
  change M.perronVector hM a * (M.mu {a}).toReal = (M.mu {a}).toReal * M.perronVector hM a
  ring

theorem finitePerronLaw_atomic_variation_tendsto (M : CountableKernel)
    (hM : M.IsRegularCritical) (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a)
    (hs : ∀ n, HasSum (w n) 1) (s : ℕ → Finset ℕ)
    (hzero : ∀ n a, a ∉ s n → w n a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑' a, |(M.finitePerronLaw (w n) (hw n) (hs n) (s n)
      (hzero n) hlower hlo).real {a} - (M.perronLaw hM).real {a}|) atTop (𝓝 0) := by
  simp_rw [M.finitePerronLaw_atom, M.perronLaw_atom]
  let C := max (M.upper / lower) M.upper
  apply M.atomic_product_error_tendsto w hw hs herr _ _ (C := C)
    (le_trans (div_nonneg M.upper_nonneg hlower.le) (le_max_left (M.upper / lower) M.upper))
  · intro n a
    have hb := M.finitePerronFunction_bounds (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo a
    exact ⟨hb.1.le, hb.2.trans (le_max_left (M.upper / lower) M.upper)⟩
  · intro a
    obtain ⟨_, _, hb⟩ := M.perronVector_bounds hM
    exact ⟨(M.perronVector_pos hM a).le, (hb a).2.trans (le_max_right (M.upper / lower) M.upper)⟩
  · exact M.finitePerronFunction_tendsto hM w hw hs s hzero hlower hlo herr

theorem probability_set_real_eq_tsum_indicator (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (s : Set ℕ) : mu.real s = ∑' a, s.indicator (fun a ↦ mu.real {a}) a := by
  have hi := integral_sum_dirac (f := s.indicator (1 : ℕ → ℝ)) (x := fun a : ℕ ↦ a)
    (c := fun a ↦ mu {a}) (fun a ↦ measure_ne_top mu {a})
  rw [mu.sum_smul_dirac] at hi
  rw [← integral_indicator_one s.to_countable.measurableSet]
  rw [hi]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ s <;> simp [ha, measureReal_def]

/-- Full atomic absolute variation controls every event, uniformly over
all subsets of the countable type space. -/
theorem probability_set_error_le_atomic_variation (mu nu : Measure ℕ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (s : Set ℕ) :
    |mu.real s - nu.real s| ≤ ∑' a, |mu.real {a} - nu.real {a}| := by
  have hmu := (probability_atomMass_hasSum mu).summable.indicator s
  have hnu := (probability_atomMass_hasSum nu).summable.indicator s
  have hs := ((probability_atomMass_hasSum mu).summable.sub
    (probability_atomMass_hasSum nu).summable).abs
  rw [probability_set_real_eq_tsum_indicator mu s, probability_set_real_eq_tsum_indicator nu s,
    ← hmu.tsum_sub hnu]
  calc
    _ ≤ ∑' a, ‖s.indicator (fun a ↦ mu.real {a}) a - s.indicator (fun a ↦ nu.real {a}) a‖ :=
      norm_tsum_le_tsum_norm (hmu.sub hnu).norm
    _ ≤ _ := (hmu.sub hnu).norm.tsum_le_tsum (fun a ↦ by
      by_cases ha : a ∈ s <;> simp [ha, Real.norm_eq_abs]) hs

theorem finitePerronLaw_uniform_event_convergence (M : CountableKernel)
    (hM : M.IsRegularCritical) (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a)
    (hs : ∀ n, HasSum (w n) 1) (s : ℕ → Finset ℕ)
    (hzero : ∀ n a, a ∉ s n → w n a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ A : Set ℕ,
      |(M.finitePerronLaw (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo).real A -
        (M.perronLaw hM).real A| < ε := by
  intro ε hε
  filter_upwards [(M.finitePerronLaw_atomic_variation_tendsto hM w hw hs s hzero
    hlower hlo herr).eventually (Iio_mem_nhds hε)] with n hn
  intro A
  exact (probability_set_error_le_atomic_variation _ _ A).trans_lt hn

def empiricalPerronLaw (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : Measure ℕ :=
  M.finitePerronLaw (M.empiricalWeights level n) (M.empiricalWeights_nonneg level n)
    (M.empiricalWeights_hasSum level n) (Finset.range (level (n + 1) + 1))
    (M.empiricalWeights_finite_support level n) hlower hlo

instance empiricalPerronLaw_isProbability (M : CountableKernel) (level : ℕ → ℕ) (n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    IsProbabilityMeasure (M.empiricalPerronLaw level n hlower hlo) := by
  unfold empiricalPerronLaw
  infer_instance

/-- Actual positive integer-count empirical realizations have Perron
probability marks converging in full atomic absolute variation. -/
theorem exists_empirical_perron_law_realization (M : CountableKernel)
    (hM : M.IsRegularCritical) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      ∃ (lower : ℝ) (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b),
        Tendsto (fun n ↦ ∑' a, |(M.empiricalPerronLaw level n hlower hlo).real {a} -
          (M.perronLaw hM).real {a}|) atTop (𝓝 0) := by
  obtain ⟨level, hm, ht, _, _, _, herr, _⟩ :=
    CountableTypeRealization.exists_positive_empirical_realization M
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  have he : Tendsto (fun n ↦ ∑' a, |M.empiricalWeights level n a - M.mu.real {a}|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, empiricalWeights] using herr.comp (tendsto_add_atTop_nat 1)
  exact ⟨level, hm, ht, lower, hlower, hlo, M.finitePerronLaw_atomic_variation_tendsto
    hM _ (M.empiricalWeights_nonneg level) (M.empiricalWeights_hasSum level) _
    (M.empiricalWeights_finite_support level) hlower hlo he⟩

end PerronWright.CountableKernel
