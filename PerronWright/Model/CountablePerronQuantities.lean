import PerronWright.Kernel.CountableSimplicity

/-!
# Canonical Perron quantities for a regular critical countable kernel

The eigenvector is selected from the proved existence-and-uniqueness
theorem.  Its probability law and positive quadratic/cubic scales are
actual measure-theoretic constructions, not model fields.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace PerronWright.CountableKernel

def IsRegularCritical (M : CountableKernel) : Prop :=
  M.IsCritical ∧ ∃ lower : ℝ, 0 < lower ∧ ∀ a b, lower ≤ M.kernel a b

theorem IsRegularCritical.existsUnique_normalized_positive_fixed
    {M : CountableKernel} (hM : M.IsRegularCritical) :
    ∃! u : M.L2, (∀ a, 0 < u a) ∧ M.actionCLM u = u ∧ (∫ a, u a ∂M.mu) = 1 := by
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  exact M.existsUnique_normalized_positive_fixed hM.1 hlower hlo

def perronVector (M : CountableKernel) (hM : M.IsRegularCritical) : M.L2 :=
  Classical.choose hM.existsUnique_normalized_positive_fixed

theorem perronVector_pos (M : CountableKernel) (hM : M.IsRegularCritical) (a : ℕ) :
    0 < M.perronVector hM a :=
  (Classical.choose_spec hM.existsUnique_normalized_positive_fixed).1.1 a

theorem perronVector_fixed (M : CountableKernel) (hM : M.IsRegularCritical) :
    M.actionCLM (M.perronVector hM) = M.perronVector hM :=
  (Classical.choose_spec hM.existsUnique_normalized_positive_fixed).1.2.1

theorem perronVector_integral (M : CountableKernel) (hM : M.IsRegularCritical) :
    (∫ a, M.perronVector hM a ∂M.mu) = 1 :=
  (Classical.choose_spec hM.existsUnique_normalized_positive_fixed).1.2.2

theorem perronVector_bounds (M : CountableKernel) (hM : M.IsRegularCritical) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ a, lower ≤ M.perronVector hM a ∧ M.perronVector hM a ≤ M.upper := by
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  exact ⟨lower, hlower, M.normalized_fixed_bounds hlo (M.perronVector hM)
    (fun a ↦ (M.perronVector_pos hM a).le) (M.perronVector_fixed hM)
    (M.perronVector_integral hM)⟩

def perronDensity (M : CountableKernel) (hM : M.IsRegularCritical) (a : ℕ) : ℝ≥0 :=
  ⟨M.perronVector hM a, (M.perronVector_pos hM a).le⟩

def perronLaw (M : CountableKernel) (hM : M.IsRegularCritical) : Measure ℕ :=
  M.mu.withDensity (fun a ↦ (M.perronDensity hM a : ℝ≥0∞))

instance perronLaw_isProbability (M : CountableKernel) (hM : M.IsRegularCritical) :
    IsProbabilityMeasure (M.perronLaw hM) := by
  constructor
  rw [perronLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun a ↦ (M.perronDensity hM a : ℝ)) M.mu := M.integrable_input _
  rw [lintegral_coe_eq_integral _ hint]
  change ENNReal.ofReal (∫ a, M.perronVector hM a ∂M.mu) = 1
  rw [M.perronVector_integral hM]
  norm_num

theorem perronLaw_integral (M : CountableKernel) (hM : M.IsRegularCritical) (f : ℕ → ℝ) :
    (∫ a, f a ∂M.perronLaw hM) = ∫ a, M.perronVector hM a * f a ∂M.mu := by
  rw [perronLaw, integral_withDensity_eq_integral_smul (measurable_of_countable _)]
  apply integral_congr_ae
  filter_upwards [] with a
  rfl

theorem perronVector_pow_integrable (M : CountableKernel) (hM : M.IsRegularCritical) (m : ℕ) :
    Integrable (fun a ↦ (M.perronVector hM a) ^ m) M.mu := by
  obtain ⟨lower, hlower, hbounds⟩ := M.perronVector_bounds hM
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (M.upper ^ m)
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (pow_nonneg (M.perronVector_pos hM a).le m)]
  exact pow_le_pow_left₀ (M.perronVector_pos hM a).le (hbounds a).2 m

theorem perronVector_pow_integral_pos (M : CountableKernel) (hM : M.IsRegularCritical) (m : ℕ) :
    0 < ∫ a, (M.perronVector hM a) ^ m ∂M.mu := by
  have hnonneg : ∀ a, 0 ≤ (M.perronVector hM a) ^ m :=
    fun a ↦ (pow_pos (M.perronVector_pos hM a) m).le
  apply lt_of_le_of_ne (integral_nonneg hnonneg)
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
    (M.perronVector_pow_integrable hM m)).mp hz.symm
  have h0 := M.forall_of_ae hae 0
  exact (pow_pos (M.perronVector_pos hM 0) m).ne' h0

def alpha (M : CountableKernel) (hM : M.IsRegularCritical) : ℝ :=
  ∫ a, (M.perronVector hM a) ^ 2 ∂M.mu

def beta (M : CountableKernel) (hM : M.IsRegularCritical) : ℝ :=
  ∫ a, (M.perronVector hM a) ^ 3 ∂M.mu

theorem alpha_pos (M : CountableKernel) (hM : M.IsRegularCritical) : 0 < M.alpha hM :=
  M.perronVector_pow_integral_pos hM 2

theorem beta_pos (M : CountableKernel) (hM : M.IsRegularCritical) : 0 < M.beta hM :=
  M.perronVector_pow_integral_pos hM 3

end PerronWright.CountableKernel
