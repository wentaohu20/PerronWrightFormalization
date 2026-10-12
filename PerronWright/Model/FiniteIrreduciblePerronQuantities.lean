import PerronWright.Kernel.FiniteIrreduciblePerron

/-!
# Actual finite-law Perron functions and quantities

The square-root diagonal change of coordinates is a constructed linear
equivalence.  Positive fixed functions, their unique type-law
normalization and the finite quadratic/cubic quantities are proved from
literal irreducibility and matrix spectral criticality.
-/

open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

def action (M : FiniteIrreducibleModel S) (f : S → ℝ) (a : S) : ℝ :=
  ∑ b, M.kernel a b * M.weight b * f b

theorem action_eq_meanMatrix_mulVec (M : FiniteIrreducibleModel S) (f : S → ℝ) :
    M.action f = Matrix.mulVec M.meanMatrix f := by
  funext a
  simp [action, Matrix.mulVec, dotProduct]

def toHilbert (M : FiniteIrreducibleModel S) : (S → ℝ) ≃ₗ[ℝ] M.Hilbert where
  toFun f := WithLp.toLp 2 (fun a ↦ M.sqrtWeight a * f a)
  invFun v := fun a ↦ v a / M.sqrtWeight a
  left_inv f := by
    funext a
    exact mul_div_cancel_left₀ _ (M.sqrtWeight_pos a).ne'
  right_inv v := by
    apply (WithLp.ext_iff 2).mpr
    funext a
    change M.sqrtWeight a * (v a / M.sqrtWeight a) = v a
    exact mul_div_cancel₀ _ (M.sqrtWeight_pos a).ne'
  map_add' f g := by
    apply (WithLp.ext_iff 2).mpr
    funext a
    change M.sqrtWeight a * (f a + g a) = M.sqrtWeight a * f a + M.sqrtWeight a * g a
    ring
  map_smul' c f := by
    apply (WithLp.ext_iff 2).mpr
    funext a
    change M.sqrtWeight a * (c * f a) = c * (M.sqrtWeight a * f a)
    ring

@[simp] theorem toHilbert_apply (M : FiniteIrreducibleModel S) (f : S → ℝ) (a : S) :
    M.toHilbert f a = M.sqrtWeight a * f a := rfl

@[simp] theorem toHilbert_symm_apply (M : FiniteIrreducibleModel S) (v : M.Hilbert) (a : S) :
    M.toHilbert.symm v a = v a / M.sqrtWeight a := rfl

theorem toHilbert_intertwines (M : FiniteIrreducibleModel S) (f : S → ℝ) :
    M.operator (M.toHilbert f) = M.toHilbert (M.action f) := by
  apply (WithLp.ext_iff 2).mpr
  funext a
  change M.operator (M.toHilbert f) a = M.toHilbert (M.action f) a
  rw [M.operator_apply, M.toHilbert_apply]
  simp_rw [M.toHilbert_apply]
  rw [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← M.sqrtWeight_sq b]
  change M.sqrtWeight a * M.kernel a b * M.sqrtWeight b * (M.sqrtWeight b * f b) = _
  ring

theorem exists_positive_fixed_function (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ f : S → ℝ, (∀ a, 0 < f a) ∧ M.action f = f := by
  obtain ⟨v, _, hv, hfix⟩ := M.exists_positive_fixed hcrit
  refine ⟨M.toHilbert.symm v, ?_, ?_⟩
  · intro a
    exact div_pos (hv a) (M.sqrtWeight_pos a)
  · apply M.toHilbert.injective
    rw [← M.toHilbert_intertwines, M.toHilbert.apply_symm_apply, hfix]

theorem fixed_function_eq_scalar_multiple (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (u : S → ℝ) (hu : ∀ a, 0 < u a) (hTu : M.action u = u)
    (v : S → ℝ) (hTv : M.action v = v) : ∃ c : ℝ, v = c • u := by
  have hup : ∀ a, 0 < M.toHilbert u a := fun a ↦ mul_pos (M.sqrtWeight_pos a) (hu a)
  have hut : M.operator (M.toHilbert u) = M.toHilbert u := by rw [M.toHilbert_intertwines, hTu]
  have hvt : M.operator (M.toHilbert v) = M.toHilbert v := by rw [M.toHilbert_intertwines, hTv]
  obtain ⟨c, hc⟩ := M.fixed_eq_scalar_multiple hcrit _ hup hut _ hvt
  refine ⟨c, M.toHilbert.injective ?_⟩
  rw [map_smul]
  exact hc

def average (M : FiniteIrreducibleModel S) (f : S → ℝ) : ℝ := ∑ a, M.weight a * f a

theorem average_pos (M : FiniteIrreducibleModel S) (f : S → ℝ) (hf : ∀ a, 0 < f a) :
    0 < M.average f := by
  let _ := M.nonempty
  exact Finset.sum_pos (fun a _ ↦ mul_pos (M.weight_pos a) (hf a)) Finset.univ_nonempty

theorem average_smul (M : FiniteIrreducibleModel S) (f : S → ℝ) (c : ℝ) :
    M.average (c • f) = c * M.average f := by
  simp [average, Finset.mul_sum, mul_comm, mul_assoc]

theorem action_smul (M : FiniteIrreducibleModel S) (f : S → ℝ) (c : ℝ) :
    M.action (c • f) = c • M.action f := by
  funext a
  simp [action, Finset.mul_sum, mul_comm, mul_assoc]

theorem existsUnique_normalized_positive_fixed_function (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∃! f : S → ℝ, (∀ a, 0 < f a) ∧ M.action f = f ∧ M.average f = 1 := by
  obtain ⟨v, hvpos, hvfix⟩ := M.exists_positive_fixed_function hcrit
  have hvav := M.average_pos v hvpos
  let u := (M.average v)⁻¹ • v
  have hup : ∀ a, 0 < u a := fun a ↦ mul_pos (inv_pos.mpr hvav) (hvpos a)
  have huf : M.action u = u := by rw [action_smul, hvfix]
  have hua : M.average u = 1 := by rw [average_smul, inv_mul_cancel₀ hvav.ne']
  refine ⟨u, ⟨hup, huf, hua⟩, ?_⟩
  intro f hf
  obtain ⟨c, hc⟩ := M.fixed_function_eq_scalar_multiple hcrit u hup huf f hf.2.1
  have he : c = 1 := by
    have hfa := hf.2.2
    rw [hc, M.average_smul, hua, mul_one] at hfa
    exact hfa
  simpa [he] using hc

def perronFunction (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : S → ℝ :=
  Classical.choose (M.existsUnique_normalized_positive_fixed_function hcrit)

theorem perronFunction_pos (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (a : S) :
    0 < M.perronFunction hcrit a :=
  (Classical.choose_spec (M.existsUnique_normalized_positive_fixed_function hcrit)).1.1 a

theorem perronFunction_fixed (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.action (M.perronFunction hcrit) = M.perronFunction hcrit :=
  (Classical.choose_spec (M.existsUnique_normalized_positive_fixed_function hcrit)).1.2.1

theorem perronFunction_average (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.average (M.perronFunction hcrit) = 1 :=
  (Classical.choose_spec (M.existsUnique_normalized_positive_fixed_function hcrit)).1.2.2

def alpha (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : ℝ :=
  M.average (fun a ↦ M.perronFunction hcrit a ^ 2)

def beta (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : ℝ :=
  M.average (fun a ↦ M.perronFunction hcrit a ^ 3)

theorem alpha_pos (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : 0 < M.alpha hcrit :=
  M.average_pos _ (fun a ↦ pow_pos (M.perronFunction_pos hcrit a) 2)

theorem beta_pos (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : 0 < M.beta hcrit :=
  M.average_pos _ (fun a ↦ pow_pos (M.perronFunction_pos hcrit a) 3)

end PerronWright.FiniteIrreducibleModel
