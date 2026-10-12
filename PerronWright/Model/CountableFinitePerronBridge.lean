import PerronWright.Model.CountableFiniteCriticalModel

/-! # Canonical Perron quantities of the actual finite retained model

Uniqueness of the normalized finite Perron function identifies it with
the already constructed finite-law function on the original countable
space. Consequently the quadratic and cubic quantities are the actual
finite-law moments, not independently chosen approximation parameters.
-/

open scoped BigOperators
noncomputable section

namespace PerronWright.CountableKernel

theorem finiteCriticalModel_perronFunction (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (hF : (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).perronFunction hF =
      fun a : s ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a := by
  let F := M.finiteCriticalModel w hw hs s hzero hpos hlower hlo
  let u : s → ℝ := fun a ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a
  have hposu : ∀ a, 0 < u a := fun a ↦
    (M.finitePerronFunction_bounds w hw hs s hzero hlower hlo a).1
  have hfix : F.action u = u := M.finiteCriticalModel_perron_fixed w hw hs s hzero hpos hlower hlo
  have hav : F.average u = 1 := by
    have he : (∑' a, w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) =
        ∑ a ∈ s, w a * M.finitePerronFunction w hw hs s hzero hlower hlo a :=
      tsum_eq_sum (fun a ha ↦ by rw [hzero a ha, zero_mul])
    change (∑ a : s, w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) = 1
    rw [Finset.sum_coe_sort s (fun a ↦ w a * M.finitePerronFunction w hw hs s hzero hlower hlo a), ← he,
      (M.finitePerronFunction_hasSum_one w hw hs s hzero hlower hlo).tsum_eq]
  exact ((Classical.choose_spec (F.existsUnique_normalized_positive_fixed_function hF)).2
    u ⟨hposu, hfix, hav⟩).symm

theorem finiteCriticalModel_perronMoment (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (hF : (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical) (m : ℕ) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).average
      (fun a ↦ (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).perronFunction hF a ^ m) =
      M.finitePerronMoment w hw hs s hzero hlower hlo m := by
  rw [FiniteIrreducibleModel.average, M.finiteCriticalModel_perronFunction]
  change (∑ a : s, w a * M.finitePerronFunction w hw hs s hzero hlower hlo a ^ m) = _
  rw [Finset.sum_coe_sort s (fun a ↦ w a * M.finitePerronFunction w hw hs s hzero hlower hlo a ^ m)]
  unfold finitePerronMoment
  exact (tsum_eq_sum (fun a ha ↦ by rw [hzero a ha, zero_mul])).symm

theorem finiteCriticalModel_alpha (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (hF : (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).alpha hF =
      M.finitePerronMoment w hw hs s hzero hlower hlo 2 :=
  M.finiteCriticalModel_perronMoment w hw hs s hzero hpos hlower hlo hF 2

theorem finiteCriticalModel_beta (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (hF : (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).beta hF =
      M.finitePerronMoment w hw hs s hzero hlower hlo 3 :=
  M.finiteCriticalModel_perronMoment w hw hs s hzero hpos hlower hlo hF 3

end PerronWright.CountableKernel
