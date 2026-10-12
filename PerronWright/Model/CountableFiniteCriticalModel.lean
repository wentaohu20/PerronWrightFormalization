import PerronWright.Model.CountablePerronQuantitiesMoments
import PerronWright.Model.FiniteIrreduciblePerronQuantities
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! # Actual spectral-normalized finite supports of a countable kernel

The retained law and literal restricted kernel construct a finite model.
Its criticality is proved from the already constructed finite-law Perron
function and a bound on every genuine matrix eigenvalue. No critical
finite-model adapter or spectral identification is assumed.
-/

open scoped BigOperators ENNReal
noncomputable section

namespace PerronWright.CountableKernel

def extendFinite (s : Finset ℕ) (f : s → ℝ) (a : ℕ) : ℝ :=
  if ha : a ∈ s then f ⟨a, ha⟩ else 0

@[simp] theorem extendFinite_apply (s : Finset ℕ) (f : s → ℝ) (a : s) :
    extendFinite s f a = f a := by simp [extendFinite, a.property]

def finiteCriticalModel (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    FiniteIrreducibleModel s where
  weight a := w a
  weight_pos a := hpos a a.property
  weight_sum := by
    have he : (∑' a, w a) = ∑ a ∈ s, w a := tsum_eq_sum hzero
    rw [Finset.sum_coe_sort, ← he, hs.tsum_eq]
  kernel a b := M.kernel a b / M.weightedSpectralRadius w hw hs
  symmetric a b := by rw [M.symmetric]
  irreducible := by
    have hr := (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1
    let A : Matrix s s ℝ := fun a b ↦ M.kernel a b / M.weightedSpectralRadius w hw hs
    change A.IsIrreducible
    apply (Matrix.isIrreducible_iff_exists_pow_pos (A := A)
      (fun a b : s ↦ (div_pos (hlower.trans_le (hlo a b)) hr).le)).mpr
    intro a b
    exact ⟨1, by omega, by rw [pow_one]; exact div_pos (hlower.trans_le (hlo a b)) hr⟩

theorem finiteCriticalModel_action (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (f : s → ℝ) (a : s) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).action f a =
      M.finiteLawAction s w (extendFinite s f) a / M.weightedSpectralRadius w hw hs := by
  rw [FiniteIrreducibleModel.action, finiteLawAction,
    ← Finset.sum_coe_sort s (fun b ↦ M.kernel a b * w b * extendFinite s f b),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  simp only [finiteCriticalModel, extendFinite_apply]
  ring

theorem finiteCriticalModel_perron_fixed (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).action
      (fun a : s ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a) =
      fun a : s ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a := by
  funext a
  rw [M.finiteCriticalModel_action]
  have he : M.finiteLawAction s w
      (extendFinite s (fun a : s ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a)) a =
      M.finiteLawAction s w (M.finitePerronFunction w hw hs s hzero hlower hlo) a := by
    apply Finset.sum_congr rfl
    intro b hb
    simp [extendFinite, hb]
  rw [he, M.finitePerronFunction_eigen,
    mul_div_cancel_left₀ _ (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1.ne']

/-- Actual matrix spectral criticality of the retained, spectrally normalized
model. The upper bound uses all real spectral values, including negatives. -/
theorem finiteCriticalModel_isCritical (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (hpos : ∀ a ∈ s, 0 < w a)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    (M.finiteCriticalModel w hw hs s hzero hpos hlower hlo).IsCritical := by
  let F := M.finiteCriticalModel w hw hs s hzero hpos hlower hlo
  let σ := M.weightedSpectralRadius w hw hs
  have hσ : 0 < σ := (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1
  change spectralRadius ℝ F.meanMatrix = 1
  apply le_antisymm
  · apply iSup₂_le
    intro lam hlam
    have hl : lam ∈ spectrum ℝ F.meanMatrix.toLin' := by
      rwa [Matrix.spectrum_toLin']
    obtain ⟨f, hf, hfne⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hl).exists_hasEigenvector
    have he : F.action f = lam • f := by
      rw [F.action_eq_meanMatrix_mulVec]
      exact Module.End.mem_eigenspace_iff.mp hf
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hfne
    have hne : ∃ a ∈ s, 0 < w a ∧ extendFinite s f a ≠ 0 :=
      ⟨a, a.property, hpos a a.property, by simpa using ha⟩
    have hev : ∀ a ∈ s, M.finiteLawAction s w (extendFinite s f) a =
        (σ * lam) * extendFinite s f a := by
      intro a ha
      have h := congrFun he ⟨a, ha⟩
      rw [M.finiteCriticalModel_action] at h
      have h' := (div_eq_iff hσ.ne').mp h
      simpa [extendFinite, ha, σ, mul_assoc, mul_comm, mul_left_comm] using h'
    have hb := M.finiteLaw_eigenvalue_abs_le w hw hs s hzero (extendFinite s f) hne hev
    have hlabs : |lam| ≤ 1 := by
      rw [abs_mul, abs_of_pos hσ] at hb
      nlinarith
    have hn : ‖lam‖₊ ≤ (1 : NNReal) := by exact_mod_cast hlabs
    exact_mod_cast hn
  · let u : s → ℝ := fun a ↦ M.finitePerronFunction w hw hs s hzero hlower hlo a
    have hu : u ≠ 0 := by
      let a := Classical.choice F.nonempty
      intro hz
      have hp := (M.finitePerronFunction_bounds w hw hs s hzero hlower hlo a).1
      have he := congrFun hz a
      change u a = 0 at he
      exact hp.ne' he
    have hfix : F.meanMatrix.toLin' u = (1 : ℝ) • u := by
      rw [Matrix.toLin'_apply, ← F.action_eq_meanMatrix_mulVec,
        M.finiteCriticalModel_perron_fixed]
      simp only [one_smul, u]
    have hev : Module.End.HasEigenvalue F.meanMatrix.toLin' 1 :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hfix, hu⟩
    have hm : (1 : ℝ) ∈ spectrum ℝ F.meanMatrix := by
      rw [← Matrix.spectrum_toLin']
      exact hev.mem_spectrum
    have hh : (‖(1 : ℝ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ F.meanMatrix :=
      le_iSup_of_le (1 : ℝ) (le_iSup_of_le hm
        (le_refl (‖(1 : ℝ)‖₊ : ℝ≥0∞)))
    simpa only [nnnorm_one, ENNReal.coe_one] using hh

end PerronWright.CountableKernel
