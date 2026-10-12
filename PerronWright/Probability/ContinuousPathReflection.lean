import PerronWright.Probability.DyadicGeometricExtension
import Mathlib.Topology.Order.Compact

/-!
# Actual running minima and reflection of continuous paths

The minimum is taken over the literal time interval `[0,t]`, and its
continuity is proved by rescaling that interval to `[0,1]`. Reflection
therefore has genuine continuous nonnegative paths. These deterministic
results will be applied to the constructed Brownian path with parabolic
drift; they do not assume a stochastic reflection or excursion theorem.
-/

open Topology
open scoped NNReal

noncomputable section

namespace PerronWright.ContinuousPathReflection

def runningMinimum (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := sInf (f '' Set.Icc 0 t)

def reflected (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := f t - runningMinimum f t

theorem rescaled_image (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    f '' Set.Icc 0 t = (fun u : ℝ≥0 ↦ f (t * u)) '' Set.Icc 0 1 := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases ht : t = 0
    · have hsz : s = 0 := le_antisymm (ht ▸ hs.2) zero_le
      refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
      simp [ht, hsz]
    · refine ⟨s / t, ⟨zero_le, ?_⟩, ?_⟩
      · exact (div_le_iff₀ (lt_of_le_of_ne zero_le (Ne.symm ht))).mpr (by simpa using hs.2)
      · dsimp only
        rw [mul_div_cancel₀ _ ht]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨t * u, ⟨zero_le, ?_⟩, rfl⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 (zero_le : 0 ≤ t)

theorem continuous_runningMinimum {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    Continuous (runningMinimum f) := by
  have h : Continuous (fun p : ℝ≥0 × ℝ≥0 ↦ f (p.1 * p.2)) :=
    hf.comp (continuous_fst.mul continuous_snd)
  have hc := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1)).continuous_sInf
    (f := fun t u : ℝ≥0 ↦ f (t * u)) h
  have he : (fun t ↦ sInf ((fun u : ℝ≥0 ↦ f (t * u)) '' Set.Icc 0 1)) =
      runningMinimum f := by
    funext t
    exact congrArg sInf (rescaled_image f t).symm
  rw [he] at hc
  exact hc

theorem runningMinimum_attained {f : ℝ≥0 → ℝ} (hf : Continuous f) (t : ℝ≥0) :
    ∃ s ∈ Set.Icc 0 t, runningMinimum f t = f s := by
  obtain ⟨s, hs, he⟩ := isCompact_Icc.exists_sInf_image_eq_and_le
    (Set.nonempty_Icc.mpr (zero_le : 0 ≤ t)) hf.continuousOn
  exact ⟨s, hs, he.1⟩

theorem runningMinimum_le {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {s t : ℝ≥0} (hs : s ≤ t) : runningMinimum f t ≤ f s := by
  exact csInf_le (isCompact_Icc.bddBelow_image hf.continuousOn)
    (Set.mem_image_of_mem f ⟨zero_le, hs⟩)

theorem runningMinimum_antitone {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    Antitone (runningMinimum f) := by
  intro s t hst
  obtain ⟨u, hu, he⟩ := runningMinimum_attained hf s
  rw [he]
  exact runningMinimum_le hf (hu.2.trans hst)

theorem runningMinimum_uniform_bound {f g : ℝ≥0 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ≥0) {ε : ℝ}
    (h : ∀ s : ℝ≥0, s ≤ t → |f s - g s| ≤ ε) :
    |runningMinimum f t - runningMinimum g t| ≤ ε := by
  obtain ⟨u, hu, he_u⟩ := runningMinimum_attained hf t
  obtain ⟨v, hv, he_v⟩ := runningMinimum_attained hg t
  have hmin_f := runningMinimum_le hf hv.2
  have hmin_g := runningMinimum_le hg hu.2
  have hu_bound := abs_le.mp (h u hu.2)
  have hv_bound := abs_le.mp (h v hv.2)
  apply abs_le.mpr
  constructor <;> linarith

theorem reflected_uniform_bound {f g : ℝ≥0 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ≥0) {ε : ℝ}
    (h : ∀ s : ℝ≥0, s ≤ t → |f s - g s| ≤ ε) :
    |reflected f t - reflected g t| ≤ 2 * ε := by
  have ht := abs_le.mp (h t le_rfl)
  have hm := abs_le.mp (runningMinimum_uniform_bound hf hg t h)
  apply abs_le.mpr
  dsimp [reflected]
  constructor <;> linarith

@[simp] theorem runningMinimum_zero (f : ℝ≥0 → ℝ) : runningMinimum f 0 = f 0 := by
  simp [runningMinimum]

theorem continuous_reflected {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    Continuous (reflected f) := hf.sub (continuous_runningMinimum hf)

theorem reflected_nonneg {f : ℝ≥0 → ℝ} (hf : Continuous f) (t : ℝ≥0) :
    0 ≤ reflected f t := sub_nonneg.mpr (runningMinimum_le hf le_rfl)

@[simp] theorem reflected_zero (f : ℝ≥0 → ℝ) : reflected f 0 = 0 := by
  simp [reflected]

theorem isOpen_positive_reflected {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    IsOpen {t | 0 < reflected f t} :=
  isOpen_lt continuous_const (continuous_reflected hf)

def parabolicDrift (lambda : ℝ) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f t + lambda * (t : ℝ) - (t : ℝ) ^ 2 / 2

theorem continuous_parabolicDrift {f : ℝ≥0 → ℝ} (hf : Continuous f) (lambda : ℝ) :
    Continuous (parabolicDrift lambda f) := by
  exact (hf.add (continuous_const.mul NNReal.continuous_coe)).sub
    ((NNReal.continuous_coe.pow 2).div_const 2)

/-- The literal parabolic-drift reflection has continuous, nonnegative
paths and open positivity sets; no Brownian density identity is asserted. -/
theorem reflected_parabolic_properties {f : ℝ≥0 → ℝ} (hf : Continuous f) (lambda : ℝ) :
    Continuous (reflected (parabolicDrift lambda f)) ∧
      (∀ t, 0 ≤ reflected (parabolicDrift lambda f) t) ∧
      IsOpen {t | 0 < reflected (parabolicDrift lambda f) t} := by
  have hd := continuous_parabolicDrift hf lambda
  exact ⟨continuous_reflected hd, reflected_nonneg hd, isOpen_positive_reflected hd⟩

end PerronWright.ContinuousPathReflection
