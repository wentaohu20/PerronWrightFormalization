import PerronWright.Probability.BrownianFullHorizonPoissonMarks
import PerronWright.Probability.BrownianClippedExcursionPoissonMarks

/-!
# Actual full-excursion conditional moments and finite-window consistency

The finite mark law and its mixed factorial moments follow from the
constructed independent Poisson measures at the genuine full areas.
On the proved Brownian full set, every fixed finite set of rational
coordinates agrees exactly with all sufficiently large clipped windows.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianFullHorizonMarkMoments

open BrownianPathLaw BrownianGaussianSkeleton
open BrownianFullHorizonExcursionAreas BrownianFullHorizonPoissonMarks

theorem markLaw_hasLaw_restrict (lambda : ℝ) (f : Path) (I : Finset ℚ) :
    HasLaw (fun m : ℕ → ℕ ↦ fun q : I ↦ rationalCount m q)
      (PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q lambda f))
      (markLaw lambda f) := by
  exact (iIndepFun.precomp Subtype.val_injective
    (markLaw_rationalCounts_independent lambda f)).hasLaw_pi
      (fun q : I ↦ markLaw_hasLaw_rationalCount lambda f q)

/-- All actual conditional mixed factorial moments, including order zero. -/
theorem integral_mixed_descFactorial (lambda : ℝ) (f : Path)
    (I : Finset ℚ) (j : I → ℕ) :
    (∫ m : ℕ → ℕ, ∏ q : I, ((rationalCount m q).descFactorial (j q) : ℝ)
      ∂markLaw lambda f) = ∏ q : I, (retainedArea q lambda f : ℝ) ^ j q := by
  have hm : Measurable (fun m : I → ℕ ↦ ∏ q : I, ((m q).descFactorial (j q) : ℝ)) :=
    measurable_of_countable _
  calc
    _ = ∫ m : I → ℕ, ∏ q : I, ((m q).descFactorial (j q) : ℝ)
        ∂PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q lambda f) := by
      simpa only [Function.comp_def] using
        (markLaw_hasLaw_restrict lambda f I).integral_comp hm.aestronglyMeasurable
    _ = _ := PoissonFactorialMoments.integral_mixed_descFactorial _ j

theorem clippedMarkLaw_hasLaw_restrict (H lambda : ℝ) (f : Path) (I : Finset ℚ) :
    HasLaw (fun m : ℕ → ℕ ↦ fun q : I ↦ rationalCount m q)
      (PoissonCountKernel.finiteCountLaw
        (fun q : I ↦ BrownianWindowExcursionAreas.retainedArea H lambda q f))
      (BrownianClippedExcursionPoissonMarks.markLaw H lambda f) := by
  exact (iIndepFun.precomp Subtype.val_injective
    (BrownianClippedExcursionPoissonMarks.markLaw_rationalCounts_independent H lambda f)).hasLaw_pi
      (fun q : I ↦ BrownianClippedExcursionPoissonMarks.markLaw_hasLaw_rationalCount H lambda f q)

/-- Finite-coordinate consistency is exact after a path-dependent finite
window; it does not assert equality of the entire infinite mark families. -/
theorem ae_all_finite_markLaw_window_stability : ∀ᵐ x ∂rationalLaw,
    ∀ lambda : ℝ, ∀ I : Finset ℚ, ∃ H : ℝ, 0 < H ∧ ∀ L ≥ H,
      (markLaw lambda (measurablePath x)).map
        (fun m : ℕ → ℕ ↦ fun q : I ↦ rationalCount m q) =
      (BrownianClippedExcursionPoissonMarks.markLaw L lambda (measurablePath x)).map
        (fun m : ℕ → ℕ ↦ fun q : I ↦ rationalCount m q) := by
  filter_upwards [ae_all_retainedArea_window_stability] with x hx
  intro lambda I
  have hq : ∀ q : I, ∃ H : ℝ, 0 < H ∧ ∀ L ≥ H,
      retainedArea q lambda (measurablePath x) =
        BrownianWindowExcursionAreas.retainedArea L lambda q (measurablePath x) := by
    intro q
    obtain ⟨H,hH,_,he⟩ := hx lambda q
    exact ⟨H,hH,he⟩
  choose H hH he using hq
  let T : ℝ := 1 + ∑ q : I, H q
  have hT : 0 < T := by
    have hs : 0 ≤ ∑ q : I, H q := Finset.sum_nonneg (fun q _ ↦ (hH q).le)
    dsimp only [T]
    linarith
  refine ⟨T,hT,fun L hL ↦ ?_⟩
  rw [(markLaw_hasLaw_restrict lambda (measurablePath x) I).map_eq,
    (clippedMarkLaw_hasLaw_restrict L lambda (measurablePath x) I).map_eq]
  congr 1
  funext q
  apply he q L
  have hs := Finset.single_le_sum (fun r _ ↦ (hH r).le) (Finset.mem_univ q)
  dsimp only [T] at hL
  linarith

end PerronWright.BrownianFullHorizonMarkMoments
