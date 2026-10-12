import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Vanishing of Taylor coefficients from local order bounds

This is a small one-variable analytic interface used to turn a proved
`O(‖z‖^N)` remainder into equality of all Taylor coefficients below `N`.
-/

open scoped Topology
open Asymptotics

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem HasFPowerSeriesAt.coeff_eq_zero_of_isBigO_norm_pow
    {f : ℂ → F} {p : FormalMultilinearSeries ℂ ℂ F} {N : ℕ}
    (hp : HasFPowerSeriesAt f p 0)
    (hO : f =O[𝓝 (0 : ℂ)] (fun z : ℂ => ‖z‖ ^ N))
    {k : ℕ} (hk : k < N) :
    p.coeff k = 0 := by
  have hall : ∀ j < N, p.coeff j = 0 := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | h j ih =>
      have hmapzero : ∀ i < j, p i = 0 := by
        intro i hi
        apply ContinuousMultilinearMap.ext
        intro x
        change p i x = 0
        simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
          ih i hi (hi.trans hj), smul_zero]
      have hpartial (z : ℂ) :
          p.partialSum (j + 1) z = p j (fun _ => z) := by
        change (∑ i ∈ Finset.range (j + 1), p i (fun _ : Fin i => z)) = _
        apply Finset.sum_eq_single j
        · intro i hi' hne
          have hi : i < j := (Finset.mem_range_succ_iff.mp hi').lt_of_ne hne
          simp only [hmapzero i hi, zero_apply]
        · exact fun hnot => False.elim
            (hnot (Finset.mem_range.mpr (Nat.lt_add_one j)))
      have hJN : j + 1 ≤ N := Nat.succ_le_iff.mpr hj
      have hpow :
          (fun z : ℂ => ‖z‖ ^ N) =O[𝓝 (0 : ℂ)]
            (fun z : ℂ => ‖z‖ ^ (j + 1)) := by
        rcases hJN.eq_or_lt with heq | hlt
        · rw [heq]
        · simpa only [sub_zero] using
            (isLittleO_pow_sub_pow_sub (0 : ℂ) hlt).isBigO
      have hfsmall := hO.trans hpow
      have hrem := hp.isBigO_sub_partialSum_pow (j + 1)
      have hhom :
          (fun z : ℂ => p j (fun _ => z)) =O[𝓝 (0 : ℂ)]
            (fun z : ℂ => ‖z‖ ^ (j + 1)) := by
        have hsub := hfsmall.sub hrem
        refine hsub.congr_left ?_
        intro z
        rw [zero_add, hpartial]
        abel
      have hz := hhom.continuousMultilinearMap_apply_eq_zero (1 : ℂ)
      change p j (fun _ => (1 : ℂ)) = 0
      exact hz
  exact hall k hk
