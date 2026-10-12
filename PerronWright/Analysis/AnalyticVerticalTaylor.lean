import PerronWright.Analysis.AnalyticVerticalDivision

open Topology
open scoped BigOperators

noncomputable section

/-!
# Finite Taylor expansion in a distinguished analytic coordinate

This file iterates analytic division by the vertical complex coordinate.  It
produces a finite Taylor expansion whose coefficients remain analytic in the
Banach-space parameter and whose remainder remains jointly analytic.  Unlike a
separate one-variable Taylor expansion on each parameter slice, the
construction retains the joint parameter dependence needed for uniform local
estimates.
-/

namespace PerronWright.AnalyticVerticalTaylor

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A jointly analytic Banach-valued function admits a finite Taylor
expansion in its vertical complex coordinate.  All coefficient functions are
analytic in the horizontal parameter, and the final remainder is still
jointly analytic. -/
theorem analytic_vertical_taylor {f : E × ℂ → F}
    (hf : AnalyticAt ℂ f (0, 0)) (n : ℕ) :
    ∃ (a : ℕ → E → F) (Q : E × ℂ → F),
      (∀ j < n, AnalyticAt ℂ (a j) 0) ∧
      AnalyticAt ℂ Q (0, 0) ∧
      ∀ᶠ x : (E × ℂ) in nhds (0, 0),
        f x =
          (∑ j ∈ Finset.range n, x.2 ^ j • a j x.1) +
            x.2 ^ n • Q x := by
  induction n with
  | zero =>
      let a : ℕ → E → F := fun _ _ ↦ 0
      refine ⟨a, f, ?_, hf, ?_⟩
      · intro j hj
        exact (Nat.not_lt_zero j hj).elim
      · exact Filter.Eventually.of_forall fun x ↦ by simp [a]
  | succ n ih =>
      obtain ⟨a, Q, ha, hQa, hfTaylor⟩ := ih
      obtain ⟨R, hRa, hQdivision⟩ :=
        PerronWright.AnalyticVerticalDivision.analytic_vertical_difference_division hQa
      let c : E → F := fun g ↦ Q (g, 0)
      have hca : AnalyticAt ℂ c 0 := by
        exact hQa.comp_of_eq
          (analyticAt_id.prod analyticAt_const :
            AnalyticAt ℂ (fun g : E ↦ (g, (0 : ℂ))) 0) rfl
      let a' : ℕ → E → F := fun j ↦ if j = n then c else a j
      refine ⟨a', R, ?_, hRa, ?_⟩
      · intro j hj
        by_cases hjn : j = n
        · subst j
          simpa only [a', if_pos] using hca
        · have hjle : j ≤ n := Nat.lt_succ_iff.mp hj
          have hjlt : j < n := Nat.lt_of_le_of_ne hjle hjn
          simpa only [a', if_neg hjn] using ha j hjlt
      · filter_upwards [hfTaylor, hQdivision] with x hfx hQx
        have hQeq : Q x = c x.1 + x.2 • R x := by
          simpa only [c, add_comm] using (sub_eq_iff_eq_add.mp hQx)
        have hsum :
            (∑ j ∈ Finset.range n, x.2 ^ j • a' j x.1) =
              ∑ j ∈ Finset.range n, x.2 ^ j • a j x.1 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjn : j ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hj)
          simp only [a', if_neg hjn]
        rw [hfx, hQeq, Finset.sum_range_succ, hsum]
        simp only [a', if_pos, smul_add, smul_smul, pow_succ, add_assoc]

end PerronWright.AnalyticVerticalTaylor
