import PerronWright.Transfer.DeltaDiscGeometry
import PerronWright.Transfer.BanachLocalPowerDerivative

/-!
Combining genuine disc containment in a Cartesian dented domain with
Banach-valued Cauchy estimates.  This is a local derivative theorem for
any actual holomorphic remainder satisfying the stated power bound;
it is not yet the paper's full coefficient transfer lemma.
-/

open Complex Metric
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- A power-bounded holomorphic Banach-valued remainder on a concrete
dented domain has explicit derivatives at unit-disc centers near `1`.
The local Cauchy circle is proved to lie inside the domain. -/
theorem banach_cartesianDelta_iteratedDeriv_bound
    {F : ℂ → E} {z : ℂ} {η m C a : ℝ} (j : ℕ)
    (hm : 0 ≤ m) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hnear : ‖z - 1‖ < η)
    (hF : DifferentiableOn ℂ F (cartesianDelta η m))
    (hbound : ∀ w ∈ cartesianDelta η m,
      ‖F w‖ ≤ C * ‖(1 : ℂ) - w‖ ^ a) :
    ‖iteratedDeriv j F z‖ ≤
      j.factorial *
        (C * (‖(1 : ℂ) - z‖ +
          ‖z - 1‖ / (2 * (m + 3))) ^ a) /
        (‖z - 1‖ / (2 * (m + 3))) ^ j := by
  let r : ℝ := ‖z - 1‖ / (2 * (m + 3))
  have hr : 0 < r := by
    dsimp [r]
    have hn : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    have hd : 0 < 2 * (m + 3) := by linarith
    positivity
  have hsubset : closedBall z r ⊆ cartesianDelta η m :=
    closedBall_subset_cartesianDelta hm hz hz1 hnear
  have hcl : DiffContOnCl ℂ F (ball z r) :=
    hF.diffContOnCl_ball hsubset
  have hboundary : ∀ w ∈ sphere z r,
      ‖F w‖ ≤ C * ‖(1 : ℂ) - w‖ ^ a := by
    intro w hw
    exact hbound w (hsubset (sphere_subset_closedBall hw))
  exact banach_iteratedDeriv_le_local_power j hr hC ha hcl hboundary

end PerronWright.Transfer
