import PerronWright.CycleAnalytic

open MeasureTheory
open scoped Topology
noncomputable section

namespace PerronWright.KernelCycle

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The genuine simple-cycle term.  Its cycle length is `n + 3`, so the
spurious length-two term present in the regularized-determinant expansion is
not included. -/
def simpleUnicyclicTermC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) (n : ℕ) : ℂ :=
  unicyclicTermC mu a w (n + 1)

/-- The direct simple-cycle series, beginning with triangles. -/
def simpleUnicyclicSeriesC (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) : ℂ :=
  ∑' n : ℕ, simpleUnicyclicTermC mu a w n

theorem summable_simpleUnicyclicTermC
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    Summable (simpleUnicyclicTermC mu a w) := by
  exact (summable_unicyclicTermC mu a r hr hsubcritical w hw).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)

omit [BorelSpace S] in
@[simp] theorem unicyclicTermC_zero
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (w : ℂ) :
    unicyclicTermC mu a w 0 =
      w ^ 2 * (cycleTrace mu a 1 : ℂ) / 4 := by
  simp [unicyclicTermC]
  ring

/-- The old series beginning at operator power two is exactly the genuine
simple-cycle series plus its explicit quadratic trace term. -/
theorem unicyclicSeriesC_eq_quadratic_add_simple
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    unicyclicSeriesC mu a w =
      w ^ 2 * (cycleTrace mu a 1 : ℂ) / 4 +
        simpleUnicyclicSeriesC mu a w := by
  let f : ℕ → ℂ := unicyclicTermC mu a w
  have hf : Summable f :=
    summable_unicyclicTermC mu a r hr hsubcritical w hw
  calc
    unicyclicSeriesC mu a w = ∑' n : ℕ, f n := rfl
    _ = ∑ i ∈ Finset.range 1, f i + ∑' i : ℕ, f (i + 1) :=
      (hf.sum_add_tsum_nat_add 1).symm
    _ = f 0 + ∑' i : ℕ, f (i + 1) := by simp
    _ = w ^ 2 * (cycleTrace mu a 1 : ℂ) / 4 +
        simpleUnicyclicSeriesC mu a w := by
      rw [show f 0 = w ^ 2 * (cycleTrace mu a 1 : ℂ) / 4 by
        exact unicyclicTermC_zero mu a w]
      congr 1

/-- Equivalently, the genuine simple-cycle series is obtained by the exact
`- Tr(L^2)/4` correction appearing in the paper. -/
theorem simpleUnicyclicSeriesC_eq_sub_quadratic
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 ≤ r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    simpleUnicyclicSeriesC mu a w =
      unicyclicSeriesC mu a w -
        w ^ 2 * (cycleTrace mu a 1 : ℂ) / 4 := by
  rw [unicyclicSeriesC_eq_quadratic_add_simple
    mu a r hr hsubcritical w hw]
  ring

/-- The genuine simple-cycle series is analytic throughout every strictly
subcritical disc.  Analyticity is inherited from the direct trace series
after the explicit quadratic correction. -/
theorem analyticAt_simpleUnicyclicSeriesC_of_subcritical_radius
    (mu : Measure S) [IsFiniteMeasure mu]
    (a : C(S × S, ℝ)) (r : ℝ) (hr : 0 < r)
    (hsubcritical : r * mu.real Set.univ * ‖a‖ < 1)
    {w : ℂ} (hw : ‖w‖ < r) :
    AnalyticAt ℂ (simpleUnicyclicSeriesC mu a) w := by
  have hseries : AnalyticAt ℂ (unicyclicSeriesC mu a) w :=
    analyticAt_unicyclicSeriesC_of_subcritical_radius
      mu a r hr hsubcritical hw
  have hquad : AnalyticAt ℂ
      (fun z : ℂ => z ^ 2 * (cycleTrace mu a 1 : ℂ) / 4) w :=
    (((analyticAt_id.pow 2).mul analyticAt_const).div_const)
  apply (hseries.sub hquad).congr
  let eps : ℝ := (r - ‖w‖) / 2
  have heps : 0 < eps := by dsimp [eps]; linarith
  apply Filter.eventually_of_mem (Metric.ball_mem_nhds w heps)
  intro z hz
  have hznorm : ‖z‖ ≤ r := by
    have hdist : dist z w < eps := Metric.mem_ball.mp hz
    apply le_of_lt
    calc
      ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ = dist z w + ‖w‖ := by rw [dist_eq_norm]
      _ < eps + ‖w‖ := by linarith
      _ ≤ r := by dsimp [eps]; linarith
  exact (simpleUnicyclicSeriesC_eq_sub_quadratic
    mu a r hr.le hsubcritical z hznorm).symm

end PerronWright.KernelCycle
