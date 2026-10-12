import PerronWright.Enumeration.UnicyclicTailOrder

/-!
# Analyticity of the full profile simple-cycle series at the origin

Normal convergence of the genuine cycle terms turns the existing termwise
derivative theorem into analyticity of the complete infinite sum.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright
namespace JointSimpleCycleEGF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem profileSimpleCycleSeries_analyticAt_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    AnalyticAt ℂ (fun w => profileSimpleCycleSeries M (tau w)) 0 := by
  have htau0 : tau 0 = 0 := by
    have h := hp.coeff_zero (1 : Fin 0 → ℂ)
    have h' : p.coeff 0 = tau 0 := by
      simpa only [FormalMultilinearSeries.coeff] using h
    exact h'.symm.trans hp0
  have htauBall : Metric.ball (0 : C(S, ℂ)) (1 / 2) ∈ 𝓝 (tau 0) := by
    rw [htau0]
    exact Metric.ball_mem_nhds _ (by norm_num)
  have htauEv : ∀ᶠ z in 𝓝 (0 : ℂ), ‖tau z‖ < 1 / 2 := by
    have h := hp.continuousAt htauBall
    filter_upwards [h] with z hz
    change tau z ∈ Metric.ball (0 : C(S, ℂ)) (1 / 2) at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  let c : ℝ := ‖deriv tau 0‖ + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hderBall : Metric.ball (deriv tau 0) 1 ∈ 𝓝 (deriv tau 0) :=
    Metric.ball_mem_nhds _ zero_lt_one
  have hderEvRaw : ∀ᶠ z in 𝓝 (0 : ℂ),
      deriv tau z ∈ Metric.ball (deriv tau 0) 1 :=
    hp.analyticAt.deriv.continuousAt hderBall
  have hderEv : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv tau z‖ ≤ c := by
    filter_upwards [hderEvRaw] with z hz
    have hz' : ‖deriv tau z - deriv tau 0‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖deriv tau z‖ =
          ‖(deriv tau z - deriv tau 0) + deriv tau 0‖ := by ring_nf
      _ ≤ ‖deriv tau z - deriv tau 0‖ + ‖deriv tau 0‖ := norm_add_le _ _
      _ ≤ c := by dsimp [c]; linarith
  have hanaEv : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ tau z :=
    hp.analyticAt.eventually_analyticAt
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖tau z‖ < 1 / 2 ∧ ‖deriv tau z‖ ≤ c ∧ AnalyticAt ℂ tau z := by
    filter_upwards [htauEv, hderEv, hanaEv] with z hz hdz haz
    exact ⟨hz, hdz, haz⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  let s : Set ℂ := Metric.ball 0 ε
  have hdata : ∀ z, z ∈ s →
      ‖tau z‖ < 1 / 2 ∧ ‖deriv tau z‖ ≤ c ∧ AnalyticAt ℂ tau z := by
    intro z hz
    exact hball (by simpa only [s, Metric.mem_ball, dist_zero_right] using hz)
  have hdiff : DifferentiableOn ℂ
      (fun w => profileSimpleCycleSeries M (tau w)) s := by
    intro z hz
    have hder := profileSimpleCycleSeries_hasDerivAt_of_uniform_subcritical
      M hM Metric.isOpen_ball (convex_ball (0 : ℂ) ε).isPreconnected
      tau (deriv tau) (1 / 2) c (by norm_num) (by norm_num) hc
      (fun y hy => (hdata y hy).2.2.differentiableAt.hasDerivAt)
      (fun y hy x => (tau y).norm_coe_le_norm x |>.trans (hdata y hy).1.le)
      (fun y hy => (hdata y hy).2.1)
      (Metric.mem_ball_self hε) hz
    exact hder.differentiableAt.differentiableWithinAt
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) 0 (Metric.mem_ball_self hε)

end JointSimpleCycleEGF
end PerronWright
