import PerronWright.Analysis.RootedTreeClosedDiskJointAtlas

/-!
# Gluing the finite closed-disk rooted-tree atlas

The global domain is the union of the selected half-radius activity balls.
On that domain a chart is chosen pointwise; pairwise compatibility makes the
choice immaterial locally, so the resulting profile is jointly analytic.
-/

open Filter
open scoped Classical Topology

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A finite compatible atlas on a compact subset of the closed unit disk
avoiding `1` glues to one jointly analytic rooted-tree profile on an open
activity neighborhood and one uniform complex-field ball. -/
theorem CompactBJRModel.exists_rootedTreeSeries_joint_analytic_continuation_near_compact_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hKdisk : K ⊆ Metric.closedBall (0 : ℂ) 1)
    (hnotone : (1 : ℂ) ∉ K) :
    ∃ (U : Set ℂ) (ε : ℝ) (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧ K ⊆ U ∧ 0 < ε ∧
      AnalyticOnNhd ℂ Ψ (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      (∀ q ∈ U ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
        TreeCritical.residual M (q, Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 → Ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), Ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ Ψ p.1 = p.2 := by
  obtain ⟨profile, radius, ε, F, hε, hr, -, han, hres, hinside,
    huniq, hcover, hcompat⟩ :=
    M.exists_finite_rootedTreeSeries_closedDisk_joint_atlas
      hM hK hKdisk hnotone
  let U : Set ℂ := ⋃ a ∈ F, Metric.ball (a : ℂ) (radius a / 2)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_biUnion fun a _ => Metric.isOpen_ball
  have hchoose (w : ℂ) (hw : w ∈ U) :
      ∃ a : K, a ∈ F ∧ w ∈ Metric.ball (a : ℂ) (radius a / 2) := by
    simpa only [U, Set.mem_iUnion, exists_prop] using hw
  let pick (w : ℂ) (hw : w ∈ U) : K := Classical.choose (hchoose w hw)
  have hpickF (w : ℂ) (hw : w ∈ U) : pick w hw ∈ F :=
    (Classical.choose_spec (hchoose w hw)).1
  have hpickBall (w : ℂ) (hw : w ∈ U) :
      w ∈ Metric.ball ((pick w hw : K) : ℂ) (radius (pick w hw) / 2) :=
    (Classical.choose_spec (hchoose w hw)).2
  let W : Set (ℂ × C(S, ℂ)) :=
    U ×ˢ Metric.ball (0 : C(S, ℂ)) ε
  let Ψ : ℂ × C(S, ℂ) → C(S, ℂ) := fun q =>
    if hq : q ∈ W then profile (pick q.1 hq.1) q else 0
  have hhalf_full (a : K) :
      Metric.ball (a : ℂ) (radius a / 2) ⊆
        Metric.ball (a : ℂ) (radius a) :=
    Metric.ball_subset_ball (by linarith [hr a])
  have hΨ_eq_chart (a : K) (haF : a ∈ F) (q : ℂ × C(S, ℂ))
      (hqa : q ∈ Metric.ball (a : ℂ) (radius a / 2) ×ˢ
        Metric.ball (0 : C(S, ℂ)) ε) :
      Ψ q = profile a q := by
    have hqU : q.1 ∈ U := by
      dsimp [U]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haF, hqa.1⟩⟩
    have hqW : q ∈ W := ⟨hqU, hqa.2⟩
    rw [show Ψ q = profile (pick q.1 hqU) q by simp [Ψ, hqW]]
    let b : K := pick q.1 hqU
    have hbF : b ∈ F := hpickF q.1 hqU
    have hqb : q.1 ∈ Metric.ball (b : ℂ) (radius b / 2) :=
      hpickBall q.1 hqU
    have hinter : (Metric.ball (b : ℂ) (radius b / 2) ∩
        Metric.ball (a : ℂ) (radius a / 2)).Nonempty :=
      ⟨q.1, hqb, hqa.1⟩
    have heq := hcompat b hbF a haF hinter
    exact heq ⟨⟨hhalf_full b hqb, hqa.2⟩,
      ⟨hhalf_full a hqa.1, hqa.2⟩⟩
  refine ⟨U, ε, Ψ, hUopen, hcover, hε, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, haF, hqa⟩ := hchoose q.1 hq.1
    have hlocalMem : q ∈ Metric.ball (a : ℂ) (radius a / 2) ×ˢ
        Metric.ball (0 : C(S, ℂ)) ε := ⟨hqa, hq.2⟩
    have hlocalNhd :
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε ∈ nhds q :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hlocalMem
    have hlocalEq : Ψ =ᶠ[nhds q] profile a := by
      filter_upwards [hlocalNhd] with y hy
      exact hΨ_eq_chart a haF y hy
    exact (han a haF q ⟨hhalf_full a hqa, hq.2⟩).congr hlocalEq.symm
  · intro q hq
    obtain ⟨a, haF, hqa⟩ := hchoose q.1 hq.1
    rw [hΨ_eq_chart a haF q ⟨hqa, hq.2⟩]
    exact hres a haF q ⟨hhalf_full a hqa, hq.2⟩
  · intro w hw hwI
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
    rw [hΨ_eq_chart a haF (w, 0) ⟨hwa, h0⟩]
    exact hinside a w (hhalf_full a hwa) hwI
  · intro w hw
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
    have hlocalMem : (w, (0 : C(S, ℂ))) ∈
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε := ⟨hwa, h0⟩
    have hlocalNhd :
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε ∈ nhds (w, (0 : C(S, ℂ))) :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hlocalMem
    have hlocalEq : Ψ =ᶠ[nhds (w, (0 : C(S, ℂ)))] profile a := by
      filter_upwards [hlocalNhd] with y hy
      exact hΨ_eq_chart a haF y hy
    have hbase : Ψ (w, 0) = profile a (w, 0) :=
      hΨ_eq_chart a haF (w, 0) hlocalMem
    rw [hbase]
    have hfst : Tendsto
        (fun p : ((ℂ × C(S, ℂ)) × C(S, ℂ)) => p.1)
        (nhds (((w, (0 : C(S, ℂ))), profile a (w, 0))))
        (nhds (w, (0 : C(S, ℂ)))) := continuousAt_fst
    filter_upwards [huniq a haF w (hhalf_full a hwa),
      hfst.eventually hlocalEq] with p hp heq
    rw [heq]
    exact hp

end PerronWright
