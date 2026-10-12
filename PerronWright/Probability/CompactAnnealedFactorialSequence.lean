import PerronWright.Probability.CompactAnnealedFactorialLocal

/-! # Sequential local factorial asymptotics without sampling interfaces

Literal floor positivity, connected normalizers and placements are proved
eventually from the fixed positive size window. A finite shift removes
them entirely from the final graph-expectation theorem.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactAnnealedFactorialSequence

open CompactAnnealedFactorialLocal AnnealedTupleResidualCounting

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Only the actual model, positive size window and convergence of its
coordinates are assumed. Sampling normalizers are proved, not premises. -/
theorem factorial_sequence_tendsto_positive_sizes (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → Fin q → ℝ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ localExpectation M lambda (N m) (x m) r) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  let R := Finset.univ.sup r
  have hr (i : Fin q) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  have hx (m) (i) : 0 ≤ x m i := ha.le.trans (hxa m i)
  have hgood : ∀ᶠ m in atTop,
      (∀ i, 0 < CriticalScaling.size (x m i) (N m)) ∧
      (∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N m)))
        (CriticalScaling.size (x m i) (N m)) (r i)) ∧
      Nonempty (Placements (N m) (fun i ↦ CriticalScaling.size (x m i) (N m))) := by
    filter_upwards [CriticalSizeTuple.eventually_size_pos_on_window N hNt a ha,
      CriticalConnectedSampling.eventually_normalizers_pos_on_window M hM R N hNt a ha,
      CriticalSizeTuple.eventually_floor_placements N hN hNt x b hb hx hxb] with m hk hC hf
    exact ⟨fun i ↦ hk _ (hxa m i), fun i ↦ hC _ (hxa m i) _ (hr i) _, hf⟩
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp hgood
  let N' m := N (m+m₀)
  let x' m := x (m+m₀)
  have hk (m) (i) : 0 < CriticalScaling.size (x' m i) (N' m) :=
    (hm₀ (m+m₀) (by omega)).1 i
  have hC (m) (i) : 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N' m)))
      (CriticalScaling.size (x' m i) (N' m)) (r i) :=
    (hm₀ (m+m₀) (by omega)).2.1 i
  let f (m) : Placements (N' m) (fun i ↦ CriticalScaling.size (x' m i) (N' m)) :=
    Classical.choice ((hm₀ (m+m₀) (by omega)).2.2)
  have ht := ready_sequence_tendsto M hM hQP hq r R hr N'
    (fun m ↦ hN (m+m₀)) (hNt.comp (tendsto_add_atTop_nat m₀))
    x' lambda a b ha hb (fun m i ↦ hxa (m+m₀) i) (fun m i ↦ hxb (m+m₀) i)
    s hs (fun i ↦ (hxs i).comp (tendsto_add_atTop_nat m₀)) hk f hC
  exact (tendsto_add_atTop_iff_nat m₀).mp ht

/-- The literal graph-size sequence, including its harmless initial
zero/very small sizes. This is a pointwise sequential local factorial
limit, not yet the uniform-window or Aldous process theorem. -/
theorem factorial_sequence_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (x : ℕ → Fin q → ℝ) (lambda a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hxa : ∀ m i, a ≤ x m i) (hxb : ∀ m i, x m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hxs : ∀ i, Tendsto (fun m ↦ x m i) atTop (𝓝 (s i))) :
    Tendsto (fun n ↦ localExpectation M lambda n (x n) r) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  have ht := factorial_sequence_tendsto_positive_sizes M hM hQP hq r
    (fun n ↦ n+1) (fun _ ↦ by omega) (tendsto_add_atTop_nat 1)
    (fun n ↦ x (n+1)) lambda a b ha hb
    (fun n i ↦ hxa (n+1) i) (fun n i ↦ hxb (n+1) i)
    s hs (fun i ↦ (hxs i).comp (tendsto_add_atTop_nat 1))
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem factorial_pointwise_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (r : Fin q → ℕ) (x : Fin q → ℝ) (lambda a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hxa : ∀ i, a ≤ x i) (hxb : ∀ i, x i ≤ b) :
    Tendsto (fun n ↦ localExpectation M lambda n x r) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda x r)) :=
  factorial_sequence_tendsto M hM hQP hq r (fun _ ↦ x) lambda a b ha hb
    (fun _ ↦ hxa) (fun _ ↦ hxb) x (fun i ↦ ha.trans_le (hxa i))
    (fun _ ↦ tendsto_const_nhds)

end PerronWright.CompactAnnealedFactorialSequence
