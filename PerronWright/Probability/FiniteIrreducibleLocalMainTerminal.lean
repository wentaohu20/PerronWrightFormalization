import PerronWright.Probability.FiniteIrreducibleLocalMainUniform

/-! # Literal deterministic finite Chapter 3 local-main terminal

The actual factorial count is that of ordered distinct genuine connected
components, not a graph-pattern surrogate. The graph law holds types
fixed and has edge probability 1-exp(-t κ/n). Every bounded O(1) count
realization is permitted. The paper's raw time and literal integer floors
are displayed below; positivity of raw time is proved at the common tail.
The parameters are the genuine normalized finite Perron α and β.

This terminal does not assert the point-process or Brownian-law theorem.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleLocalMainTerminal

open FiniteIrreducibleLocalMainIdentity FiniteIrreducibleLocalMainUniform
open FiniteIrreducibleCriticalPrefactorScaling FiniteIrreducibleFactorialDensityFloor
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Literal raw-time/floor local-main density theorem. The threshold is
uniform in actual assignments realizing the counts, target size vectors
in the whole window, and every surplus vector bounded by R. -/
theorem eventually_uniform_paper_floor_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + lambda * (n : ℝ)^(-(1/3 : ℝ)) ∧
      ∀ ht : 0 ≤ 1 + lambda * (n : ℝ)^(-(1/3 : ℝ)),
      ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |(n : ℝ)^(2*(q : ℝ)/3) *
          (∫ G, (ComponentCounts.count G
            (fun i ↦ ⌊y i * (n : ℝ)^(2/3 : ℝ)⌋₊) r : ℝ)
            ∂FiniteIrreducibleTypedGraphLaw.law M
              (1 + lambda * (n : ℝ)^(-(1/3 : ℝ))) ht x) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  filter_upwards [eventually_uniform_floor_factorial_expectation_density
      M hM q R hq lambda a b ha hb c D hD hround hε,
    CriticalScaling.time_eq_raw_eventually lambda,
    (CriticalScaling.raw_time_tendsto lambda).eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn ht hp
  refine ⟨hp, ?_⟩
  intro htime x hc y r hya hyb hr
  have h := hn x hc y r hya hyb hr
  simpa only [scaledFactorialExpectation, CriticalScaling.size, ht] using h

/-- No prescribed count scheme is needed: every actual deterministic
assignment sequence with bounded literal fibre-count errors has the
uniform paper local-main conclusion. -/
theorem eventually_uniform_floor_factorial_density_of_assignment
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |(n : ℝ)^(2*(q : ℝ)/3) *
          (∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) n) r : ℝ)
            ∂FiniteIrreducibleTypedGraphLaw.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) (x n)) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  filter_upwards [eventually_uniform_floor_factorial_expectation_density
    M hM q R hq lambda a b ha hb (fun n ↦ fiberCount (x n)) D hD hround hε] with n hn
  exact hn (x n) (fun _ ↦ rfl)

/-- Directed literal integer-window local-main along every diverging
ambient-size sequence, with arbitrary varying actual integer sizes. -/
theorem tendsto_factorial_density_of_counts
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (x : (m : ℕ) → Fin (N m) → S)
    (hc : ∀ m s, fiberCount (x m) s = c (N m) s)
    (k : ℕ → Fin q → ℕ) (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hka : ∀ᶠ m in atTop, ∀ i, a ≤ normalizedSize (N m) (k m i))
    (hkb : ∀ᶠ m in atTop, ∀ i, normalizedSize (N m) (k m i) ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hks : ∀ i, Tendsto (fun m ↦ normalizedSize (N m) (k m i)) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ scaledFactorialExpectation M lambda (N m) (x m) (k m) r)
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  have hd := density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r
    (fun m i ↦ normalizedSize (N m) (k m i)) s hs hks
  have he : Tendsto (fun m ↦ scaledFactorialExpectation M lambda (N m) (x m) (k m) r -
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
        (fun i ↦ normalizedSize (N m) (k m i)) r) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (eventually_uniform_factorial_expectation_density
      M hM q R hq lambda a b ha hb c D hD hround hε), hka, hkb] with m hm hma hmb
    rw [Real.dist_eq, sub_zero]
    exact hm (x m) (hc m) (k m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

/-- Genuine floor local-main for varying target coordinates and arbitrary
diverging ambient sizes under the deterministic graph probability law. -/
theorem tendsto_floor_factorial_density_of_counts
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ) (hq : 0 < q)
    (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (x : (m : ℕ) → Fin (N m) → S)
    (hc : ∀ m s, fiberCount (x m) s = c (N m) s)
    (y : ℕ → Fin q → ℝ) (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hya : ∀ᶠ m in atTop, ∀ i, a ≤ y m i)
    (hyb : ∀ᶠ m in atTop, ∀ i, y m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hys : ∀ i, Tendsto (fun m ↦ y m i) atTop (𝓝 (s i))) :
    Tendsto (fun m ↦ scaledFactorialExpectation M lambda (N m) (x m)
      (fun i ↦ CriticalScaling.size (y m i) (N m)) r)
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r)) := by
  have hd := density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r y s hs hys
  have he : Tendsto (fun m ↦ scaledFactorialExpectation M lambda (N m) (x m)
      (fun i ↦ CriticalScaling.size (y m i) (N m)) r -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (y m) r) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (eventually_uniform_floor_factorial_expectation_density
      M hM q R hq lambda a b ha hb c D hD hround hε), hya, hyb] with m hm hma hmb
    rw [Real.dist_eq, sub_zero]
    exact hm (x m) (hc m) (y m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

end PerronWright.FiniteIrreducibleLocalMainTerminal
