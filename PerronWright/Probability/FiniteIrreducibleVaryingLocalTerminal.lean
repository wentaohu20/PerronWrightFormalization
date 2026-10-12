import PerronWright.Probability.FiniteIrreducibleVaryingMarkedLocalMain

/-! # Literal raw-time varying-parameter local factorial terminals

Every source below is the genuine fixed-assignment graph law, at the paper
time 1 + ell(n) n^(-1/3). Positivity is proved eventually. Counts may be
any O(1) realization of the finite reference weights. Coupled continuous
mark tests converge to their deterministic normalized Perron evaluation.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleVaryingLocalTerminal

open FiniteIrreducibleVaryingMarkedLocalMain FiniteIrreducibleMarkedLocalMain
open FiniteIrreducibleVaryingCriticalTime FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleNativeMarkConcentration (perronMarks)
open FiniteIrreducibleFactorialDensityFloor (density_tendsto_positive)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open AnnealedMarkedFactorialCounting (markedCount markedCount_one)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Full-window coupled marked local-main at the literal raw time and floors.
The sole spectral condition is finite irreducible criticality, permitting -1. -/
theorem eventually_uniform_paper_floor_marked_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ ht : 0 ≤ 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)),
      ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |(n : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, markedCount x G (fun i ↦ ⌊y i * (n : ℝ) ^ (2 / 3 : ℝ)⌋₊) r Ψ
            ∂FiniteIrreducibleTypedGraphLaw.law M
              (1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ))) ht x) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r *
          Ψ (perronMarks M hM q)| < ε := by
  filter_upwards [FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
      M hM q R hq ell lambda a b hl ha hb c D hD hround Ψ hΨ hε,
    eventually_time_eq_raw ell lambda hl,
    (FiniteIrreducibleVaryingCriticalTime.rawTime_tendsto ell lambda hl).eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn ht hp
  refine ⟨hp, ?_⟩
  intro htime x hc y r hya hyb hr
  have h := hn x hc y r hya hyb hr
  simpa only [scaledMarkedFactorialExpectation, CriticalScaling.size, ht, rawTime] using h

/-- Unmarked local-main is an actual graph count consequence, by the
constant coupled test, not a separate asymptotic interface. -/
theorem eventually_uniform_paper_floor_factorial_density
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
      ∀ ht : 0 ≤ 1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ)),
      ∀ x : Fin n → S, (∀ s, fiberCount x s = c n s) →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |(n : ℝ) ^ (2 * (q : ℝ) / 3) *
          (∫ G, (ComponentCounts.count G (fun i ↦ ⌊y i * (n : ℝ) ^ (2 / 3 : ℝ)⌋₊) r : ℝ)
            ∂FiniteIrreducibleTypedGraphLaw.law M
              (1 + ell n * (n : ℝ) ^ (-(1 / 3 : ℝ))) ht x) -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r| < ε := by
  filter_upwards [eventually_uniform_paper_floor_marked_factorial_density
    M hM q R hq ell lambda a b hl ha hb c D hD hround (fun _ ↦ 1) continuous_const hε]
    with n hn
  refine ⟨hn.1, ?_⟩
  intro ht x hc y r hya hyb hr
  simpa only [markedCount_one, mul_one] using hn.2 ht x hc y r hya hyb hr

/-- No prescribed rounding scheme is required: the observed fibre counts
of any actual assignment sequence give the same varying-time conclusion. -/
theorem eventually_uniform_floor_marked_density_of_assignment
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |scaledMarkedFactorialExpectation M (ell n) n (x n)
          (fun i ↦ CriticalScaling.size (y i) n) r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r *
          Ψ (perronMarks M hM q)| < ε := by
  filter_upwards [FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
    M hM q R hq ell lambda a b hl ha hb (fun n ↦ fiberCount (x n)) D hD hround Ψ hΨ hε]
    with n hn
  exact hn (x n) (fun _ ↦ rfl)

/-- Along every diverging size subsequence, actual varying integer tuples
and coupled marks have the literal density at the limiting parameter. -/
theorem tendsto_marked_factorial_density_of_counts
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (x : (m : ℕ) → Fin (N m) → S)
    (hc : ∀ m s, fiberCount (x m) s = c (N m) s)
    (k : ℕ → Fin q → ℕ) (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hka : ∀ᶠ m in atTop, ∀ i, a ≤ normalizedSize (N m) (k m i))
    (hkb : ∀ᶠ m in atTop, ∀ i, normalizedSize (N m) (k m i) ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hks : ∀ i, Tendsto (fun m ↦ normalizedSize (N m) (k m i)) atTop (𝓝 (s i)))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun m ↦ scaledMarkedFactorialExpectation M (ell (N m)) (N m) (x m) (k m) r Ψ)
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r *
        Ψ (perronMarks M hM q))) := by
  have hd := (density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r
    (fun m i ↦ normalizedSize (N m) (k m i)) s hs hks).mul_const (Ψ (perronMarks M hM q))
  have he : Tendsto (fun m ↦
      scaledMarkedFactorialExpectation M (ell (N m)) (N m) (x m) (k m) r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize (N m) (k m i)) r * Ψ (perronMarks M hM q))
      atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (eventually_uniform_marked_factorial_density_limit_parameter
      M hM q R hq ell lambda a b hl ha hb c D hD hround Ψ hΨ hε), hka, hkb]
      with m hm hma hmb
    rw [Real.dist_eq, sub_zero]
    exact hm (x m) (hc m) (k m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

/-- Genuine varying-time floor local-main along arbitrary diverging ambient
sizes and varying positive target coordinates, with the actual coupled marks. -/
theorem tendsto_floor_marked_factorial_density_of_counts
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {q : ℕ} (R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    (c : ℕ → S → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(c n s : ℝ) - (n : ℝ) * M.weight s| ≤ D)
    (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (x : (m : ℕ) → Fin (N m) → S)
    (hc : ∀ m s, fiberCount (x m) s = c (N m) s)
    (y : ℕ → Fin q → ℝ) (r : Fin q → ℕ) (hr : ∀ i, r i ≤ R)
    (hya : ∀ᶠ m in atTop, ∀ i, a ≤ y m i)
    (hyb : ∀ᶠ m in atTop, ∀ i, y m i ≤ b)
    (s : Fin q → ℝ) (hs : ∀ i, 0 < s i)
    (hys : ∀ i, Tendsto (fun m ↦ y m i) atTop (𝓝 (s i)))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun m ↦ scaledMarkedFactorialExpectation M (ell (N m)) (N m) (x m)
      (fun i ↦ CriticalScaling.size (y m i) (N m)) r Ψ)
      atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda s r *
        Ψ (perronMarks M hM q))) := by
  have hd := (density_tendsto_positive (M.alpha hM) (M.beta hM) lambda r y s hs hys).mul_const
    (Ψ (perronMarks M hM q))
  have he : Tendsto (fun m ↦
      scaledMarkedFactorialExpectation M (ell (N m)) (N m) (x m)
        (fun i ↦ CriticalScaling.size (y m i) (N m)) r Ψ -
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda (y m) r *
          Ψ (perronMarks M hM q)) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hNt.eventually (FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
      M hM q R hq ell lambda a b hl ha hb c D hD hround Ψ hΨ hε), hya, hyb]
      with m hm hma hmb
    rw [Real.dist_eq, sub_zero]
    exact hm (x m) (hc m) (y m) r hma hmb hr
  simpa only [sub_add_cancel, zero_add] using he.add hd

end PerronWright.FiniteIrreducibleVaryingLocalTerminal
