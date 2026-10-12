import PerronWright.Probability.FiniteIrreducibleLocalMainTerminal
import PerronWright.Probability.FiniteIrreducibleComponentProcess
import PerronWright.Probability.FactorialWindowMass
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual deterministic floor factorial expectation window integrals

The actual fixed-type graph expectations are measurable step functions.
The proved local-main theorem and continuous literal density bounds give
uniform domination and genuine density integrals, without a moment or
convergence interface assumption.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleWindowExpectation

open FiniteIrreducibleComponentProcess FiniteIrreducibleLocalMainIdentity
open FiniteIrreducibleLocalMainTerminal FactorialDensity
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def localExpectation (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ)
    {q : ℕ} (x : Fin n → S) (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  scaledFactorialExpectation M lambda n x (fun i ↦ CriticalScaling.size (y i) n) r

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem measurable_localExpectation (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (x : Fin n → S) (r : Fin q → ℕ) :
    Measurable (fun y : Fin q → ℝ ↦ localExpectation M lambda n x y r) := by
  let E : (Fin q → ℕ) → ℝ := fun k ↦ scaledFactorialExpectation M lambda n x k r
  have hsize : Measurable (fun y : Fin q → ℝ ↦ fun i ↦ CriticalScaling.size (y i) n) := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun y : Fin q → ℝ ↦ ⌊y i * (n : ℝ)^(2/3 : ℝ)⌋₊)
    have hc : Measurable (fun y : Fin q → ℝ ↦ y i) := measurable_pi_apply i
    exact (hc.mul_const ((n : ℝ)^(2/3 : ℝ))).nat_floor
  exact (measurable_of_countable E).comp hsize

theorem factorial_pointwise_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    (y : Fin q → ℝ) (hya : ∀ i, a ≤ y i) (hyb : ∀ i, y i ≤ b) :
    Tendsto (fun n ↦ localExpectation M lambda n (x n) y r) atTop
      (𝓝 (density (M.alpha hM) (M.beta hM) lambda y r)) := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_uniform_floor_factorial_density_of_assignment
    M hM q R hq lambda a b ha hb x D hD hround hε] with n hn
  rw [Real.dist_eq]
  exact hn y r hya hyb hr

theorem exists_uniform_scaled_bound (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (hq : 0 < q) (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ y ∈ sizeWindow q a b, |localExpectation M lambda n (x n) y r| ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_density_window_bound (b := b) (M.beta_pos hM) ha R
  let B := C^q * Real.exp (-M.beta hM * (a*q)^3/24)
  have hB : 0 < B := mul_pos (pow_pos hC _) (Real.exp_pos _)
  refine ⟨B+1, by linarith, ?_⟩
  filter_upwards [eventually_uniform_floor_factorial_density_of_assignment M hM q R hq
    lambda a b ha (ha.le.trans hab) x D hD hround (by norm_num : (0 : ℝ) < 1)]
    with n hn r hr y hy
  have hya := fun i ↦ (mem_sizeWindow.mp hy i).1
  have hyb := fun i ↦ (mem_sizeWindow.mp hy i).2
  have he := hn y r hya hyb hr
  change |localExpectation M lambda n (x n) y r-density (M.alpha hM) (M.beta hM) lambda y r| < 1 at he
  have hd := density_pos (M.alpha hM) lambda (M.beta_pos hM) y r (fun i ↦ ha.trans_le (hya i))
  have hbnd := hbound q (M.alpha hM) lambda y r (mem_sizeWindow.mp hy) hr
  change density (M.alpha hM) (M.beta hM) lambda y r ≤ B at hbnd
  have h := abs_add_le
    (localExpectation M lambda n (x n) y r-density (M.alpha hM) (M.beta hM) lambda y r)
    (density (M.alpha hM) (M.beta hM) lambda y r)
  rw [sub_add_cancel, abs_of_pos hd] at h
  exact h.trans (by linarith)

theorem eventually_integrableOn_localExpectation (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    ∀ᶠ n in atTop, IntegrableOn (fun y ↦ localExpectation M lambda n (x n) y r)
      (sizeWindow q a b) volume := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B, _, hbound⟩ := exists_uniform_scaled_bound M hM hq R lambda a b ha hab x D hD hround
  let : IsFiniteMeasure (volume.restrict (sizeWindow q a b)) :=
    isFiniteMeasure_restrict.mpr (by
      change volume (Set.Icc (fun _ : Fin q ↦ a) (fun _ ↦ b)) ≠ ⊤
      exact isCompact_Icc.measure_lt_top.ne)
  filter_upwards [hbound] with n hn
  apply (integrable_const B).mono' (measurable_localExpectation M lambda n (x n) r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  simpa only [Real.norm_eq_abs] using hn r hr y hy

theorem localExpectation_window_integral_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ ∫ y in sizeWindow q a b, localExpectation M lambda n (x n) y r)
      atTop (𝓝 (fixedSurplusWindowMass (M.alpha hM) (M.beta hM) lambda a b r)) := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨B, _, hbound⟩ := exists_uniform_scaled_bound M hM hq R lambda a b ha hab x D hD hround
  let : IsFiniteMeasure (volume.restrict (sizeWindow q a b)) :=
    isFiniteMeasure_restrict.mpr (by
      change volume (Set.Icc (fun _ : Fin q ↦ a) (fun _ ↦ b)) ≠ ⊤
      exact isCompact_Icc.measure_lt_top.ne)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
  · exact Eventually.of_forall (fun n ↦ (measurable_localExpectation M lambda n (x n) r).aestronglyMeasurable)
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    simpa only [Real.norm_eq_abs] using hn r hr y hy
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact factorial_pointwise_tendsto M hM hq r lambda a b ha (ha.le.trans hab) x D hD hround y
      (fun i ↦ (mem_sizeWindow.mp hy i).1) (fun i ↦ (mem_sizeWindow.mp hy i).2)

end PerronWright.FiniteIrreducibleWindowExpectation
