import PerronWright.Probability.FiniteIrreducibleMarkedLocalMain
import PerronWright.Probability.FiniteIrreducibleComponentProcess
import PerronWright.Probability.CriticalFloorCells
import PerronWright.Probability.FactorialWindowMass
import Mathlib.MeasureTheory.Function.Floor

/-! # Exact floor-cell integrals of actual deterministic marked expectations -/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleMarkedWindowGrid

open FiniteIrreducibleMarkedLocalMain FiniteIrreducibleNativeMarkConcentration
  FiniteIrreducibleComponentProcess AnnealedMarkedFactorialCounting
  CriticalFloorCells FactorialDensity
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def localMarkedExpectation (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ)
    {q : ℕ} (x0 : Fin n → S) (y : Fin q → ℝ) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  scaledMarkedFactorialExpectation M lambda n x0 (fun i ↦ CriticalScaling.size (y i) n) r Ψ

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem measurable_localMarkedExpectation (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (x0 : Fin n → S) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    Measurable (fun y : Fin q → ℝ ↦ localMarkedExpectation M lambda n x0 y r Ψ) := by
  let E : (Fin q → ℕ) → ℝ := fun k ↦ scaledMarkedFactorialExpectation M lambda n x0 k r Ψ
  have hs : Measurable (fun y : Fin q → ℝ ↦ fun i ↦ CriticalScaling.size (y i) n) := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun y : Fin q → ℝ ↦ ⌊y i * (n : ℝ)^(2/3 : ℝ)⌋₊)
    have hc : Measurable (fun y : Fin q → ℝ ↦ y i) := measurable_pi_apply i
    exact (hc.mul_const ((n : ℝ)^(2/3 : ℝ))).nat_floor
  exact (measurable_of_countable E).comp hs

theorem marked_pointwise_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q : ℕ} (hq : 0 < q) (r : Fin q → ℕ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (y : Fin q → ℝ) (hya : ∀ i, a ≤ y i) (hyb : ∀ i, y i ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun n ↦ localMarkedExpectation M lambda n (x n) y r Ψ) atTop
      (𝓝 (density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q))) := by
  let R := Finset.univ.sup r
  have hr (i) : r i ≤ R := Finset.le_sup (Finset.mem_univ i)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_uniform_floor_marked_factorial_density M hM q R hq
    lambda a b ha hb (fun n s ↦ fiberCount (x n) s) D hD hround Ψ hΨ hε] with n hn
  rw [Real.dist_eq]
  exact hn (x n) (fun _ ↦ rfl) y r hya hyb hr

theorem exists_uniform_scaled_marked_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {q : ℕ} (hq : 0 < q) (R : ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ y ∈ sizeWindow q a b, |localMarkedExpectation M lambda n (x n) y r Ψ| ≤ B := by
  obtain ⟨C,hC,hbound⟩ := exists_density_window_bound (b := b) (M.beta_pos hM) ha R
  let B₀ := C^q * Real.exp (-M.beta hM*(a*q)^3/24)
  refine ⟨1+B₀*|Ψ (perronMarks M hM q)|, by dsimp only [B₀]; positivity, ?_⟩
  filter_upwards [eventually_uniform_floor_marked_factorial_density M hM q R hq
    lambda a b ha (ha.le.trans hab) (fun n s ↦ fiberCount (x n) s) D hD hround
    Ψ hΨ (by norm_num : (0 : ℝ) < 1)] with n hn r hr y hy
  have hxi := mem_sizeWindow.mp hy
  have he := hn (x n) (fun _ ↦ rfl) y r (fun i ↦ (hxi i).1) (fun i ↦ (hxi i).2) hr
  have hd := hbound q (M.alpha hM) lambda y r hxi hr
  have hp := density_pos (M.alpha hM) lambda (M.beta_pos hM) y r (fun i ↦ ha.trans_le (hxi i).1)
  calc
    |localMarkedExpectation M lambda n (x n) y r Ψ| =
      |(localMarkedExpectation M lambda n (x n) y r Ψ -
        density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)) +
        density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)| := by congr 1; ring
    _ ≤ |localMarkedExpectation M lambda n (x n) y r Ψ -
        density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)| +
        |density (M.alpha hM) (M.beta hM) lambda y r * Ψ (perronMarks M hM q)| := abs_add_le _ _
    _ ≤ 1+B₀*|Ψ (perronMarks M hM q)| := by
      rw [abs_mul,abs_of_pos hp]
      exact add_le_add he.le (mul_le_mul_of_nonneg_right hd (abs_nonneg _))

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem localMarkedExpectation_eq_on_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ)
    {y : Fin q → ℝ} (hy : y ∈ cell ((n : ℝ)^(2/3 : ℝ)) k) :
    localMarkedExpectation M lambda n x0 y r Ψ = (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ G, markedCount x0 G k r Ψ ∂graphLaw M lambda n x0 := by
  have he := floor_eq_on_cell (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) k hy
  simp only [localMarkedExpectation,scaledMarkedFactorialExpectation,CriticalScaling.size,he,graphLaw]

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem integrableOn_localMarkedExpectation_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    IntegrableOn (fun y ↦ localMarkedExpectation M lambda n x0 y r Ψ)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  let : IsFiniteMeasure (volume.restrict (cell ((n : ℝ)^(2/3 : ℝ)) k)) :=
    isFiniteMeasure_restrict_cell _ k
  apply (integrable_const ((n : ℝ)^(2*(q : ℝ)/3) *
    ∫ G, markedCount x0 G k r Ψ ∂graphLaw M lambda n x0)).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with y hy
  exact (localMarkedExpectation_eq_on_cell M lambda hn x0 k r Ψ hy).symm

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem integral_localMarkedExpectation_cell (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ y in cell ((n : ℝ)^(2/3 : ℝ)) k, localMarkedExpectation M lambda n x0 y r Ψ) =
      ∫ G, markedCount x0 G k r Ψ ∂graphLaw M lambda n x0 := by
  calc
    _ = ∫ _y in cell ((n : ℝ)^(2/3 : ℝ)) k, (n : ℝ)^(2*(q : ℝ)/3) *
        ∫ G, markedCount x0 G k r Ψ ∂graphLaw M lambda n x0 :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun _ hy ↦ localMarkedExpectation_eq_on_cell M lambda hn x0 k r Ψ hy)
    _ = _ := by
      rw [setIntegral_const,smul_eq_mul,measureReal_def,critical_cell_volume_toReal hn]
      have hp := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (2*(q : ℝ)/3)).ne'
      field_simp

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem integral_localMarkedExpectation_grid (M : FiniteIrreducibleModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (x0 : Fin n → S)
    (A : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ y in ⋃ k ∈ A, cell ((n : ℝ)^(2/3 : ℝ)) k, localMarkedExpectation M lambda n x0 y r Ψ) =
      ∑ k ∈ A, ∫ G, markedCount x0 G k r Ψ ∂graphLaw M lambda n x0 := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_localMarkedExpectation_cell M lambda hn x0 k r Ψ)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_localMarkedExpectation_cell M lambda hn x0 k r Ψ)

end PerronWright.FiniteIrreducibleMarkedWindowGrid
