import PerronWright.Probability.CompactAnnealedMarkedFactorialUniform
import PerronWright.Probability.CriticalFloorCells
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounds, measurability and exact floor-cell integrals for actual marks -/

open MeasureTheory Filter Topology
open scoped BigOperators Real Topology Classical

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactAnnealedMarkedFactorialGrid

open CompactAnnealedMarkedFactorialLocal CompactAnnealedMarkedFactorialUniform
  AnnealedMarkedFactorialCounting AnnealedMarkedResidualConcentration FactorialDensity
  CriticalFloorCells

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem exists_uniform_scaled_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) {q : ℕ} (hq : 0 < q)
    (R : ℕ) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ r : Fin q → ℕ, (∀ i, r i ≤ R) →
      ∀ x ∈ sizeWindow q a b, |localMarkedExpectation M lambda n x r Ψ| ≤ B := by
  obtain ⟨C,hC,hbound⟩ := exists_density_window_bound (b := b) (M.beta_pos hM) ha R
  let B₀ := C^q * Real.exp (-M.beta hM*(a*q)^3/24)
  refine ⟨1+B₀*|Ψ (perronMarks M hM q)|,by dsimp only [B₀]; positivity,?_⟩
  filter_upwards [marked_factorial_uniform_bounded_surplus M hM hQP hq R lambda a b ha hab Ψ hΨ 1 zero_lt_one]
    with n hn r hr x hx
  have hxi := mem_sizeWindow.mp hx
  have hd := hbound q (M.alpha hM) lambda x r hxi hr
  have hp := density_pos (M.alpha hM) lambda (M.beta_pos hM) x r
    (fun i ↦ ha.trans_le (hxi i).1)
  calc
    |localMarkedExpectation M lambda n x r Ψ| =
        |(localMarkedExpectation M lambda n x r Ψ-
          density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)) +
          density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)| := by congr 1; ring
    _ ≤ |localMarkedExpectation M lambda n x r Ψ-
          density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)| +
        |density (M.alpha hM) (M.beta hM) lambda x r * Ψ (perronMarks M hM q)| := abs_add_le _ _
    _ ≤ 1+B₀*|Ψ (perronMarks M hM q)| := by
      rw [abs_mul,abs_of_pos hp]
      exact add_le_add (hn r hr x hx).le (mul_le_mul_of_nonneg_right hd (abs_nonneg _))

theorem measurable_localMarkedExpectation (M : CompactBJRModel S)
    (lambda : ℝ) (n : ℕ) {q : ℕ} (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    Measurable (fun x : Fin q → ℝ ↦ localMarkedExpectation M lambda n x r Ψ) := by
  let E : (Fin q → ℕ) → ℝ := fun k ↦
    (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n
  have hsize : Measurable (fun x : Fin q → ℝ ↦
      fun i ↦ CriticalScaling.size (x i) n) := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun x : Fin q → ℝ ↦ ⌊x i * (n : ℝ)^(2/3 : ℝ)⌋₊)
    have hc : Measurable (fun x : Fin q → ℝ ↦ x i) := measurable_pi_apply i
    exact (hc.mul_const ((n : ℝ)^(2/3 : ℝ))).nat_floor
  exact (measurable_of_countable E).comp hsize

theorem localMarkedExpectation_eq_on_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ)
    {x : Fin q → ℝ} (hx : x ∈ cell ((n : ℝ)^(2/3 : ℝ)) k) :
    localMarkedExpectation M lambda n x r Ψ = (n : ℝ)^(2*(q : ℝ)/3) *
      ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  have he := floor_eq_on_cell (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) k hx
  simp only [localMarkedExpectation,CriticalScaling.size,he]

theorem integrableOn_localMarkedExpectation_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    IntegrableOn (fun x ↦ localMarkedExpectation M lambda n x r Ψ)
      (cell ((n : ℝ)^(2/3 : ℝ)) k) volume := by
  let : IsFiniteMeasure (volume.restrict (cell ((n : ℝ)^(2/3 : ℝ)) k)) :=
    isFiniteMeasure_restrict_cell _ k
  apply (integrable_const ((n : ℝ)^(2*(q : ℝ)/3) *
      ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n)).congr
  filter_upwards [ae_restrict_mem (measurableSet_cell _ k)] with x hx
  exact (localMarkedExpectation_eq_on_cell M lambda hn k r Ψ hx).symm

/-- A full critical cell contributes exactly its actual typed-graph
continuous-mark tuple expectation, including at every finite graph size. -/
theorem integral_localMarkedExpectation_cell (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (k r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ x in cell ((n : ℝ)^(2/3 : ℝ)) k, localMarkedExpectation M lambda n x r Ψ) =
      ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  calc
    _ = ∫ _x in cell ((n : ℝ)^(2/3 : ℝ)) k,
        (n : ℝ)^(2*(q : ℝ)/3) *
          ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
            ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n :=
      setIntegral_congr_fun (measurableSet_cell _ k)
        (fun _ hx ↦ localMarkedExpectation_eq_on_cell M lambda hn k r Ψ hx)
    _ = _ := by
      rw [setIntegral_const,smul_eq_mul,measureReal_def,critical_cell_volume_toReal hn]
      have hp := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (2*(q : ℝ)/3)).ne'
      field_simp

theorem integral_localMarkedExpectation_grid (M : CompactBJRModel S)
    (lambda : ℝ) {n q : ℕ} (hn : 0 < n) (A : Finset (Fin q → ℕ)) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ x in ⋃ k ∈ A, cell ((n : ℝ)^(2/3 : ℝ)) k,
      localMarkedExpectation M lambda n x r Ψ) =
      ∑ k ∈ A, ∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ
        ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n := by
  rw [integral_biUnion_finset A (fun k _ ↦ measurableSet_cell _ k)
    (fun _ _ _ _ hkl ↦ disjoint_cells
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _) hkl)
    (fun k _ ↦ integrableOn_localMarkedExpectation_cell M lambda hn k r Ψ)]
  exact Finset.sum_congr rfl (fun k _ ↦ integral_localMarkedExpectation_cell M lambda hn k r Ψ)

end PerronWright.CompactAnnealedMarkedFactorialGrid
